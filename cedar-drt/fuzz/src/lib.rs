/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

pub use libfuzzer_sys::fuzz_target;

/// Guided-collection logging: capture EVERY valid input a cargo-fuzz run produces
/// (not libFuzzer's minimized ~1000-entry corpus) so the coverage experiment can
/// replay the full stream through the instrument-coverage binary.
///
/// When `CEDAR_FUZZ_LOG_DIR` is set, `log_input` writes each valid input's replayable
/// bytes (the same `[schema_len:u32-le ‖ schema-proto ‖ policies-proto]` framing the
/// collect corpus uses) to a uniquely-named file there; `run_guided_collection`'s drain
/// thread streams those to S3 and deletes them (bounded disk). `record` maintains the
/// valid/total counts + periodic snapshots and writes `CEDAR_FUZZ_STATS` (the JSON
/// `guided::run_guided_*` reads). No-ops entirely when the env vars are unset.
pub mod guided_log {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::{Mutex, OnceLock};
    use std::time::{Duration, Instant};

    static COUNTER: AtomicU64 = AtomicU64::new(0);
    static VALID: AtomicU64 = AtomicU64::new(0);
    static TOTAL: AtomicU64 = AtomicU64::new(0);
    static NEXT_SNAP_MS: AtomicU64 = AtomicU64::new(0);
    static START: OnceLock<Instant> = OnceLock::new();
    static SNAPS: Mutex<Vec<(u64, u64, u64)>> = Mutex::new(Vec::new());
    static SINCE_CHECK: AtomicU64 = AtomicU64::new(0);

    fn start() -> &'static Instant {
        START.get_or_init(Instant::now)
    }

    fn env_u64(key: &str, default: u64) -> u64 {
        std::env::var(key).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
    }

    /// Count pending (undrained) files in the log dir. Cheap enough to call periodically.
    fn pending_count(dir: &str) -> usize {
        std::fs::read_dir(dir).map(|rd| rd.count()).unwrap_or(0)
    }

    /// Record one valid input: bump the valid count and (if `CEDAR_FUZZ_LOG_DIR` is
    /// set) write its replayable bytes for the drain to stream to S3.
    ///
    /// LOSSLESS via BACKPRESSURE: previously the write was best-effort — when the fuzzer
    /// out-ran the S3 drain, `log_dir` (tmpfs) filled, `fs::write` failed, and the input was
    /// silently DROPPED, so the collected corpus came out far smaller than the valid count
    /// (per-rep 6–100%). Now, before writing, if the undrained backlog exceeds `HIGH`, we
    /// BLOCK until the drain brings it back under `LOW` — throttling generation to the drain
    /// rate so the backlog (and tmpfs use) stays bounded and no input is dropped. The write
    /// itself also RETRIES rather than dropping. Result: corpus size == valid count.
    /// Watermarks are env-tunable (`CEDAR_FUZZ_DRAIN_HIGH`/`_LOW`).
    pub fn log_input(bytes: &[u8]) {
        VALID.fetch_add(1, Ordering::Relaxed);
        if let Ok(dir) = std::env::var("CEDAR_FUZZ_LOG_DIR") {
            // Backpressure check every 256 inputs (bounds the read_dir cost; the backlog can
            // only grow by ~256 files between checks, negligible vs the watermarks).
            if SINCE_CHECK.fetch_add(1, Ordering::Relaxed) % 256 == 0 {
                let high = env_u64("CEDAR_FUZZ_DRAIN_HIGH", 8000) as usize;
                let low = env_u64("CEDAR_FUZZ_DRAIN_LOW", 2000) as usize;
                if pending_count(&dir) > high {
                    // Over high-water: block until the drain catches up to low-water (hysteresis).
                    while pending_count(&dir) > low {
                        std::thread::sleep(Duration::from_millis(5));
                    }
                }
            }
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            // temp name then rename, so the drain never reads a half-written file.
            let final_path = format!("{dir}/in_{n:012}.bin");
            let tmp_path = format!("{dir}/.wip_{n:012}.bin");
            // Retry on failure (e.g. a transient ENOSPC) instead of dropping. Backpressure keeps
            // tmpfs from filling, so this loop almost never spins; cap it so a dead drain can't hang.
            for _ in 0..2000 {
                if std::fs::write(&tmp_path, bytes).is_ok() {
                    let _ = std::fs::rename(&tmp_path, &final_path);
                    return;
                }
                std::thread::sleep(Duration::from_millis(5));
            }
        }
    }

    /// Record one execution attempt (call once per fuzz invocation, valid or not);
    /// emits periodic snapshots + stats. Valid count is bumped separately by `log_input`.
    pub fn note_attempt() {
        let _ = start();
        TOTAL.fetch_add(1, Ordering::Relaxed);
        let snap_ms: u64 = std::env::var("CEDAR_FUZZ_SNAPSHOT_MS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1000);
        if snap_ms == 0 {
            return;
        }
        let el = start().elapsed().as_millis() as u64;
        if el >= NEXT_SNAP_MS.load(Ordering::Relaxed) {
            NEXT_SNAP_MS.store(el + snap_ms, Ordering::Relaxed);
            let (v, t) = (VALID.load(Ordering::Relaxed), TOTAL.load(Ordering::Relaxed));
            if let Ok(mut s) = SNAPS.lock() {
                s.push((el, v, t));
            }
            write_stats();
        }
    }

    /// Write `CEDAR_FUZZ_STATS` (if set) — the FuzzStats JSON `guided.rs` reads.
    pub fn write_stats() {
        let Ok(path) = std::env::var("CEDAR_FUZZ_STATS") else {
            return;
        };
        let (v, t) = (VALID.load(Ordering::Relaxed), TOTAL.load(Ordering::Relaxed));
        let el = start().elapsed().as_millis() as u64;
        let snaps = SNAPS.lock().map(|s| s.clone()).unwrap_or_default();
        let stats = serde_json::json!({
            "valid_count": v, "total_count": t, "elapsed_ms": el, "snapshots": snaps,
        });
        let tmp = format!("{path}.tmp");
        if std::fs::write(&tmp, stats.to_string()).is_ok() {
            let _ = std::fs::rename(&tmp, &path);
        }
    }

    /// Register an atexit hook that flushes the final stats. Call once at startup.
    pub fn install_stats_at_exit() {
        extern "C" fn flush() {
            write_stats();
        }
        unsafe {
            libc::atexit(flush);
        }
    }
}

pub mod abac;
pub mod pst_equiv;
pub mod pst_gen;
pub mod roundtrip_entities;
pub mod schemas;
pub mod symcc;
pub mod tpe;
pub mod validation_drt;

/// Install a SIGURG handler that flushes LLVM coverage profile data.
/// Call once (via `Once`) at fuzz target startup. This allows external scripts
/// to poll coverage mid-run without restarting the process.
pub fn install_coverage_flush_handler() {
    unsafe extern "C" fn flush_coverage(_sig: libc::c_int) {
        unsafe extern "C" {
            fn __llvm_profile_write_file() -> i32;
        }
        unsafe { __llvm_profile_write_file() };
    }
    unsafe {
        libc::signal(libc::SIGURG, flush_coverage as libc::sighandler_t);
    }
}

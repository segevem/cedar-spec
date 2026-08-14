use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::experiment::config::{ThroughputResult, ThroughputSnapshot, GeneratorParams};

/// A filesystem-safe token identifying an approach, derived from its (approach-specific)
/// output directory's final component. Used to make per-rep scratch dirs (libFuzzer corpus,
/// the drain log dir) unique PER APPROACH, so approaches running the same rep in parallel
/// don't collide in `/dev/shm` (which would race-split their logged inputs into each other's
/// corpus). Falls back to a hash of the full path if the component isn't usable.
fn approach_tag(output_dir: &Path) -> String {
    let raw = output_dir
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("approach");
    let cleaned: String = raw
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '-' || c == '_' { c } else { '_' })
        .collect();
    if cleaned.is_empty() { "approach".to_string() } else { cleaned }
}

/// Stats JSON written by `logging_fuzz_target!` at exit.
#[derive(Debug, Serialize, Deserialize)]
pub struct FuzzStats {
    pub valid_count: u64,
    pub total_count: u64,
    pub elapsed_ms: u64,
    pub snapshots: Vec<(u64, u64, u64)>, // (elapsed_ms, valid, total)
}

/// Result of a guided fuzzing session.
#[derive(Debug, Serialize)]
pub struct GuidedResult {
    pub stats: FuzzStats,
    pub log_dir: PathBuf,
}

/// Run a single guided throughput repetition.
///
/// Uses `cargo fuzz run` — the canonical way a guided campaign runs — with a fresh empty
/// corpus, `-max_total_time`, and `-seed`. This is IDENTICAL to how
/// [`run_guided_collection_with_drain`] invokes the fuzzer; the only difference is that
/// throughput does NOT set `CEDAR_FUZZ_LOG_DIR`, so it measures the rate unburdened by
/// input logging/draining (via `CEDAR_FUZZ_STATS`).
pub fn run_guided_throughput(
    fuzz_target: &str,
    duration: Duration,
    rep_id: u32,
    seed: u64,
    output_dir: &Path,
    params: &GeneratorParams,
) -> ThroughputResult {
    let stats_path = output_dir.join(format!("throughput/_fuzz_stats_rep_{:02}.json", rep_id));
    std::fs::create_dir_all(stats_path.parent().unwrap()).ok();

    // Use a fresh empty corpus for cold-start measurement. Keyed by APPROACH (derived
    // from the approach-specific `output_dir`) as well as rep, so approaches running the
    // same rep in parallel don't share libFuzzer's working corpus.
    let tag = approach_tag(output_dir);
    let empty_corpus =
        std::env::temp_dir().join(format!("cedar-fuzz-empty-corpus-{}-{}", tag, rep_id));
    let _ = std::fs::remove_dir_all(&empty_corpus);
    std::fs::create_dir_all(&empty_corpus).ok();

    let status = Command::new("cargo")
        .args(["+nightly", "fuzz", "run", "-s", "none", fuzz_target])
        .arg(format!("{}", empty_corpus.display()))
        .arg("--")
        .arg(format!("-max_total_time={}", duration.as_secs()))
        .arg(format!("-seed={}", seed))
        // Disable libFuzzer's default 2GB RSS limit: a single memory-heavy generated input
        // must NOT abort the probe (which would undercount V_t, the collect target).
        .arg("-rss_limit_mb=0")
        .env("CEDAR_FUZZ_STATS", &stats_path)
        .env("CEDAR_FUZZ_SNAPSHOT_MS", "1000")
        .current_dir(fuzz_dir())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();
    let _ = status;

    let _ = std::fs::remove_dir_all(&empty_corpus);

    let stats = read_fuzz_stats(&stats_path).unwrap_or_else(|| FuzzStats {
        valid_count: 0,
        total_count: 0,
        elapsed_ms: duration.as_millis() as u64,
        snapshots: Vec::new(),
    });

    let elapsed_secs = stats.elapsed_ms as f64 / 1000.0;

    ThroughputResult {
        rep_id,
        generator: format!("guided:{}", fuzz_target),
        target: "validation-drt".to_string(),
        duration_secs: duration.as_secs_f64(),
        seed,
        valid_count: stats.valid_count,
        attempt_count: stats.total_count,
        throughput_valid_per_sec: stats.valid_count as f64 / elapsed_secs,
        throughput_attempts_per_sec: stats.total_count as f64 / elapsed_secs,
        elapsed_secs,
        params: params.clone(),
        snapshots: stats.snapshots.iter().map(|(ms, valid, total)| ThroughputSnapshot {
            elapsed_secs: *ms as f64 / 1000.0,
            valid_count: *valid,
            attempt_count: *total,
        }).collect(),
    }
}

/// Run a single guided collection repetition.
/// Spawns the fuzz binary with logging enabled for the given duration.
/// A background drain thread continuously moves files from the tmpfs log dir
/// to `on_file`, keeping disk usage bounded.
pub fn run_guided_collection(
    fuzz_target: &str,
    total_runs: u64,
    max_total_time_secs: Option<u64>,
    target_stats_path: Option<PathBuf>,
    rep_id: u32,
    seed: u64,
    corpus_dir: &Path,
    output_dir: &Path,
) -> u64 {
    run_guided_collection_with_drain(
        fuzz_target, total_runs, max_total_time_secs, target_stats_path, rep_id, seed,
        corpus_dir, output_dir,
        |_name, _bytes| {},
    )
}

/// Like `run_guided_collection` but calls `on_file(filename, bytes)` for each
/// corpus file as it's drained from tmpfs. Use this to stream to S3.
///
/// Stop bound (first hit wins):
///   * `target_stats_path = Some(p)` — COUNT-signal mode: run unbounded and stop once
///     the collected valid count reaches the throughput probe's `valid_count` (read from
///     `p`). Collect runs in TRUE PARALLEL with the throughput probe (a separate,
///     core-pinned process) and keeps going PAST throughput's wall-clock until it hits
///     the same N, so N is the fair pure-throughput term count. Used for guided runs.
///   * else `-runs=<total_runs>` (skipped when 0) and/or `-max_total_time=<secs>`.
pub fn run_guided_collection_with_drain(
    fuzz_target: &str,
    total_runs: u64,
    max_total_time_secs: Option<u64>,
    // When `Some(path)`, collect runs UNBOUNDED and stops once it has drained the
    // number of valid inputs the (concurrent) throughput probe produced — read from
    // that probe's FuzzStats file (`valid_count`) as soon as it finishes. This is the
    // "collect matches throughput's count" signal: collect keeps going PAST throughput's
    // wall-clock (it's slower due to logging/drain I/O) until it hits the same N, so N is
    // the fair pure-throughput term count, not an I/O-depressed cutoff.
    target_stats_path: Option<PathBuf>,
    rep_id: u32,
    seed: u64,
    corpus_dir: &Path,
    output_dir: &Path,
    mut on_file: impl FnMut(&str, &[u8]) + Send + 'static,
) -> u64 {
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    use std::sync::Arc;

    // Keyed by APPROACH (from the approach-specific `output_dir`) AND rep: approaches
    // running the same rep in parallel MUST NOT share this drain dir, or the drain would
    // interleave both targets' logged inputs into each other's corpus (a race-split mix).
    let tag = approach_tag(output_dir);
    let log_dir = PathBuf::from(format!("/dev/shm/cedar-fuzz-{}-rep-{:02}", tag, rep_id));
    std::fs::create_dir_all(&log_dir).ok();

    let stats_path = output_dir.join(format!("collect/_fuzz_stats_rep_{:02}.json", rep_id));
    std::fs::create_dir_all(stats_path.parent().unwrap()).ok();

    std::fs::create_dir_all(corpus_dir).ok();

    // Use a fresh empty dir for libfuzzer's working corpus (cold start), also approach-keyed.
    let fuzz_corpus_dir =
        log_dir.with_file_name(format!("cedar-fuzz-corpus-{}-{:02}", tag, rep_id));
    let _ = std::fs::remove_dir_all(&fuzz_corpus_dir);
    std::fs::create_dir_all(&fuzz_corpus_dir).ok();

    // Preserve crash evidence: libFuzzer writes `crash-*`/`oom-*`/`timeout-*` artifacts to
    // `-artifact_prefix`, and we capture the fuzzer's stderr (panic backtraces, libFuzzer
    // "ERROR: ... OOM/timeout" lines) to a file instead of /dev/null. Both live under the
    // approach's output dir so the results sync ships them to S3 for inspection. If collect
    // undershoots the count target, these tell us WHY (panic/mismatch vs OOM vs timeout).
    let artifact_dir = output_dir.join(format!("collect/rep_{:02}_artifacts", rep_id));
    let _ = std::fs::remove_dir_all(&artifact_dir);
    std::fs::create_dir_all(&artifact_dir).ok();
    let stderr_path = output_dir.join(format!("collect/rep_{:02}_stderr.log", rep_id));
    let stderr_file = std::fs::File::create(&stderr_path)
        .map(std::process::Stdio::from)
        .unwrap_or_else(|_| std::process::Stdio::null());

    // Run via `cargo fuzz run` — the canonical guided invocation, IDENTICAL to
    // run_guided_throughput — plus the collection env (CEDAR_FUZZ_LOG_DIR) so the target
    // logs every valid input for the drain. libFuzzer stop bounds: in count-signal mode
    // (`target_stats_path`) run UNBOUNDED and kill from the monitor once the target valid
    // count is drained; otherwise -runs and/or -max_total_time. Spawned in a NEW process
    // group so the count-match kill takes down cargo AND the fuzz binary it spawns.
    let mut cmd = Command::new("cargo");
    cmd.args(["+nightly", "fuzz", "run", "-s", "none", fuzz_target])
        .arg(fuzz_corpus_dir.to_str().unwrap())
        .arg("--")
        .arg(format!("-seed={}", seed))
        // Disable libFuzzer's default 2GB RSS limit so a single memory-heavy input can't
        // abort collect early (the cause of count-target undershoot on the fast generator).
        .arg("-rss_limit_mb=0")
        // Keep crash/oom/timeout artifacts (the reproducing input bytes) for inspection.
        .arg(format!("-artifact_prefix={}/", artifact_dir.display()));
    if target_stats_path.is_none() {
        if total_runs > 0 {
            cmd.arg(format!("-runs={}", total_runs));
        }
        if let Some(secs) = max_total_time_secs {
            cmd.arg(format!("-max_total_time={}", secs));
        }
    }
    cmd.env("CEDAR_FUZZ_LOG_DIR", &log_dir)
        .env("CEDAR_FUZZ_STATS", &stats_path)
        .env("CEDAR_FUZZ_SNAPSHOT_MS", "1000")
        .current_dir(fuzz_dir())
        .stdout(std::process::Stdio::null())
        .stderr(stderr_file);
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0); // child becomes group leader (pgid == child pid)
    }
    let mut child = cmd.spawn().expect("failed to spawn cargo fuzz run");

    // Drain thread: continuously move files from log_dir, call on_file, delete.
    // `drained` is shared so the monitor loop can see progress toward the target.
    let drain_dir = log_dir.clone();
    let done = Arc::new(AtomicBool::new(false));
    let done_clone = done.clone();
    let drained = Arc::new(AtomicU64::new(0));
    let drained_clone = drained.clone();

    let drain_handle = std::thread::spawn(move || {
        let mut count = 0u64;
        loop {
            let mut found_any = false;
            if let Ok(entries) = std::fs::read_dir(&drain_dir) {
                let mut files: Vec<_> = entries.filter_map(|e| e.ok()).collect();
                files.sort_by_key(|e| e.file_name());
                for entry in files {
                    if let Ok(bytes) = std::fs::read(entry.path()) {
                        let name = entry.file_name().to_string_lossy().to_string();
                        on_file(&name, &bytes);
                        count += 1;
                        drained_clone.store(count, Ordering::Relaxed);
                        found_any = true;
                    }
                    std::fs::remove_file(entry.path()).ok();
                }
            }
            if done_clone.load(Ordering::Relaxed) && !found_any {
                break;
            }
            if !found_any {
                std::thread::sleep(std::time::Duration::from_millis(500));
            }
        }
        count
    });

    let mut killed_by_us = false;
    let mut target_seen: Option<u64> = None;
    if let Some(ref tpath) = target_stats_path {
        // Count-signal mode: poll for (a) the fuzz child exiting on its own, and
        // (b) the throughput probe's target count. Once the target is known and we've
        // drained that many valids, stop the (otherwise unbounded) fuzz child.
        let mut target: Option<u64> = None;
        loop {
            if matches!(child.try_wait(), Ok(Some(_))) {
                break; // fuzzer exited on its own — a crash/OOM/timeout (diagnosed below)
            }
            if target.is_none() {
                target = read_valid_count(tpath);
                if let Some(t) = target {
                    target_seen = Some(t);
                    eprintln!("collect rep {rep_id}: throughput target = {t} valids");
                }
            }
            if let Some(t) = target {
                if drained.load(Ordering::Relaxed) >= t {
                    // Kill the whole process group so cargo AND its fuzz binary child stop.
                    #[cfg(unix)]
                    unsafe { libc::kill(-(child.id() as i32), libc::SIGKILL); }
                    child.kill().ok();
                    killed_by_us = true;
                    break;
                }
            }
            std::thread::sleep(std::time::Duration::from_millis(200));
        }
    }

    // Wait for fuzz process (returns immediately if already killed/exited above)
    let status = child.wait().ok();
    done.store(true, Ordering::Relaxed);

    let count = drain_handle.join().unwrap_or(0);

    // Diagnose an EARLY EXIT: in count-signal mode, if we did NOT kill it (drain never
    // reached the target) the fuzzer terminated on its own — a panic (incl. a DRT mismatch),
    // a libFuzzer OOM, or a timeout. Surface it loudly and preserve the artifacts + stderr so
    // the cause is inspectable (this is exactly the count-target undershoot we saw on the fast
    // generator). Otherwise (normal count-match kill) drop the empty artifact dir + stderr.
    if target_stats_path.is_some() && !killed_by_us {
        let artifacts: Vec<String> = std::fs::read_dir(&artifact_dir)
            .into_iter()
            .flatten()
            .filter_map(|e| e.ok())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| n.starts_with("crash-") || n.starts_with("oom-") || n.starts_with("timeout-"))
            .collect();
        eprintln!(
            "WARNING: collect rep {rep_id} fuzzer EXITED EARLY (status={:?}); drained {} of \
             target {:?} valids. Likely panic/mismatch, OOM, or timeout. artifacts={:?} \
             stderr={}",
            status, count, target_seen, artifacts, stderr_path.display()
        );
    } else {
        // Clean completion: no useful artifacts/stderr to keep.
        let _ = std::fs::remove_dir_all(&artifact_dir);
        let _ = std::fs::remove_file(&stderr_path);
    }

    // Clean up
    std::fs::remove_dir_all(&log_dir).ok();
    std::fs::remove_dir_all(&fuzz_corpus_dir).ok();

    count
}

/// Read the FINAL `valid_count` from the throughput probe's result JSON (a
/// `ThroughputResult` at throughput/rep_NN.json, written once when the probe completes).
/// Returns `None` until the file exists, parses, AND reports a NON-ZERO count — so the
/// count-match poller waits for the probe to finish rather than latching onto an absent
/// file or a transient zero. Parsed as generic JSON so any shape carrying `valid_count` works.
fn read_valid_count(path: &Path) -> Option<u64> {
    let data = std::fs::read_to_string(path).ok()?;
    let v: serde_json::Value = serde_json::from_str(&data).ok()?;
    v.get("valid_count").and_then(|x| x.as_u64()).filter(|&t| t > 0)
}

/// Read the stats JSON written by the fuzz target macro.
fn read_fuzz_stats(path: &Path) -> Option<FuzzStats> {
    let data = std::fs::read_to_string(path).ok()?;
    serde_json::from_str(&data).ok()
}

/// Get the fuzz directory path (relative to the worktree root).
fn fuzz_dir() -> PathBuf {
    let mut dir = std::env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    // Walk up from target/debug/ to find the fuzz dir
    for _ in 0..5 {
        let candidate = dir.join("cedar-drt/fuzz");
        if candidate.exists() {
            return candidate;
        }
        let candidate2 = dir.join("fuzz");
        if candidate2.exists() {
            return candidate2;
        }
        dir = dir.parent().unwrap_or(&dir).to_path_buf();
    }
    PathBuf::from("../fuzz")
}

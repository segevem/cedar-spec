//! In-process source coverage tracking using LLVM's profiling runtime counters.
//!
//! When built with `-C instrument-coverage`, the LLVM profiling runtime exposes:
//! - `__llvm_profile_reset_counters()` — zero all counters
//! - `__llvm_profile_begin_counters()` / `__llvm_profile_end_counters()` — counter array bounds
//!
//! These are the SAME counters that `llvm-cov` reads from profdata files.
//! By reading them in-process, we get per-input source coverage measurement
//! without any subprocess overhead.

use std::path::PathBuf;
use std::time::Instant;

extern "C" {
    fn __llvm_profile_reset_counters();
    fn __llvm_profile_begin_counters() -> *const u64;
    fn __llvm_profile_end_counters() -> *const u64;
}

/// Number of source coverage counters.
pub fn num_counters() -> usize {
    unsafe {
        let begin = __llvm_profile_begin_counters();
        let end = __llvm_profile_end_counters();
        end.offset_from(begin) as usize
    }
}

/// Reset all source coverage counters to zero.
pub fn reset_counters() {
    unsafe { __llvm_profile_reset_counters(); }
}

/// Count how many counters are non-zero (regions hit).
pub fn count_hit() -> usize {
    unsafe {
        let begin = __llvm_profile_begin_counters();
        let end = __llvm_profile_end_counters();
        let len = end.offset_from(begin) as usize;
        let counters = std::slice::from_raw_parts(begin, len);
        counters.iter().filter(|&&c| c > 0).count()
    }
}

/// Isolates the coverage produced by a *specific phase* (the validation target)
/// from everything else running in the same process (input generation, k-path
/// analysis, protobuf encode). LLVM counters are global and cumulative, so we
/// cannot attribute a line to a phase after the fact — instead we reset the
/// counters immediately before the target runs (`begin`) and fold only that
/// delta into a persistent union (`fold`). Generation / analysis coverage is
/// wiped by the next `begin`, so it never enters the union.
///
/// At the end `overwrite_live` writes the union back into the live counter array
/// so a normal profraw dump reflects ONLY validation-phase coverage — which
/// llvm-cov then maps to source lines with no harness/generator leakage and no
/// static call-graph approximation.
pub struct ValidationCov {
    union: Vec<u64>,
}

impl ValidationCov {
    pub fn new() -> Self {
        let n = num_counters();
        reset_counters();
        Self { union: vec![0; n] }
    }

    /// Call immediately BEFORE the validation target runs: clears generation /
    /// analysis coverage accumulated since the last fold.
    #[inline]
    pub fn begin(&self) {
        reset_counters();
    }

    /// Call immediately AFTER the validation target runs: fold this input's
    /// validation coverage into the union (max preserves "was this region hit").
    #[inline]
    pub fn fold(&mut self) {
        unsafe {
            let begin = __llvm_profile_begin_counters();
            let len = self.union.len();
            let live = std::slice::from_raw_parts(begin, len);
            for i in 0..len {
                let v = live[i];
                if v > self.union[i] {
                    self.union[i] = v;
                }
            }
        }
    }

    /// Regions hit across all validations so far (validation-scoped).
    pub fn hit(&self) -> usize {
        self.union.iter().filter(|&&c| c > 0).count()
    }

    /// Write the accumulated validation-only union back into the live counter
    /// array, so a following profraw dump captures ONLY validation coverage.
    /// After this the live counters are clobbered (only call at session end).
    pub fn overwrite_live(&self) {
        unsafe {
            let begin = __llvm_profile_begin_counters() as *mut u64;
            let len = self.union.len();
            debug_assert_eq!(len, num_counters());
            let live = std::slice::from_raw_parts_mut(begin, len);
            live.copy_from_slice(&self.union);
        }
    }
}

impl Default for ValidationCov {
    fn default() -> Self {
        Self::new()
    }
}

/// A point-in-time snapshot.
#[derive(Clone, serde::Serialize)]
pub struct CoverageSnapshot {
    pub elapsed_secs: f64,
    pub corpus_idx: usize,
    pub counters_hit: usize,
    pub counters_total: usize,
    pub coverage_pct: f64,
}

/// Tracks source coverage cumulatively across corpus entries.
/// Does NOT reset between entries — coverage accumulates, matching
/// what you'd get from replaying the whole corpus and measuring at the end.
pub struct SourceCovTracker {
    start_time: Instant,
    total: usize,
    corpus_idx: usize,
    corpus_dir: Option<PathBuf>,
    pub snapshots: Vec<CoverageSnapshot>,
}

impl SourceCovTracker {
    pub fn new(corpus_dir: Option<PathBuf>) -> Self {
        let total = num_counters();
        // Reset once at the start so we measure only what the corpus hits
        reset_counters();
        if let Some(ref dir) = corpus_dir {
            std::fs::create_dir_all(dir).ok();
        }
        Self {
            start_time: Instant::now(),
            total,
            corpus_idx: 0,
            corpus_dir,
            snapshots: Vec::new(),
        }
    }

    /// Execute a closure and record the cumulative coverage after it runs.
    /// Counters are NOT reset between calls — coverage accumulates.
    pub fn run_and_record<F: FnOnce()>(&mut self, f: F, input_bytes: Option<&[u8]>) {
        f();
        self.corpus_idx += 1;

        let hit = count_hit();
        let pct = if self.total > 0 { 100.0 * hit as f64 / self.total as f64 } else { 0.0 };

        self.snapshots.push(CoverageSnapshot {
            elapsed_secs: self.start_time.elapsed().as_secs_f64(),
            corpus_idx: self.corpus_idx,
            counters_hit: hit,
            counters_total: self.total,
            coverage_pct: pct,
        });

        // Save input to corpus if provided
        if let (Some(ref dir), Some(bytes)) = (&self.corpus_dir, input_bytes) {
            let path = dir.join(format!("id_{:06}", self.corpus_idx));
            std::fs::write(path, bytes).ok();
        }
    }

    pub fn elapsed_secs(&self) -> f64 {
        self.start_time.elapsed().as_secs_f64()
    }

    pub fn write_json(&self, path: &str) {
        let json = serde_json::to_string_pretty(&self.snapshots).unwrap();
        std::fs::write(path, json).unwrap();
    }
}

//! Coverage-guided corpus filtering using sancov 8-bit counters.
//!
//! Provides the same "is this input interesting?" logic as libfuzzer:
//! reset counters, execute, check if any new (edge, bucket) pair appeared.
//! Saves coverage-expanding inputs to a corpus directory.

use std::collections::HashSet;
use std::path::PathBuf;
use std::sync::Mutex;
use std::time::Instant;

struct CounterRegion {
    start: *mut u8,
    len: usize,
}

unsafe impl Send for CounterRegion {}

static COUNTER_REGIONS: Mutex<Vec<CounterRegion>> = Mutex::new(Vec::new());

#[no_mangle]
pub unsafe extern "C" fn __sanitizer_cov_8bit_counters_init(start: *mut u8, stop: *mut u8) {
    let len = stop as usize - start as usize;
    if len > 0 {
        COUNTER_REGIONS.lock().unwrap().push(CounterRegion { start, len });
    }
}

#[no_mangle]
pub unsafe extern "C" fn __sanitizer_cov_pcs_init(_pcs_beg: *const usize, _pcs_end: *const usize) {
}

#[no_mangle]
pub unsafe extern "C" fn __sanitizer_cov_trace_pc_indir(_callee: usize) {
}



/// Check if the sancov counters are active.
pub fn is_initialized() -> bool {
    !COUNTER_REGIONS.lock().unwrap().is_empty()
}

fn bucket_count(count: u8) -> u8 {
    match count {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4..=7 => 4,
        8..=15 => 5,
        16..=31 => 6,
        32..=127 => 7,
        128..=255 => 8,
    }
}

/// A point-in-time snapshot.
#[derive(Clone, serde::Serialize)]
pub struct TrackerSnapshot {
    pub elapsed_secs: f64,
    pub total_tested: u64,
    pub novel_count: u64,
    pub total_features: usize,
    pub throughput: f64,
    pub novel_throughput: f64,
}

/// Tracks coverage-expanding inputs. Saves novel inputs to a corpus directory.
pub struct EdgeTracker {
    seen_features: HashSet<u64>,
    pub novel_count: u64,
    pub total_tested: u64,
    corpus_dir: Option<PathBuf>,
    start_time: Instant,
    snapshots: Vec<TrackerSnapshot>,
    snapshot_interval_inputs: u64,
    next_snapshot_at: u64,
}

impl EdgeTracker {
    pub fn new(corpus_dir: Option<PathBuf>, snapshot_interval_inputs: u64) -> Self {
        if let Some(ref dir) = corpus_dir {
            std::fs::create_dir_all(dir).ok();
        }
        Self {
            seen_features: HashSet::new(),
            novel_count: 0,
            total_tested: 0,
            corpus_dir,
            start_time: Instant::now(),
            snapshots: Vec::new(),
            snapshot_interval_inputs,
            next_snapshot_at: snapshot_interval_inputs,
        }
    }

    /// Run a closure with edge tracking. Returns true if the input expanded coverage.
    pub fn run_tracked<F: FnOnce()>(&mut self, f: F, input_bytes: Option<&[u8]>) -> bool {
        // Reset
        let regions = COUNTER_REGIONS.lock().unwrap();
        for region in regions.iter() {
            unsafe { std::ptr::write_bytes(region.start, 0, region.len); }
        }
        drop(regions);

        // Execute
        f();
        self.total_tested += 1;

        // Check novelty
        let mut novel = false;
        let regions = COUNTER_REGIONS.lock().unwrap();
        let mut idx: u64 = 0;
        for region in regions.iter() {
            let counters = unsafe { std::slice::from_raw_parts(region.start, region.len) };
            for &count in counters {
                if count > 0 {
                    let feature = idx * 8 + bucket_count(count) as u64;
                    if self.seen_features.insert(feature) {
                        novel = true;
                    }
                }
                idx += 1;
            }
        }
        drop(regions);

        if novel {
            self.novel_count += 1;
            if let (Some(ref dir), Some(bytes)) = (&self.corpus_dir, input_bytes) {
                let path = dir.join(format!("id_{:06}", self.novel_count));
                std::fs::write(path, bytes).ok();
            }
        }

        if self.total_tested >= self.next_snapshot_at {
            self.take_snapshot();
            self.next_snapshot_at += self.snapshot_interval_inputs;
        }

        novel
    }

    fn take_snapshot(&mut self) {
        let elapsed = self.start_time.elapsed().as_secs_f64();
        self.snapshots.push(TrackerSnapshot {
            elapsed_secs: elapsed,
            total_tested: self.total_tested,
            novel_count: self.novel_count,
            total_features: self.seen_features.len(),
            throughput: self.total_tested as f64 / elapsed,
            novel_throughput: self.novel_count as f64 / elapsed,
        });
    }

    pub fn total_features(&self) -> usize { self.seen_features.len() }

    pub fn throughput(&self) -> f64 {
        let e = self.start_time.elapsed().as_secs_f64();
        if e > 0.0 { self.total_tested as f64 / e } else { 0.0 }
    }

    pub fn finalize(&mut self) { self.take_snapshot(); }
    pub fn snapshots(&self) -> &[TrackerSnapshot] { &self.snapshots }
}

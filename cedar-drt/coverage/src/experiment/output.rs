use std::fs;
use std::path::Path;

use crate::experiment::config::{ThroughputResult, ThroughputSnapshot, ThroughputSummary};
use crate::experiment::orchestrator::mean_stddev;

/// Write a single throughput result to disk.
pub fn write_throughput_result(output_dir: &Path, result: &ThroughputResult) {
    let dir = output_dir.join("throughput");
    fs::create_dir_all(&dir).expect("failed to create throughput output directory");
    let path = dir.join(format!("rep_{:02}.json", result.rep_id));
    let json = serde_json::to_string_pretty(result).unwrap();
    fs::write(path, json).unwrap();
}

/// Compute the median time series across all reps.
/// For each snapshot index i, takes the median valid_count across reps at that index.
/// If reps have different numbers of snapshots, uses the minimum length.
fn compute_median_time_series(results: &[ThroughputResult]) -> Vec<ThroughputSnapshot> {
    if results.is_empty() {
        return Vec::new();
    }

    let min_len = results.iter().map(|r| r.snapshots.len()).min().unwrap_or(0);
    let mut median_series = Vec::with_capacity(min_len);

    for i in 0..min_len {
        let mut valids: Vec<u64> = results.iter().map(|r| r.snapshots[i].valid_count).collect();
        let mut attempts: Vec<u64> = results.iter().map(|r| r.snapshots[i].attempt_count).collect();
        let mut elapsed: Vec<f64> = results.iter().map(|r| r.snapshots[i].elapsed_secs).collect();

        valids.sort();
        attempts.sort();
        elapsed.sort_by(|a, b| a.partial_cmp(b).unwrap());

        let mid = valids.len() / 2;
        median_series.push(ThroughputSnapshot {
            elapsed_secs: elapsed[mid],
            valid_count: valids[mid],
            attempt_count: attempts[mid],
        });
    }

    median_series
}

/// Compute and write the summary across all throughput reps.
pub fn write_throughput_summary(output_dir: &Path, results: &[ThroughputResult]) {
    if results.is_empty() {
        return;
    }

    let valid_counts: Vec<f64> = results.iter().map(|r| r.valid_count as f64).collect();
    let throughputs: Vec<f64> = results.iter().map(|r| r.throughput_valid_per_sec).collect();

    let (mean_valid, stddev_valid) = mean_stddev(&valid_counts);
    let (mean_tp, stddev_tp) = mean_stddev(&throughputs);

    let median_time_series = compute_median_time_series(results);

    let summary = ThroughputSummary {
        generator: results[0].generator.clone(),
        target: results[0].target.clone(),
        reps: results.len() as u32,
        duration_secs: results[0].duration_secs as u64,
        mean_valid_count: mean_valid,
        stddev_valid_count: stddev_valid,
        mean_throughput_valid_per_sec: mean_tp,
        stddev_throughput_valid_per_sec: stddev_tp,
        median_time_series,
        results: results.to_vec(),
    };

    let dir = output_dir.join("throughput");
    fs::create_dir_all(&dir).ok();
    let path = dir.join("summary.json");
    let json = serde_json::to_string_pretty(&summary).unwrap();
    fs::write(path, json).unwrap();
}

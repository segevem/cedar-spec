use std::path::Path;
use std::process::Command;

use crate::experiment::config::ThroughputResult;

/// Spawn a child process for a single repetition, optionally pinned to a CPU core.
pub fn spawn_rep(
    binary: &str,
    args: &[String],
    cpu_core: Option<usize>,
) -> std::io::Result<std::process::Child> {
    if let Some(core) = cpu_core {
        Command::new("taskset")
            .arg("-c")
            .arg(core.to_string())
            .arg(binary)
            .args(args)
            .spawn()
    } else {
        Command::new(binary)
            .args(args)
            .spawn()
    }
}

/// Determine which CPU core to pin a given rep to.
/// Distributes across available cores, skipping core 0.
pub fn core_for_rep(rep: u32, total_cores: usize) -> usize {
    let usable = total_cores.saturating_sub(1);
    if usable == 0 {
        return 0;
    }
    1 + (rep as usize % usable)
}

/// Get the number of available CPU cores.
pub fn num_cores() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
}

/// Collect throughput results from output directory.
pub fn collect_throughput_results(output_dir: &Path, reps: u32) -> Vec<ThroughputResult> {
    let mut results = Vec::new();
    for rep in 0..reps {
        let path = output_dir.join(format!("throughput/rep_{:02}.json", rep));
        if let Ok(data) = std::fs::read_to_string(&path) {
            if let Ok(result) = serde_json::from_str::<ThroughputResult>(&data) {
                results.push(result);
            }
        }
    }
    results
}

/// Compute mean and standard deviation from a slice of f64 values.
pub fn mean_stddev(values: &[f64]) -> (f64, f64) {
    if values.is_empty() {
        return (0.0, 0.0);
    }
    let n = values.len() as f64;
    let mean = values.iter().sum::<f64>() / n;
    let variance = values.iter().map(|v| (v - mean).powi(2)).sum::<f64>() / (n - 1.0).max(1.0);
    (mean, variance.sqrt())
}

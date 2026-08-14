use std::time::{Duration, Instant};

use crate::experiment::config::{GeneratorParams, ThroughputResult, ThroughputSnapshot};
use crate::target::Target;
use crate::{ValidationGenerator, run_coverage_session};

/// Run a single throughput repetition: generate for `duration` seconds, report stats.
/// Records a snapshot every `snapshot_interval` seconds for time-series plotting.
pub fn run_throughput_rep(
    generator: &dyn ValidationGenerator,
    target: &dyn Target,
    rep_id: u32,
    seed: u64,
    duration: Duration,
    snapshot_interval: Duration,
    params: &GeneratorParams,
) -> ThroughputResult {
    // Warm-up (untimed): pay the one-time cold cost — paging in the large derived
    // generator code + Lean runtime, the first batch refill, and the first DRT
    // call — BEFORE the measured window, so the reported rate is the warm
    // steady-state rate. Without this the throughput probe (always the first, cold
    // invocation) massively under-measures slow-cold configs and mis-sizes N.
    // THROUGHPUT_WARMUP inputs (default 1000 = one full generator batch, so the
    // first *measured* generate triggers an already-warm refill). Kept lightweight:
    // no k-path / analysis work here — just generate + target, matching the probe.
    // Time-boxed: stop at THROUGHPUT_WARMUP_SECS (default 20s) OR
    // THROUGHPUT_WARMUP inputs (default 2000), whichever comes first — so a
    // slow-cold config can't turn warm-up into a 1000×-DRT stall.
    let warmup: u64 = std::env::var("THROUGHPUT_WARMUP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(2000);
    let warmup_secs: f64 = std::env::var("THROUGHPUT_WARMUP_SECS")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(20.0);
    if warmup > 0 && warmup_secs > 0.0 {
        let w_start = Instant::now();
        let w_budget = Duration::from_secs_f64(warmup_secs);
        let mut warmed = 0u64;
        let mut attempts = 0u64;
        while warmed < warmup && w_start.elapsed() < w_budget {
            if let Some(input) = generator.generate(seed.wrapping_add(attempts)) {
                let _ = target.run(&input);
                warmed += 1;
            }
            attempts += 1;
        }
        eprintln!("Rep {}: warmed up {} inputs in {:.1}s before timing",
            rep_id, warmed, w_start.elapsed().as_secs_f64());
    }

    let start = Instant::now();
    let mut snapshots: Vec<ThroughputSnapshot> = Vec::new();
    let mut next_snapshot = snapshot_interval;

    let stats = run_coverage_session(
        generator,
        target,
        seed,
        u64::MAX,
        Some(duration),
        None,
        None,
        |_attempts, _valid| {
            if start.elapsed() >= next_snapshot {
                snapshots.push(ThroughputSnapshot {
                    elapsed_secs: start.elapsed().as_secs_f64(),
                    valid_count: _valid,
                    attempt_count: _attempts,
                });
                next_snapshot += snapshot_interval;
            }
        },
    );

    ThroughputResult {
        rep_id,
        generator: generator.name().to_string(),
        target: target.name().to_string(),
        duration_secs: duration.as_secs_f64(),
        seed,
        valid_count: stats.valid,
        attempt_count: stats.attempts,
        throughput_valid_per_sec: stats.valid as f64 / stats.elapsed_secs,
        throughput_attempts_per_sec: stats.attempts as f64 / stats.elapsed_secs,
        elapsed_secs: stats.elapsed_secs,
        params: params.clone(),
        snapshots,
    }
}

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::time::{Duration, Instant};

use crate::experiment::analyze::{AnalyzeResult, DiversitySnapshot};
use crate::kpath;
use crate::target::{Target, TargetResult};
use crate::{EdgeSnapshot, SessionStats, ValidationGenerator, ValidationInput, ViolationRecord};

/// Result of a collection session.
pub struct CollectResult {
    pub stats: SessionStats,
    pub inputs_saved: u64,
    /// Full per-rep metrics computed inline (no separate replay needed). The
    /// corpus is still saved so `analyze` can recompute other metrics later.
    pub analyze: AnalyzeResult,
    /// Number of DRT violations (Rust/Lean disagreements) seen this session.
    pub violation_count: u64,
}

/// Read `valid_count` from a throughput result JSON (ThroughputResult or FuzzStats — both
/// carry the field). Returns `None` if the file is absent or mid-write (parse fails), so
/// the count-match poller simply retries on the next check.
fn read_valid_count_json(path: &std::path::Path) -> Option<u64> {
    let data = std::fs::read_to_string(path).ok()?;
    let v: serde_json::Value = serde_json::from_str(&data).ok()?;
    v.get("valid_count").and_then(|x| x.as_u64())
}

/// Run a collection session: generate until `target_valid_count` valid inputs are produced.
///
/// This computes the FULL `AnalyzeResult` inline (unique inputs, skeletons, k-path
/// frequencies, diversity-over-time) as it generates — so the corpus need not be
/// replayed afterward. The corpus is still saved (via `on_save` / local files) for
/// ad-hoc later re-analysis with the `analyze` command.
///
/// On a DRT violation the target returns `TargetResult::Violation` (it never
/// crashes the process); `on_violation(index, message, input)` is invoked so the
/// caller can persist a reproducible repro (schema + policy + provenance). If
/// `stop_on_violation` is set, collection stops at the first violation.
#[allow(clippy::too_many_arguments)]
pub fn run_collection_session(
    generator: &dyn ValidationGenerator,
    target: &dyn Target,
    start_seed: u64,
    target_valid_count: u64,
    snapshot_interval: Option<Duration>,
    corpus_dir: &Path,
    // When false, per-input `.bin` files are NOT written to `corpus_dir` — only
    // `on_save` runs (e.g. S3 upload). Writing one tiny file per input is a major
    // bottleneck for large N, so callers that stream to S3 should pass `false`.
    write_local: bool,
    stop_on_violation: bool,
    mut on_progress: impl FnMut(u64, u64),
    mut on_save: impl FnMut(&str, &[u8]),
    mut on_violation: impl FnMut(u64, &str, &ValidationInput),
) -> CollectResult {
    fs::create_dir_all(corpus_dir).expect("failed to create corpus directory");

    // Optional wall-clock bound: stop the collect after this many seconds regardless
    // of `target_valid_count` (set `target_valid_count` huge to make time the bound).
    // This is the honest "N-minute run" primitive — each approach validates for the
    // same wall-clock window, so a faster generator simply produces more inputs.
    let max_secs = std::env::var("COLLECT_MAX_SECS").ok().and_then(|s| s.parse::<f64>().ok());
    // COUNT-MATCH mode: when `COLLECT_MATCH_STATS=<path>` points at the throughput probe's
    // result JSON, collect ignores `target_valid_count` and instead runs until it has
    // collected the number of valid inputs the (true-parallel, separate-core) throughput
    // probe produced (`valid_count` in that JSON, appearing when the probe finishes). This
    // makes N the fair full-speed term count: collect carries validation/coverage I/O so
    // it's slower and runs PAST the probe's wall-clock until it matches — it does NOT cut
    // off when the probe ends. The file is polled every 4096 attempts (cheap).
    let match_stats = std::env::var("COLLECT_MATCH_STATS").ok().map(std::path::PathBuf::from);
    let mut match_target: Option<u64> = None;
    // STREAM-ONLY: skip the per-input k-path/HLL/node-histogram analysis (the ~10x cost
    // that makes collect far slower than the throughput probe and stalls count-match).
    // Collect still generates, runs the DRT target (mismatch detection + probe-speed
    // parity), and streams the corpus. All diversity metrics are recomputed off the
    // critical path by the parallel replay-analyze pass (`analyze --format proto`), which
    // reads this same corpus. Coverage likewise comes from the replay. Used for all
    // approaches so collect ≈ probe speed and count-match completes quickly.
    let stream_only = std::env::var("COLLECT_STREAM_ONLY").is_ok();
    // Optional: reject ill-typed generations so coverage / corpus / analysis reflect
    // ONLY well-typed inputs — using the SAME predicate as the `validation-welltyped-drt`
    // fuzz target's `Corpus::Reject` (`crate::target::is_well_typed`). "If the corpus
    // would reject it, we reject it too": a rejected input counts as an attempt but is
    // not validated by the target, folded into coverage, saved to the corpus, or analyzed.
    let welltyped_only = std::env::var("COLLECT_WELLTYPED_ONLY").is_ok();
    let mut rejected = 0u64;
    // For coverage-only runs the saved corpus is not needed (coverage comes from the
    // fused profraw, not a replay); COLLECT_SKIP_CORPUS avoids spraying one tiny file
    // per input (which at high throughput is both a bottleneck and an inode flood).
    let write_local = write_local && std::env::var("COLLECT_SKIP_CORPUS").is_err();

    let metadata_path = corpus_dir.parent().unwrap_or(corpus_dir).join("per_input.jsonl");
    let metadata_file = fs::File::create(&metadata_path).expect("failed to create metadata file");
    let mut metadata_writer = BufWriter::new(metadata_file);

    let start = Instant::now();
    let mut valid = 0u64;
    let mut attempts = 0u64;
    let mut violation_count = 0u64;

    // --- inline analysis accumulators (mirror analyze::replay_and_analyze) ---
    let mut total_nodes = 0u64;
    let mut node_hist = crate::hll::NodeHistogram::default();
    let mut unique_hashes = crate::hll::Hll::new(21);
    let mut unique_skeletons = crate::hll::Hll::new(21);
    let mut all_2paths: HashSet<kpath::KPath> = HashSet::new();
    let mut all_3paths: HashSet<kpath::KPath> = HashSet::new();
    let mut kpath2_freq: HashMap<kpath::KPath, u64> = HashMap::new();
    let mut kpath3_freq: HashMap<kpath::KPath, u64> = HashMap::new();
    let mut top_constructors: HashMap<&'static str, u64> = HashMap::new();
    let mut diversity: Vec<DiversitySnapshot> = Vec::new();
    // snapshot roughly every 1% of the target (bounded to a sane range)
    let div_interval = target_valid_count.max(1) / 100;
    let div_interval = div_interval.clamp(1, 5000);

    let mut violations: Vec<ViolationRecord> = Vec::new();
    let mut edge_snapshots: Vec<EdgeSnapshot> = Vec::new();
    let mut next_snapshot = snapshot_interval.unwrap_or(Duration::from_secs(u64::MAX));

    // FUSED coverage: when built with `-C instrument-coverage` (+ `profraw`) and
    // `COLLECT_PROFRAW_DIR` is set, capture validator line coverage from the
    // validation this collect ALREADY runs (`target.run`), so no separate replay
    // pass is needed. `ValidationCov` resets the LLVM counters right before each
    // `target.run` and folds only that delta into a union — so generation, k-path
    // analysis, and protobuf encode running in the same process are EXCLUDED at the
    // source (no harness/generator leakage, no static call-graph approximation).
    #[cfg(feature = "profraw")]
    let cov_dir = std::env::var("COLLECT_PROFRAW_DIR").ok();
    #[cfg(feature = "profraw")]
    let mut vcov = cov_dir
        .as_ref()
        .map(|d| {
            fs::create_dir_all(d).ok();
            crate::source_cov_tracker::ValidationCov::new()
        });
    // Snapshot cadence: env override, else ~20 points over the run. 0/invalid ⇒ default
    // (never 0 — that would be a mod-by-zero below).
    #[cfg(feature = "profraw")]
    let cov_every: u64 = {
        let e = std::env::var("COLLECT_SNAP_EVERY").ok().and_then(|s| s.parse::<u64>().ok()).unwrap_or(0);
        if e == 0 { (target_valid_count.max(20) / 20).max(1) } else { e }
    };
    #[cfg(feature = "profraw")]
    let mut cov_manifest: Vec<serde_json::Value> = Vec::new();

    loop {
        if let Some(ref p) = match_stats {
            // Count-match mode: stop only once we've collected the throughput probe's
            // valid count. Poll the probe's result JSON until it appears (it's written
            // when the parallel probe finishes), then match that count.
            if match_target.is_none() && attempts % 4096 == 0 {
                match_target = read_valid_count_json(p);
                if let Some(t) = match_target {
                    eprintln!("collect: throughput target = {t} valids; collecting to match");
                }
            }
            if let Some(t) = match_target {
                if valid >= t {
                    break;
                }
            }
        } else {
            if valid >= target_valid_count {
                break;
            }
            if let Some(m) = max_secs {
                if start.elapsed().as_secs_f64() >= m {
                    break;
                }
            }
        }
        if snapshot_interval.is_some() && start.elapsed() >= next_snapshot {
            edge_snapshots.push(EdgeSnapshot {
                elapsed_secs: start.elapsed().as_secs_f64(),
                attempts,
                valid,
                novel_inputs: 0,
                total_features: 0,
            });
            next_snapshot += snapshot_interval.unwrap();
        }

        let seed = start_seed.wrapping_add(attempts);
        if let Some(input) = generator.generate(seed) {
            // Reject ill-typed inputs BEFORE any measurement, mirroring the guided
            // target's `Corpus::Reject`. Skips coverage fold, corpus save, analysis,
            // and the valid count — it only ticks `attempts` (like a rejected mutation).
            if welltyped_only && !crate::target::is_well_typed(&input.schema, &input.policies) {
                rejected += 1;
                attempts += 1;
                on_progress(attempts, valid);
                continue;
            }
            // Per-input k-path/HLL/node analysis — SKIPPED in stream_only (recomputed by
            // the parallel replay-analyze). `node_stats` carries just the small counts the
            // local per-input metadata needs, so nothing heavy leaks past this block.
            let node_stats: Option<(usize, usize, usize)> = if stream_only {
                None
            } else {
                let stats3 = kpath::analyze_policy_set(&input.policies, 3);
                let stats2 = kpath::analyze_policy_set(&input.policies, 2);
                let nc = stats3.node_count;
                total_nodes += nc as u64;
                node_hist.add(nc);
                unique_hashes.add(kpath::hash_policy_set(&input.policies));
                unique_skeletons.add(kpath::hash_policy_set_skeleton(&input.policies));
                for p in &stats2.kpaths {
                    *kpath2_freq.entry(p.clone()).or_insert(0) += 1;
                }
                for p in &stats3.kpaths {
                    *kpath3_freq.entry(p.clone()).or_insert(0) += 1;
                }
                all_2paths.extend(stats2.kpaths.iter().cloned());
                all_3paths.extend(stats3.kpaths.iter().cloned());
                for ctor in &stats3.top_constructors {
                    *top_constructors.entry(*ctor).or_insert(0) += 1;
                }
                Some((nc, stats2.kpaths.len(), stats3.kpaths.len()))
            };

            // DRT: run the target; a mismatch comes back as Violation (no crash).
            // Reset counters right before validation and fold only this run's delta
            // into the union, so the coverage we record is validation-ONLY (the
            // generation + k-path analysis above is wiped by `begin`).
            #[cfg(feature = "profraw")]
            if let Some(v) = vcov.as_ref() { v.begin(); }
            let result = target.run(&input);
            #[cfg(feature = "profraw")]
            if let Some(v) = vcov.as_mut() { v.fold(); }
            if let TargetResult::Violation(ref msg) = result {
                violation_count += 1;
                on_violation(valid, msg, &input);
                // Each violation is already persisted durably via `on_violation`;
                // keep only a bounded sample in memory (messages embed the full
                // schema Debug, so an unbounded Vec balloons on mismatch-heavy reps).
                if violations.len() < 100 {
                    violations.push(ViolationRecord {
                        seed,
                        message: msg.clone(),
                        raw_bytes: input.raw_bytes.clone(),
                    });
                }
            }

            // Save input to corpus as [schema_len:u32-le ‖ schema-proto ‖ policies-proto]
            // so the recorded corpus is self-contained (schema + policies). This lets
            // analyses be *revisited* over the saved data — in particular instrumented
            // line-coverage replay through the validator, which needs the schema (the
            // old policies-only corpus couldn't be validated).
            {
                use cedar_policy::proto::traits::Protobuf;
                let schema_bytes = input.schema.encode();
                let policy_bytes = input.policies.encode();
                let mut proto_bytes = Vec::with_capacity(4 + schema_bytes.len() + policy_bytes.len());
                proto_bytes.extend_from_slice(&(schema_bytes.len() as u32).to_le_bytes());
                proto_bytes.extend_from_slice(&schema_bytes);
                proto_bytes.extend_from_slice(&policy_bytes);
                let filename = format!("id_{:06}.bin", valid);
                if write_local {
                    fs::write(corpus_dir.join(&filename), &proto_bytes).ok();
                }
                on_save(&filename, &proto_bytes);
            }

            // Per-input metadata (local only; skipped in stream_only, which has no
            // node_stats). References the real generation seed/index via provenance.
            if let (Some((nc, k2, k3)), true) = (node_stats, write_local) {
                let (prov_seed, prov_idx) = input
                    .provenance
                    .as_ref()
                    .map(|p| (p.base_seed, p.index as i64))
                    .unwrap_or((seed, -1));
                let meta_line = serde_json::json!({
                    "idx": valid,
                    "seed": prov_seed,
                    "prov_index": prov_idx,
                    "node_count": nc,
                    "kpath2_count": k2,
                    "kpath3_count": k3,
                });
                writeln!(metadata_writer, "{}", meta_line).ok();
            }

            valid += 1;
            if !stream_only && valid % div_interval == 0 {
                diversity.push(DiversitySnapshot {
                    input_idx: valid as usize,
                    unique_inputs: unique_hashes.estimate() as usize,
                    unique_skeletons: unique_skeletons.estimate() as usize,
                    cumulative_2paths: all_2paths.len(),
                    cumulative_3paths: all_3paths.len(),
                });
            }

            #[cfg(feature = "profraw")]
            if cov_dir.is_some() {
                if valid % cov_every == 0 {
                    // Over-time point = in-process region-hit COUNT (a number), NOT a
                    // profraw dump. Cumulative full dumps (~MB each) would pile up
                    // locally; we keep only ONE final profraw per rep (below), which the
                    // caller uploads to S3 and deletes. The count gives the over-time
                    // shape; the harness-excluded final line count comes from that profraw.
                    cov_manifest.push(serde_json::json!({
                        "snapshot": cov_manifest.len(), "corpus_idx": valid, "validated": valid,
                        "elapsed_secs": start.elapsed().as_secs_f64(),
                        "counters_hit": vcov.as_ref().map(|v| v.hit()).unwrap_or(0),
                    }));
                }
            }

            if stop_on_violation && violation_count > 0 {
                break;
            }
        }
        attempts += 1;
        on_progress(attempts, valid);
    }

    if welltyped_only {
        eprintln!(
            "welltyped-only: kept {valid} well-typed, rejected {rejected} ill-typed ({attempts} attempts)"
        );
    }

    #[cfg(feature = "profraw")]
    if let (Some(ref d), Some(v)) = (&cov_dir, vcov.as_ref()) {
        // ONE final profraw per rep (the only one written). Write the validation-only
        // union back into the live counters first, so the dumped profraw contains
        // ONLY validation coverage (generation/analysis/encode excluded at the source).
        // The caller uploads it to S3 and deletes it locally so profraw never accumulates.
        v.overwrite_live();
        crate::profraw::dump_profraw_to(&format!("{d}/final.profraw"));
        cov_manifest.push(serde_json::json!({
            "snapshot": cov_manifest.len(), "corpus_idx": valid, "validated": valid,
            "elapsed_secs": start.elapsed().as_secs_f64(), "file": "final.profraw",
            "counters_hit": v.hit(),
        }));
        fs::write(format!("{d}/snapshots.json"), serde_json::to_string_pretty(&cov_manifest).unwrap()).ok();
    }

    if snapshot_interval.is_some() {
        edge_snapshots.push(EdgeSnapshot {
            elapsed_secs: start.elapsed().as_secs_f64(),
            attempts,
            valid,
            novel_inputs: 0,
            total_features: 0,
        });
    }

    // Final diversity snapshot if the last one didn't land on the boundary (none in
    // stream_only — diversity is recomputed by the replay-analyze).
    if !stream_only && valid > 0 && (diversity.is_empty() || diversity.last().unwrap().input_idx as u64 != valid) {
        diversity.push(DiversitySnapshot {
            input_idx: valid as usize,
            unique_inputs: unique_hashes.estimate() as usize,
            unique_skeletons: unique_skeletons.estimate() as usize,
            cumulative_2paths: all_2paths.len(),
            cumulative_3paths: all_3paths.len(),
        });
    }

    let mean_node_count = node_hist.mean();
    let median_node_count = node_hist.median();

    let mut kpath2_frequency: Vec<(String, u64)> =
        kpath2_freq.into_iter().map(|(k, v)| (k.0.join("\u{2192}"), v)).collect();
    kpath2_frequency.sort_by(|a, b| b.1.cmp(&a.1));
    let mut kpath3_frequency: Vec<(String, u64)> =
        kpath3_freq.into_iter().map(|(k, v)| (k.0.join("\u{2192}"), v)).collect();
    kpath3_frequency.sort_by(|a, b| b.1.cmp(&a.1));

    let analyze = AnalyzeResult {
        corpus_size: valid as usize,
        unique_inputs: unique_hashes.estimate() as usize,
        unique_skeletons: unique_skeletons.estimate() as usize,
        total_nodes,
        mean_node_count,
        median_node_count,
        cumulative_2paths: all_2paths.len(),
        cumulative_3paths: all_3paths.len(),
        kpath2_frequency,
        kpath3_frequency,
        diversity_over_time: diversity,
        source_coverage_pct: None,
        coverage_snapshots: Vec::new(),
    };

    let stats = SessionStats {
        valid,
        attempts,
        elapsed_secs: start.elapsed().as_secs_f64(),
        total_nodes,
        kpath2_count: all_2paths.len(),
        kpath3_count: all_3paths.len(),
        top_constructor_counts: top_constructors,
        novel_inputs: 0,
        total_features: 0,
        snapshots: edge_snapshots,
        violations,
    };

    CollectResult { stats, inputs_saved: valid, analyze, violation_count }
}

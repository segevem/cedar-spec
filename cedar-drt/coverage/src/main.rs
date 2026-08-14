use std::time::Duration;

use cedar_drt_coverage::generators::{
    ABACGenerator, AdaptiveGenerator, CorpusReplayGenerator, LateRampGenerator,
    MetaGenerator, MutatingGenerator, RetryABACGenerator, ScalingGenerator,
};
use cedar_drt_coverage::target::{self, Target};
use cedar_drt_coverage::{ValidationGenerator, run_adaptive_session, run_coverage_session};
use cedar_policy_generators::settings::ABACSettings;
use clap::{Parser, ValueEnum};

#[derive(Clone, ValueEnum)]
enum GeneratorKind {
    TypeDirected,
    Undirected,
    RetryTypeDirected,
    RetryUndirected,
    ScalingSlow,
    ScalingFast,
    MetaSmall,
    MutatingUndirected,
    LateRamp,
    CorpusReplay,
    Adaptive,
    #[cfg(feature = "lean-gen")]
    LeanTypeof,
    #[cfg(feature = "lean-gen")]
    LeanSchemaTypeof,
}

#[derive(Clone, ValueEnum)]
enum TargetKind {
    RustOnly,
    #[cfg(feature = "lean-gen")]
    ValidationDrt,
    #[cfg(feature = "lean-gen")]
    LevelValidationDrt,
    #[cfg(feature = "symcc")]
    SymccTermAlwaysAllows,
    #[cfg(feature = "symcc")]
    SymccTermAlwaysDenies,
    #[cfg(feature = "symcc")]
    SymccTermNeverErrors,
    #[cfg(feature = "symcc")]
    SymccCheckAlwaysAllowsOk,
    #[cfg(feature = "symcc")]
    SymccCheckAlwaysDeniesOk,
    #[cfg(feature = "symcc")]
    SymccCheckNeverErrorsOk,
}

#[derive(Parser)]
#[command(about = "Run a validation generator against a target and track coverage")]
struct Args {
    /// Which generator to use
    #[arg(long, value_enum, default_value = "type-directed")]
    generator: GeneratorKind,

    /// Which target (test oracle) to run inputs against
    #[arg(long, value_enum, default_value = "rust-only")]
    target: TargetKind,

    /// Maximum number of attempts (default: unlimited if --duration is set)
    #[arg(long, short = 'n')]
    iterations: Option<u64>,

    /// Run for this many seconds (takes priority over --iterations)
    #[arg(long)]
    duration: Option<u64>,

    /// Starting seed
    #[arg(long, default_value = "0")]
    seed: u64,

    /// PRNG buffer size (bytes of randomness per generation attempt)
    #[arg(long, default_value = "65536")]
    buffer_size: usize,

    /// Print progress every N attempts
    #[arg(long, default_value = "1000")]
    report_interval: u64,

    /// Path to corpus directory (required for corpus-replay generator)
    #[arg(long)]
    corpus: Option<String>,

    /// Edge snapshot interval in seconds (enables JSON time-series output)
    #[arg(long)]
    snapshot_interval: Option<u64>,

    /// Output file for edge tracking snapshots (JSON)
    #[arg(long)]
    snapshot_output: Option<String>,

    /// Specimen structure size budget for Lean generators (default 20)
    #[arg(long, default_value = "20")]
    lean_size: u32,

    /// Directory to save coverage-expanding inputs (corpus)
    #[arg(long)]
    corpus_dir: Option<String>,

    /// Directory to save violation-triggering inputs
    #[arg(long)]
    violations_dir: Option<String>,

    /// Replay a protobuf corpus directory (schema+policy pairs) through the validator
    #[arg(long)]
    replay_proto: Option<String>,

    /// Replay a fuzzer corpus directory (raw Unstructured bytes) through the validator
    #[arg(long)]
    replay_fuzz: Option<String>,

    /// Stream a corpus from S3 and replay it through the validator WITHOUT storing
    /// the corpus locally. `--replay-s3-bucket` + `--replay-s3-prefix <…/rep_NN>`
    /// (the `/corpus` suffix is added). Use with `REPLAY_PROFRAW_DIR` to emit
    /// `.profraw` coverage snapshots (transient — caller uploads to S3 + deletes).
    #[arg(long)]
    replay_s3_bucket: Option<String>,
    #[arg(long)]
    replay_s3_prefix: Option<String>,

    /// Only replay the first N entries (sorted by modification time)
    #[arg(long)]
    replay_limit: Option<usize>,

    /// Output JSON file for per-entry coverage data during replay
    #[arg(long)]
    replay_output: Option<String>,

    /// Replay only shard `--replay-shard` of `--replay-shards` (S3 replay only): a
    /// contiguous slice of the corpus's sorted batches, so N workers each cover ~1/N of
    /// a rep in parallel. Each shard dumps its own `final.profraw` (via
    /// `REPLAY_PROFRAW_DIR`); the caller merges the shards (union = rep coverage;
    /// cumulative-merge in shard order = the over-time curve).
    #[arg(long, default_value = "0")]
    replay_shard: usize,
    #[arg(long, default_value = "1")]
    replay_shards: usize,
}

fn make_generator(args: &Args) -> Box<dyn ValidationGenerator> {
    match args.generator {
        GeneratorKind::TypeDirected => {
            let mut gen = ABACGenerator::type_directed();
            gen.buffer_size = args.buffer_size;
            Box::new(gen)
        }
        GeneratorKind::Undirected => {
            let mut gen = ABACGenerator::undirected();
            gen.buffer_size = args.buffer_size;
            Box::new(gen)
        }
        GeneratorKind::RetryTypeDirected => {
            let mut gen = RetryABACGenerator::type_directed();
            gen.inner.buffer_size = args.buffer_size;
            Box::new(gen)
        }
        GeneratorKind::RetryUndirected => {
            let mut gen = RetryABACGenerator::undirected();
            gen.inner.buffer_size = args.buffer_size;
            Box::new(gen)
        }
        GeneratorKind::ScalingSlow => Box::new(ScalingGenerator::slow()),
        GeneratorKind::ScalingFast => Box::new(ScalingGenerator::fast()),
        GeneratorKind::MetaSmall => Box::new(MetaGenerator::small()),
        GeneratorKind::MutatingUndirected => Box::new(MutatingGenerator::new()),
        GeneratorKind::LateRamp => {
            let total_hint = args.duration.unwrap_or(600) * 260;
            Box::new(LateRampGenerator::new(total_hint))
        }
        GeneratorKind::CorpusReplay => {
            let corpus_dir = args.corpus.as_deref().unwrap_or_else(|| {
                eprintln!("--corpus is required for corpus-replay generator");
                std::process::exit(1);
            });
            let settings = ABACSettings {
                enable_additional_attributes: true,
                ..ABACSettings::type_directed()
            };
            Box::new(CorpusReplayGenerator::new(corpus_dir, settings))
        }
        GeneratorKind::Adaptive => unreachable!("handled separately"),
        #[cfg(feature = "lean-gen")]
        GeneratorKind::LeanTypeof => {
            Box::new(cedar_drt_coverage::lean_gen::LeanTypeOfGenerator::new(args.lean_size))
        }
        #[cfg(feature = "lean-gen")]
        GeneratorKind::LeanSchemaTypeof => {
            Box::new(cedar_drt_coverage::lean_gen::LeanSchemaTypeOfGenerator::with_range(10, args.lean_size))
        }
    }
}

fn make_target(args: &Args) -> Box<dyn Target> {
    match args.target {
        TargetKind::RustOnly => Box::new(target::RustValidation),
        #[cfg(feature = "lean-gen")]
        TargetKind::ValidationDrt => Box::new(target::ValidationDrt::new()),
        #[cfg(feature = "lean-gen")]
        TargetKind::LevelValidationDrt => Box::new(target::LevelValidationDrt::new(3)),
        #[cfg(feature = "symcc")]
        TargetKind::SymccTermAlwaysAllows => {
            Box::new(target::SymccTermDrt::new(target::SymccCheck::AlwaysAllows))
        }
        #[cfg(feature = "symcc")]
        TargetKind::SymccTermAlwaysDenies => {
            Box::new(target::SymccTermDrt::new(target::SymccCheck::AlwaysDenies))
        }
        #[cfg(feature = "symcc")]
        TargetKind::SymccTermNeverErrors => {
            Box::new(target::SymccTermDrt::new(target::SymccCheck::NeverErrors))
        }
        #[cfg(feature = "symcc")]
        TargetKind::SymccCheckAlwaysAllowsOk => {
            Box::new(target::SymccCheckOk::new(target::SymccCheck::AlwaysAllows))
        }
        #[cfg(feature = "symcc")]
        TargetKind::SymccCheckAlwaysDeniesOk => {
            Box::new(target::SymccCheckOk::new(target::SymccCheck::AlwaysDenies))
        }
        #[cfg(feature = "symcc")]
        TargetKind::SymccCheckNeverErrorsOk => {
            Box::new(target::SymccCheckOk::new(target::SymccCheck::NeverErrors))
        }
    }
}

fn save_violations(stats: &cedar_drt_coverage::SessionStats, dir: &str) {
    std::fs::create_dir_all(dir).expect("failed to create violations directory");
    for (i, v) in stats.violations.iter().enumerate() {
        let base = format!("{}/violation_{:04}_seed_{}", dir, i, v.seed);
        if let Some(ref bytes) = v.raw_bytes {
            std::fs::write(format!("{base}.bin"), bytes).ok();
        }
        std::fs::write(format!("{base}.txt"), &v.message).ok();
    }
}

#[cfg(feature = "profraw")]
fn replay_proto_corpus(args: &Args, dir: &str, limit: Option<usize>, output: Option<&str>) {
    static REJECTED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    use cedar_policy::proto::traits::Protobuf;
    use cedar_policy::{PolicySet, Schema, ValidationMode};
    #[cfg(not(feature = "lean-gen"))]
    use cedar_policy::Validator;
    use cedar_drt_coverage::source_cov_tracker::{count_hit, num_counters, reset_counters};
    use std::fs;

    // FAITHFUL replay: drive the SAME `--target` oracle the run used (`make_target(args)`),
    // one source of truth — full DRT (Rust validate + Lean FFI + compare) for validation-drt,
    // or the symbolic compiler for a symcc-* target. Not hardcoded, so the exercised code
    // matches the instrumented crate for whichever target. Without `lean-gen` (local quick
    // builds) it falls back to Rust-only validate.
    #[cfg(feature = "lean-gen")]
    let target = make_target(args);

    let mut entries: Vec<_> = fs::read_dir(dir)
        .expect("failed to read corpus directory")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_file())
        .collect();
    entries.sort_by_key(|p| p.metadata().and_then(|m| m.modified()).unwrap_or(std::time::SystemTime::UNIX_EPOCH));
    if let Some(n) = limit {
        entries.truncate(n);
    }

    // CHEAP cumulative coverage: a replay has NO generation between inputs (only proto
    // decode + the validate target), so — unlike the fused collect — we do NOT need to
    // reset the LLVM counters per input to exclude generation. We reset ONCE here and let
    // the counters accumulate; we read the array (`count_hit`, O(counters)) only at the
    // ~`num_snaps` snapshot points, NOT per input. This removes the per-input memset+read
    // of the whole counter array — the memory-bandwidth cost that collapsed the fused
    // collect under parallelism — so full (uncapped) coverage scales with cores.
    reset_counters();
    eprintln!("Replaying {} protobuf corpus entries ({} counters, reset-once cumulative)", entries.len(), num_counters());
    let mut validated = 0u64;
    let mut failed = 0u64;
    let mut mismatches = 0u64;

    // Over-time coverage: snapshots record the cumulative region-hit COUNT (`count_hit`),
    // NOT intermediate profraw dumps (those would pile up locally). A single `final.profraw`
    // is written at the end (the live counters ARE the cumulative union) for the per-approach
    // llvm-profdata merge, which `coverage_analyze.py` maps to source lines with the
    // harness-exclusion regex. `REPLAY_PROFRAW_DIR` = output dir; `REPLAY_SNAPSHOTS` =
    // number of evenly-spaced over-time points (default 20).
    let snap_dir = std::env::var("REPLAY_PROFRAW_DIR").ok();
    let num_snaps: usize = std::env::var("REPLAY_SNAPSHOTS").ok()
        .and_then(|s| s.parse().ok()).unwrap_or(20);
    if let Some(ref d) = snap_dir { fs::create_dir_all(d).ok(); }
    // Files are either single combined entries (`id_*.bin`) or S3 batch objects
    // (`batch_*.bin` = many `[len‖entry]` frames, `decode_batch`). Each entry is
    // `[schema_len:u32-le ‖ schema-proto ‖ policies-proto]`. Snapshot per file-group
    // so we get ~num_snaps points without pre-scanning the entry count.
    // Split a batch object (`[u32-le len ‖ payload]` repeated) into entries.
    // Duplicated from experiment::s3 (which is `s3`-feature-gated) so the
    // instrumented replay binary need not pull the aws deps.
    fn decode_batch(data: &[u8]) -> Vec<Vec<u8>> {
        let mut out = Vec::new();
        let mut pos = 0;
        while pos + 4 <= data.len() {
            let len = u32::from_le_bytes([data[pos], data[pos+1], data[pos+2], data[pos+3]]) as usize;
            pos += 4;
            if pos + len > data.len() { break; }
            out.push(data[pos..pos+len].to_vec());
            pos += len;
        }
        out
    }
    let n_files = entries.len();
    let snap_file_every = if num_snaps > 0 { (n_files / num_snaps).max(1) } else { usize::MAX };
    let mut snap_manifest: Vec<serde_json::Value> = Vec::new();
    let start = std::time::Instant::now();

    let validate_entry = |data: &[u8], validated: &mut u64, failed: &mut u64, mismatches: &mut u64| {
        if data.len() < 4 { *failed += 1; return; }
        let schema_len = u32::from_le_bytes([data[0], data[1], data[2], data[3]]) as usize;
        if data.len() < 4 + schema_len { *failed += 1; return; }
        let schema = match Schema::decode(&data[4..4 + schema_len]) {
            Ok(s) => s, Err(_) => { *failed += 1; return; }
        };
        let policies = match PolicySet::decode(&data[4 + schema_len..]) {
            Ok(p) => p, Err(_) => { *failed += 1; return; }
        };
        // No per-input counter reset — coverage accumulates into the live counters.
        let is_mismatch = {
            #[cfg(feature = "lean-gen")]
            {
                use cedar_drt_coverage::target::Target;
                let input = cedar_drt_coverage::ValidationInput {
                    schema, policies, raw_bytes: None, provenance: None,
                };
                target.run(&input).is_violation()
            }
            #[cfg(not(feature = "lean-gen"))]
            { let r = Validator::new(schema).validate(&policies, ValidationMode::Strict); if !r.validation_passed() { REJECTED.fetch_add(1, std::sync::atomic::Ordering::Relaxed); } false }
        };
        if is_mismatch { *mismatches += 1; }
        *validated += 1;
    };

    for (fi, path) in entries.iter().enumerate() {
        let data = match fs::read(path) { Ok(d) => d, Err(_) => { failed += 1; continue; } };
        let is_batch = path.file_name().and_then(|n| n.to_str())
            .map(|n| n.starts_with("batch_")).unwrap_or(false);
        if is_batch {
            for entry in decode_batch(&data) {
                validate_entry(&entry, &mut validated, &mut failed, &mut mismatches);
            }
        } else {
            validate_entry(&data, &mut validated, &mut failed, &mut mismatches);
        }

        // Record the cumulative region-hit count after every file-group (reads the array
        // only ~num_snaps times total — not per input).
        if snap_dir.is_some() && (fi + 1) % snap_file_every == 0 {
            snap_manifest.push(serde_json::json!({
                "snapshot": snap_manifest.len(), "corpus_idx": validated, "validated": validated,
                "elapsed_secs": start.elapsed().as_secs_f64(),
                "counters_hit": count_hit(),
            }));
        }
    }

    // ONE final profraw (validation-only union) for the per-approach llvm-profdata
    // merge. The live counters already hold the cumulative union (we never reset mid-run).
    if let Some(ref d) = snap_dir {
        cedar_drt_coverage::profraw::dump_profraw_to(&format!("{d}/final.profraw"));
        snap_manifest.push(serde_json::json!({
            "snapshot": snap_manifest.len(), "corpus_idx": validated, "validated": validated,
            "elapsed_secs": start.elapsed().as_secs_f64(), "file": "final.profraw",
            "counters_hit": count_hit(),
        }));
        fs::write(format!("{d}/snapshots.json"),
            serde_json::to_string_pretty(&snap_manifest).unwrap()).ok();
    }

    eprintln!("REJECTED by Rust strict validate = {} / {}", REJECTED.load(std::sync::atomic::Ordering::Relaxed), validated);

    eprintln!("Done. {} validated, {} failed, {} DRT mismatches, {} regions hit",
        validated, failed, mismatches, count_hit());

    if let Some(out_path) = output {
        fs::write(out_path, serde_json::to_string_pretty(&snap_manifest).unwrap()).ok();
        eprintln!("  Per-entry data written to: {out_path}");
    }
}

/// Stream a corpus from S3 and validate each entry under `-C instrument-coverage`,
/// dumping cumulative `.profraw` snapshots — WITHOUT ever storing the corpus locally
/// (each batch is decoded in memory by `stream_batches` and dropped). The caller
/// (coverage_analyze.py) runs llvm-cov on the snapshots, uploads them to S3, and
/// deletes the transient local copies.
#[cfg(all(feature = "profraw", feature = "s3"))]
fn replay_s3_corpus(args: &Args, bucket: &str, prefix: &str, shard: usize, shards: usize) {
    use cedar_policy::proto::traits::Protobuf;
    use cedar_policy::{PolicySet, Schema, ValidationMode};
    #[cfg(not(feature = "lean-gen"))]
    use cedar_policy::Validator;
    use cedar_drt_coverage::source_cov_tracker::{count_hit, num_counters, reset_counters};
    use std::fs;

    let snap_dir = std::env::var("REPLAY_PROFRAW_DIR").ok();
    let num_snaps: usize = std::env::var("REPLAY_SNAPSHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(20);
    let snap_every: u64 = std::env::var("REPLAY_SNAP_EVERY").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    if let Some(ref d) = snap_dir { fs::create_dir_all(d).ok(); }

    // FAITHFUL replay driving the SAME `--target` oracle the run used — `make_target(args)`,
    // NOT a hardcoded `ValidationDrt`. This matters for non-validation targets: a symcc run
    // (`--target symcc-term-never-errors`) must replay through `SymccTermDrt` so the exercised
    // code is the symbolic COMPILER (cedar-policy-symcc), matching the instrumented crate —
    // otherwise it'd run the validator and record zero symcc coverage. `coverage_analyze.py`
    // always passes `--target` (default `validation-drt`), so validation runs are unchanged.
    // Reset-once cumulative (see `replay_proto_corpus`): no per-input counter reset — the
    // memory-bandwidth cost that collapsed under parallelism — just read `count_hit` at
    // snapshot points. Full uncapped coverage that scales with cores.
    #[cfg(feature = "lean-gen")]
    let target = make_target(args);
    reset_counters();
    let corpus_prefix = format!("{prefix}/corpus");
    eprintln!("Streaming corpus from s3://{bucket}/{corpus_prefix} shard {shard}/{shards} ({} counters, reset-once cumulative)",
        num_counters());

    let mut validated = 0u64;
    let mut failed = 0u64;
    let mut mismatches = 0u64;
    // Diagnostic: count corpus inputs the Rust STRICT validator rejects on replay. For the
    // welltyped guided corpus this MUST be ~0 (it was logged only if is_well_typed passed);
    // a nonzero count means the input became ill-typed between fuzz-time and replay (proto
    // encode/decode roundtrip). Gated by REPLAY_COUNT_ILLTYPED (extra validate ⇒ slower).
    let count_illtyped = std::env::var("REPLAY_COUNT_ILLTYPED").is_ok();
    // FAIR re-measure: when set, SKIP inputs the Rust strict validator rejects so coverage
    // reflects only genuinely well-typed inputs (removes error-path contamination from a
    // generator whose well-typed predicate over-accepts relative to Rust strict).
    let welltyped_only = std::env::var("REPLAY_WELLTYPED_ONLY").is_ok();
    let dump_illtyped: usize = std::env::var("REPLAY_DUMP_ILLTYPED").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let mut dumped_ill = 0usize;
    let mut illtyped = 0u64;
    let dump_n: usize = std::env::var("REPLAY_DUMP").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let mut dumped: usize = 0;
    let mut snap_manifest: Vec<serde_json::Value> = Vec::new();
    let start = std::time::Instant::now();

    // SINGLE-THREAD runtime: this shard just streams S3 objects sequentially (one GET in
    // flight at a time), so a multi-thread runtime's ~num_cpus worker threads would sit idle.
    // Under the flattened (approach×rep×shard) pool, ~191 concurrent shard PROCESSES each
    // spinning a ~192-thread runtime = ~36k threads → OS thread/FD exhaustion → some processes
    // panic at runtime creation and die before writing `final.profraw` → silently-dropped
    // shards → truncated coverage. `new_current_thread` = 1 thread/process, no exhaustion, and
    // no perf loss (the work is sequential I/O). `enable_all` keeps the I/O+time drivers the
    // AWS SDK needs.
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();
    rt.block_on(async {
        let client = cedar_drt_coverage::experiment::s3::make_client().await;
        // Each streamed `buf` is one corpus entry: [schema_len ‖ schema ‖ policies].
        let _ = cedar_drt_coverage::experiment::s3::stream_batches_sharded(&client, bucket, &corpus_prefix, shard, shards, |buf| {
            if buf.len() < 4 { failed += 1; return; }
            let schema_len = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]) as usize;
            if buf.len() < 4 + schema_len { failed += 1; return; }
            let schema = match Schema::decode(&buf[4..4 + schema_len]) { Ok(s) => s, Err(_) => { failed += 1; return; } };
            let policies = match PolicySet::decode(&buf[4 + schema_len..]) { Ok(p) => p, Err(_) => { failed += 1; return; } };
            if count_illtyped || welltyped_only {
                // Re-validate the DECODED (post-roundtrip) input with the Rust strict validator.
                let res = cedar_policy::Validator::new(schema.clone())
                    .validate(&policies, cedar_policy::ValidationMode::Strict);
                if !res.validation_passed() {
                    illtyped += 1;
                    // Dig: dump the first REPLAY_DUMP_ILLTYPED rejected inputs' strict errors
                    // (+ the policy) so we can see WHY the relational generator's "well-typed"
                    // policies are rejected by Rust strict.
                    if dump_illtyped > 0 && dumped_ill < dump_illtyped {
                        let errs: Vec<String> = res.validation_errors().map(|e| e.to_string()).collect();
                        eprintln!("===ILLTYPED {dumped_ill}===\n  ERRORS: {errs:?}\n  POLICY: {policies}\n");
                        dumped_ill += 1;
                    }
                    if welltyped_only { return; } // exclude from coverage (fair re-measure)
                }
            }
            // Diagnostic: dump the first REPLAY_DUMP decoded policies (Display) to inspect
            // whether the SCOPE head is constrained vs inlined into the `when` clause.
            if dump_n > 0 && dumped < dump_n {
                for p in policies.policies() {
                    eprintln!("===POLICY {dumped}===\n{p}\n");
                    dumped += 1;
                    if dumped >= dump_n { break; }
                }
            }
            let is_mismatch = {
                #[cfg(feature = "lean-gen")]
                {
                    use cedar_drt_coverage::target::Target;
                    let input = cedar_drt_coverage::ValidationInput {
                        schema, policies, raw_bytes: None, provenance: None,
                    };
                    target.run(&input).is_violation()
                }
                #[cfg(not(feature = "lean-gen"))]
                { let _ = Validator::new(schema).validate(&policies, ValidationMode::Strict); false }
            };
            if is_mismatch { mismatches += 1; }
            validated += 1;
            // Over-time point = cumulative region-hit COUNT (reads the array only every
            // snap_every inputs, not per input).
            if snap_dir.is_some() && num_snaps > 0 && validated % snap_every == 0 {
                snap_manifest.push(serde_json::json!({
                    "snapshot": snap_manifest.len(), "corpus_idx": validated, "validated": validated,
                    "elapsed_secs": start.elapsed().as_secs_f64(),
                    "counters_hit": count_hit(),
                }));
            }
        }).await;
    });

    // The live counters already hold the cumulative union (never reset mid-run).
    if let Some(ref d) = snap_dir {
        cedar_drt_coverage::profraw::dump_profraw_to(&format!("{d}/final.profraw"));
        snap_manifest.push(serde_json::json!({
            "snapshot": snap_manifest.len(), "corpus_idx": validated, "validated": validated,
            "elapsed_secs": start.elapsed().as_secs_f64(), "file": "final.profraw",
            "counters_hit": count_hit(),
        }));
        fs::write(format!("{d}/snapshots.json"), serde_json::to_string_pretty(&snap_manifest).unwrap()).ok();
    }
    if count_illtyped {
        eprintln!("ILLTYPED-ON-REPLAY: {illtyped} / {validated} inputs the Rust strict validator REJECTS (should be ~0 for welltyped corpus)");
    }
    eprintln!("Done. {validated} validated, {failed} failed, {mismatches} DRT mismatches, {} regions hit", count_hit());
}

#[cfg(feature = "profraw")]
fn replay_fuzz_corpus(dir: &str, limit: Option<usize>, output: Option<&str>) {
    use cedar_policy::{Schema, ValidationMode, Validator};
    use cedar_policy_generators::{schema, schema_gen::SchemaGen, settings::ABACSettings};
    use cedar_drt_coverage::source_cov_tracker::SourceCovTracker;
    use arbitrary::Unstructured;
    use std::fs;

    let mut entries: Vec<_> = fs::read_dir(dir)
        .expect("failed to read corpus directory")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_file())
        .collect();
    entries.sort_by_key(|p| p.metadata().and_then(|m| m.modified()).unwrap_or(std::time::SystemTime::UNIX_EPOCH));
    if let Some(n) = limit {
        entries.truncate(n);
    }

    let settings = ABACSettings {
        enable_additional_attributes: true,
        ..ABACSettings::type_directed()
    };

    let mut tracker = SourceCovTracker::new(None);
    eprintln!("Replaying {} fuzz corpus entries ({} counters)", entries.len(), cedar_drt_coverage::source_cov_tracker::num_counters());
    let mut validated = 0u64;
    let mut failed = 0u64;

    for path in &entries {
        let data = match fs::read(path) {
            Ok(d) => d,
            Err(_) => { failed += 1; continue; }
        };

        let mut u = Unstructured::new(&data);
        let gen_schema = match schema::Schema::arbitrary(settings.clone(), &mut u) {
            Ok(s) => s,
            Err(_) => { failed += 1; continue; }
        };
        let hierarchy = match gen_schema.arbitrary_hierarchy(&mut u) {
            Ok(h) => h,
            Err(_) => { failed += 1; continue; }
        };
        let policy = match gen_schema.arbitrary_policy(&hierarchy, &mut u) {
            Ok(p) => p,
            Err(_) => { failed += 1; continue; }
        };
        let schema = match Schema::try_from(gen_schema) {
            Ok(s) => s,
            Err(_) => { failed += 1; continue; }
        };
        let policies = policy.into_policy_set();

        tracker.run_and_record(|| {
            let validator = Validator::new(schema);
            let _result = validator.validate(&policies, ValidationMode::Strict);
        }, None);
        validated += 1;
    }

    let last = tracker.snapshots.last();
    eprintln!("Done. {} validated, {} failed, coverage: {:.2}%",
        validated, failed, last.map(|s| s.coverage_pct).unwrap_or(0.0));

    if let Some(out_path) = output {
        tracker.write_json(out_path);
        eprintln!("  Per-entry data written to: {out_path}");
    }
}

fn main() {
    let args = Args::parse();

    // Replay modes: run corpus entries through validator with in-process coverage tracking
    #[cfg(feature = "profraw")]
    {
        if let Some(ref proto_dir) = args.replay_proto {
            replay_proto_corpus(&args, proto_dir, args.replay_limit, args.replay_output.as_deref());
            return;
        }
        if let Some(ref fuzz_dir) = args.replay_fuzz {
            replay_fuzz_corpus(fuzz_dir, args.replay_limit, args.replay_output.as_deref());
            return;
        }
        #[cfg(feature = "s3")]
        if let (Some(bucket), Some(prefix)) = (args.replay_s3_bucket.as_ref(), args.replay_s3_prefix.as_ref()) {
            replay_s3_corpus(&args, bucket, prefix, args.replay_shard, args.replay_shards);
            return;
        }
    }

    let duration = args.duration.map(Duration::from_secs);
    let max_attempts = args.iterations.unwrap_or(u64::MAX);
    let report_interval = args.report_interval;
    let target = make_target(&args);

    // Adaptive generator needs special handling (mutable)
    if matches!(args.generator, GeneratorKind::Adaptive) {
        let mut gen = AdaptiveGenerator::new();
        eprintln!(
            "Running generator 'adaptive' -> target '{}' for {}s (seed={}, {} configs)",
            target.name(),
            duration.map_or("∞".to_string(), |d| d.as_secs().to_string()),
            args.seed,
            gen.configs.len(),
        );

        let stats = run_adaptive_session(&mut gen, &*target, args.seed, max_attempts, duration, |i, v| {
            if i % report_interval == 0 {
                eprintln!("  ... {} attempts, {} valid", i, v);
            }
        });

        // Print top configs by weight
        let mut sorted: Vec<_> = gen.configs.iter().collect();
        sorted.sort_by(|a, b| b.weight.partial_cmp(&a.weight).unwrap());
        eprintln!("Top configs by weight:");
        for c in sorted.iter().take(10) {
            eprintln!("  buf={:>6} depth={:>2} weight={:.1}", c.buf_size, c.max_depth, c.weight);
        }

        print_summary(&stats, &args);
        return;
    }

    let generator = make_generator(&args);

    if let Some(dur) = duration {
        eprintln!(
            "Running generator '{}' -> target '{}' for {}s (seed={})",
            generator.name(),
            target.name(),
            dur.as_secs(),
            args.seed,
        );
    } else {
        eprintln!(
            "Running generator '{}' -> target '{}' for {} attempts (seed={})",
            generator.name(),
            target.name(),
            max_attempts,
            args.seed,
        );
    }

    let snapshot_interval = args.snapshot_interval.map(Duration::from_secs);
    let corpus_dir = args.corpus_dir.clone().map(std::path::PathBuf::from);

    let stats = run_coverage_session(
        &*generator, &*target, args.seed, max_attempts, duration,
        snapshot_interval, corpus_dir,
        |i, v| {
            if i % report_interval == 0 {
                eprintln!("  ... {} attempts, {} valid", i, v);
            }
        },
    );

    if let Some(ref path) = args.snapshot_output {
        if !stats.snapshots.is_empty() {
            let json = serde_json::to_string_pretty(&stats.snapshots).unwrap();
            std::fs::write(path, json).unwrap();
            eprintln!("  Edge snapshots written to: {path}");
        }
    }

    print_summary(&stats, &args);
}

fn print_summary(stats: &cedar_drt_coverage::SessionStats, args: &Args) {
    eprintln!(
        "Done. {} valid inputs from {} attempts in {:.2}s ({:.0} attempts/sec)",
        stats.valid, stats.attempts, stats.elapsed_secs,
        stats.attempts as f64 / stats.elapsed_secs,
    );

    if stats.total_nodes > 0 {
        eprintln!(
            "  AST nodes: {} total ({:.1} avg/input)",
            stats.total_nodes,
            stats.total_nodes as f64 / stats.valid.max(1) as f64,
        );
        let n_parents = 12u64;
        let n_all = 16u64;
        let total_2paths = n_parents * n_all;
        let total_3paths = n_parents * n_parents * n_all;
        eprintln!("  2-paths covered: {}/{} ({:.1}%)", stats.kpath2_count, total_2paths, 100.0 * stats.kpath2_count as f64 / total_2paths as f64);
        eprintln!("  3-paths covered: {}/{} ({:.1}%)", stats.kpath3_count, total_3paths, 100.0 * stats.kpath3_count as f64 / total_3paths as f64);
    }

    if stats.novel_inputs > 0 || stats.total_features > 0 {
        eprintln!(
            "  Novel inputs (expanded coverage): {} / {} ({:.1}%)",
            stats.novel_inputs, stats.valid,
            100.0 * stats.novel_inputs as f64 / stats.valid.max(1) as f64,
        );
        eprintln!("  Total edge features discovered: {}", stats.total_features);
        let valid_throughput = stats.valid as f64 / stats.elapsed_secs;
        let novel_throughput = stats.novel_inputs as f64 / stats.elapsed_secs;
        eprintln!("  Throughput: {:.1} valid/sec, {:.2} novel/sec", valid_throughput, novel_throughput);
        if args.corpus_dir.is_some() {
            eprintln!("  Corpus saved: {} inputs", stats.novel_inputs);
        }
    }

    if !stats.violations.is_empty() {
        eprintln!("  VIOLATIONS: {} found!", stats.violations.len());
        for v in stats.violations.iter().take(5) {
            eprintln!("    seed={}: {}", v.seed, &v.message[..v.message.len().min(120)]);
        }
        if stats.violations.len() > 5 {
            eprintln!("    ... and {} more", stats.violations.len() - 5);
        }
        if let Some(ref dir) = args.violations_dir {
            save_violations(stats, dir);
            eprintln!("  Violation inputs saved to: {dir}");
        }
    }

    if !stats.top_constructor_counts.is_empty() {
        let mut ctors: Vec<_> = stats.top_constructor_counts.iter().collect();
        ctors.sort_by(|a, b| b.1.cmp(a.1));
        eprintln!("  Top constructors:");
        for (name, count) in ctors.iter().take(8) {
            eprintln!("    {:>8}: {}", name, count);
        }
    }
}

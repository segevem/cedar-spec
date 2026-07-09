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

    /// Only replay the first N entries (sorted by modification time)
    #[arg(long)]
    replay_limit: Option<usize>,

    /// Output JSON file for per-entry coverage data during replay
    #[arg(long)]
    replay_output: Option<String>,
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
fn replay_proto_corpus(dir: &str, limit: Option<usize>, output: Option<&str>) {
    use cedar_policy::proto::traits::Protobuf;
    use cedar_policy::{PolicySet, Schema, ValidationMode, Validator};
    use cedar_drt_coverage::source_cov_tracker::SourceCovTracker;
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

    let mut tracker = SourceCovTracker::new(None);
    eprintln!("Replaying {} protobuf corpus entries ({} counters)", entries.len(), cedar_drt_coverage::source_cov_tracker::num_counters());
    let mut validated = 0u64;
    let mut failed = 0u64;

    for path in &entries {
        let data = match fs::read(path) {
            Ok(d) => d,
            Err(_) => { failed += 1; continue; }
        };
        if data.len() < 4 { failed += 1; continue; }
        let schema_len = u32::from_le_bytes([data[0], data[1], data[2], data[3]]) as usize;
        if data.len() < 4 + schema_len { failed += 1; continue; }

        let schema = match Schema::decode(&data[4..4 + schema_len]) {
            Ok(s) => s,
            Err(_) => { failed += 1; continue; }
        };
        let policies = match PolicySet::decode(&data[4 + schema_len..]) {
            Ok(p) => p,
            Err(_) => { failed += 1; continue; }
        };

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
            replay_proto_corpus(proto_dir, args.replay_limit, args.replay_output.as_deref());
            return;
        }
        if let Some(ref fuzz_dir) = args.replay_fuzz {
            replay_fuzz_corpus(fuzz_dir, args.replay_limit, args.replay_output.as_deref());
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

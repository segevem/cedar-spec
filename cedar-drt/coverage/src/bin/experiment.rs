use std::path::PathBuf;
use std::time::Duration;

use clap::{Parser, Subcommand, ValueEnum};

use cedar_drt_coverage::experiment::config::GeneratorParams;
use cedar_drt_coverage::experiment::collect::run_collection_session;
use cedar_drt_coverage::experiment::orchestrator::{core_for_rep, mean_stddev, num_cores};
use cedar_drt_coverage::experiment::output::{write_throughput_result, write_throughput_summary};
use cedar_drt_coverage::experiment::throughput::run_throughput_rep;
use cedar_drt_coverage::generators::{ABACGenerator, RetryABACGenerator};
use cedar_drt_coverage::target::{self, Target};
use cedar_drt_coverage::ValidationGenerator;

#[derive(Clone, Debug, ValueEnum)]
enum GeneratorArg {
    TypeDirected,
    Undirected,
    RetryTypeDirected,
    RetryUndirected,
    #[cfg(feature = "lean-gen")]
    LeanTypeof,
    #[cfg(feature = "lean-gen")]
    LeanSchemaTypeof,
}

impl GeneratorArg {
    fn as_str(&self) -> &'static str {
        match self {
            Self::TypeDirected => "type-directed",
            Self::Undirected => "undirected",
            Self::RetryTypeDirected => "retry-type-directed",
            Self::RetryUndirected => "retry-undirected",
            #[cfg(feature = "lean-gen")]
            Self::LeanTypeof => "lean-typeof",
            #[cfg(feature = "lean-gen")]
            Self::LeanSchemaTypeof => "lean-schema-typeof",
        }
    }
}

#[derive(Clone, Debug, ValueEnum)]
enum TargetArg {
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
}

impl TargetArg {
    fn as_str(&self) -> &'static str {
        match self {
            Self::RustOnly => "rust-only",
            #[cfg(feature = "lean-gen")]
            Self::ValidationDrt => "validation-drt",
            #[cfg(feature = "lean-gen")]
            Self::LevelValidationDrt => "level-validation-drt",
            #[cfg(feature = "symcc")]
            Self::SymccTermAlwaysAllows => "symcc-term-always-allows",
            #[cfg(feature = "symcc")]
            Self::SymccTermAlwaysDenies => "symcc-term-always-denies",
            #[cfg(feature = "symcc")]
            Self::SymccTermNeverErrors => "symcc-term-never-errors",
        }
    }
}

#[derive(Parser)]
#[command(name = "cedar-experiment", about = "Orchestrate phased Cedar DRT experiments")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Phase 1: Measure throughput with minimal instrumentation
    Throughput(ThroughputArgs),
    /// Phase 2: Collect N valid inputs, saving all to corpus
    Collect(CollectArgs),
    /// Phase 3: Analyze collected corpus (metrics from per_input.jsonl)
    Analyze(AnalyzeArgs),
    /// Run all phases sequentially
    RunAll(RunAllArgs),
}

#[derive(Parser)]
struct ThroughputArgs {
    // Defaulted so guided runs (which use --fuzz-target and ignore the generator) need
    // not pass it; non-guided callers always pass --generator explicitly.
    #[arg(long, value_enum, default_value = "type-directed")]
    generator: GeneratorArg,

    #[arg(long, value_enum, default_value = "rust-only")]
    target: TargetArg,

    /// Use coverage-guided fuzzing (cargo fuzz) instead of unguided generation
    #[arg(long)]
    guided: bool,

    /// Fuzz target name for guided mode (e.g. validation-drt-type-directed)
    #[arg(long, default_value = "validation-drt-type-directed")]
    fuzz_target: String,

    /// Duration in seconds for each repetition
    #[arg(long)]
    duration: u64,

    /// Number of repetitions
    #[arg(long, default_value = "5")]
    reps: u32,

    /// Base seed (each rep adds its rep_id)
    #[arg(long, default_value = "0")]
    seed_base: u64,

    /// Per-rep seed stride: rep i starts at seed_base + i*seed_stride. Must exceed
    /// the per-rep input count N so reps draw disjoint, independent samples
    /// (the old hardcoded 1e6 was < N, so reps overlapped -> invalid CIs).
    #[arg(long, default_value = "1000000000")]
    seed_stride: u64,

    /// Output directory for results
    #[arg(long)]
    output_dir: String,

    /// Pin each repetition to a CPU core
    #[arg(long)]
    cpu_pin: bool,

    /// PRNG buffer size for ABAC generators
    #[arg(long, default_value = "65536")]
    buffer_size: usize,

    /// Specimen size budget for Lean generators
    #[arg(long, default_value = "20")]
    lean_size: u32,

    /// Specimen strategy variant (budget-aware, graded-uniform, default, flat)
    #[arg(long, default_value = "budget-aware")]
    strategy: String,

    /// Snapshot interval in seconds (for time-series recording)
    #[arg(long, default_value = "1")]
    snapshot_interval: u64,

    /// Single-rep mode (used internally by orchestrator)
    #[arg(long, hide = true)]
    single_rep: Option<u32>,
}

#[derive(Parser)]
struct CollectArgs {
    // Defaulted so guided runs (which use --fuzz-target and ignore the generator) need
    // not pass it; non-guided callers always pass --generator explicitly.
    #[arg(long, value_enum, default_value = "type-directed")]
    generator: GeneratorArg,

    #[arg(long, value_enum, default_value = "rust-only")]
    target: TargetArg,

    /// Use coverage-guided fuzzing (cargo fuzz) instead of unguided generation
    #[arg(long)]
    guided: bool,

    /// Fuzz target name for guided mode
    #[arg(long, default_value = "validation-drt-type-directed")]
    fuzz_target: String,

    /// Number of total executions to run (valid + invalid for guided, valid only for unguided)
    #[arg(long)]
    valid_count: u64,

    /// Guided-only: stop collecting once the collected valid count reaches the valid
    /// count the CONCURRENT throughput probe produced (read from its FuzzStats). Runs the
    /// guided collect UNBOUNDED and matches the throughput term count exactly (collect is
    /// slower due to logging I/O, so it runs a bit past throughput's wall-clock). The two
    /// run in true parallel on separate cores. Overrides --valid-count / --guided-max-secs.
    #[arg(long)]
    guided_match_throughput: bool,

    /// Guided-only: wall-clock bound for the guided collect (`-max_total_time`), instead
    /// of a `-runs` count. Ignored when --guided-match-throughput is set.
    #[arg(long)]
    guided_max_secs: Option<u64>,

    /// Number of repetitions
    #[arg(long, default_value = "5")]
    reps: u32,

    /// Base seed
    #[arg(long, default_value = "0")]
    seed_base: u64,

    /// Per-rep seed stride: rep i starts at seed_base + i*seed_stride. Must exceed
    /// the per-rep input count N so reps draw disjoint, independent samples
    /// (the old hardcoded 1e6 was < N, so reps overlapped -> invalid CIs).
    #[arg(long, default_value = "1000000000")]
    seed_stride: u64,

    /// Output directory
    #[arg(long)]
    output_dir: String,

    /// Pin each repetition to a CPU core
    #[arg(long)]
    cpu_pin: bool,

    /// PRNG buffer size for ABAC generators
    #[arg(long, default_value = "65536")]
    buffer_size: usize,

    /// Specimen size budget
    #[arg(long, default_value = "20")]
    lean_size: u32,

    /// Specimen strategy variant (budget-aware, graded-uniform, default, flat)
    #[arg(long, default_value = "budget-aware")]
    strategy: String,

    /// Snapshot interval in seconds
    #[arg(long, default_value = "10")]
    snapshot_interval: u64,

    /// Single-rep mode (used internally)
    #[arg(long, hide = true)]
    single_rep: Option<u32>,

    /// Upload results to S3 bucket
    #[cfg(feature = "s3")]
    #[arg(long)]
    s3_bucket: Option<String>,

    /// S3 key prefix
    #[cfg(feature = "s3")]
    #[arg(long)]
    s3_prefix: Option<String>,
}

#[derive(Parser)]
struct AnalyzeArgs {
    /// Output directory for writing results (always required)
    #[arg(long)]
    output_dir: String,

    /// Corpus format: "fuzz" (raw libfuzzer buffers), "proto" (protobuf PolicySet), or "jsonl"
    #[arg(long, default_value = "fuzz")]
    format: String,

    /// Number of repetitions to analyze (reads collect/rep_00..rep_N)
    #[arg(long, default_value = "5")]
    reps: u32,

    /// Read corpus from S3 instead of local disk (bucket name)
    #[cfg(feature = "s3")]
    #[arg(long)]
    s3_bucket: Option<String>,

    /// S3 key prefix for reading corpus (e.g. "experiment/td-10min/collect/rep_00/corpus")
    #[cfg(feature = "s3")]
    #[arg(long)]
    s3_prefix: Option<String>,

    /// Upload analysis results to S3
    #[cfg(feature = "s3")]
    #[arg(long)]
    s3_upload_bucket: Option<String>,

    /// S3 prefix for uploading results
    #[cfg(feature = "s3")]
    #[arg(long)]
    s3_upload_prefix: Option<String>,
}

#[derive(Parser)]
struct RunAllArgs {
    // Defaulted so guided runs (which use --fuzz-target and ignore the generator) need
    // not pass it; non-guided callers always pass --generator explicitly.
    #[arg(long, value_enum, default_value = "type-directed")]
    generator: GeneratorArg,

    #[arg(long, value_enum, default_value = "rust-only")]
    target: TargetArg,

    /// Duration in seconds for throughput phase
    #[arg(long)]
    duration: u64,

    /// Number of repetitions for each phase
    #[arg(long, default_value = "5")]
    reps: u32,

    /// Base seed
    #[arg(long, default_value = "0")]
    seed_base: u64,

    /// Per-rep seed stride: rep i starts at seed_base + i*seed_stride. Must exceed
    /// the per-rep input count N so reps draw disjoint, independent samples
    /// (the old hardcoded 1e6 was < N, so reps overlapped -> invalid CIs).
    #[arg(long, default_value = "1000000000")]
    seed_stride: u64,

    /// Output directory
    #[arg(long)]
    output_dir: String,

    /// Pin repetitions to CPU cores
    #[arg(long)]
    cpu_pin: bool,

    /// PRNG buffer size
    #[arg(long, default_value = "65536")]
    buffer_size: usize,

    /// Specimen size budget
    #[arg(long, default_value = "20")]
    lean_size: u32,

    /// Specimen strategy variant (budget-aware, graded-uniform, default, flat)
    #[arg(long, default_value = "budget-aware")]
    strategy: String,
}

fn make_generator(kind: &GeneratorArg, params: &GeneratorParams) -> Box<dyn ValidationGenerator> {
    match kind {
        GeneratorArg::TypeDirected => {
            let mut gen = ABACGenerator::type_directed();
            gen.buffer_size = params.buffer_size;
            Box::new(gen)
        }
        GeneratorArg::Undirected => {
            let mut gen = ABACGenerator::undirected();
            gen.buffer_size = params.buffer_size;
            Box::new(gen)
        }
        GeneratorArg::RetryTypeDirected => {
            let mut gen = RetryABACGenerator::type_directed();
            gen.inner.buffer_size = params.buffer_size;
            Box::new(gen)
        }
        GeneratorArg::RetryUndirected => {
            let mut gen = RetryABACGenerator::undirected();
            gen.inner.buffer_size = params.buffer_size;
            Box::new(gen)
        }
        #[cfg(feature = "lean-gen")]
        GeneratorArg::LeanTypeof => {
            let strategy = params.scoring.clone().unwrap_or_else(|| "budget-aware".to_string());
            Box::new(cedar_drt_coverage::lean_gen::LeanTypeOfGenerator::with_strategy(
                params.lean_size, strategy,
            ))
        }
        #[cfg(feature = "lean-gen")]
        GeneratorArg::LeanSchemaTypeof => {
            // Schema fuel defaults to the term fuel; override via CEDAR_SCHEMA_SIZE
            // (e.g. richer schemas: CEDAR_SCHEMA_SIZE=20 with --lean-size 12).
            let schema_size = std::env::var("CEDAR_SCHEMA_SIZE")
                .ok()
                .and_then(|s| s.parse::<u32>().ok())
                .unwrap_or(params.lean_size);
            // Policies generated per FFI call (one schema + this many terms).
            // Smaller batches => each blocking `refill` is cheaper, so the
            // throughput probe's duration check fires more often (less overrun)
            // and its rate averages over many more schemas (less schema-variance
            // skew); also yields more schema diversity in the collected corpus.
            // Override with CEDAR_BATCH_SIZE.
            let batch_size = std::env::var("CEDAR_BATCH_SIZE")
                .ok()
                .and_then(|s| s.parse::<u32>().ok())
                .unwrap_or(100);
            let strategy = params.scoring.clone().unwrap_or_else(|| "budget-aware".to_string());
            Box::new(cedar_drt_coverage::lean_gen::LeanSchemaTypeOfGenerator::with_sizes_seeded(
                schema_size,
                params.lean_size,
                strategy,
                batch_size,
                params.start_seed,
            ))
        }
    }
}

fn make_target(kind: &TargetArg) -> Box<dyn Target> {
    match kind {
        TargetArg::RustOnly => Box::new(target::RustValidation),
        #[cfg(feature = "lean-gen")]
        TargetArg::ValidationDrt => Box::new(target::ValidationDrt::new()),
        #[cfg(feature = "lean-gen")]
        TargetArg::LevelValidationDrt => Box::new(target::LevelValidationDrt::new(3)),
        #[cfg(feature = "symcc")]
        TargetArg::SymccTermAlwaysAllows => {
            Box::new(target::SymccTermDrt::new(target::SymccCheck::AlwaysAllows))
        }
        #[cfg(feature = "symcc")]
        TargetArg::SymccTermAlwaysDenies => {
            Box::new(target::SymccTermDrt::new(target::SymccCheck::AlwaysDenies))
        }
        #[cfg(feature = "symcc")]
        TargetArg::SymccTermNeverErrors => {
            Box::new(target::SymccTermDrt::new(target::SymccCheck::NeverErrors))
        }
    }
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Throughput(args) => cmd_throughput(args),
        Commands::Collect(args) => cmd_collect(args),
        Commands::Analyze(args) => cmd_analyze(args),
        Commands::RunAll(args) => cmd_run_all(args),
    }
}

fn cmd_throughput(args: ThroughputArgs) {
    let mut params = GeneratorParams {
        buffer_size: args.buffer_size,
        lean_size: args.lean_size,
        scoring: Some(args.strategy.clone()),
        ..Default::default()
    };

    // Single-rep mode: run one rep and write result
    if let Some(rep_id) = args.single_rep {
        let seed = args.seed_base.wrapping_add(rep_id as u64 * args.seed_stride);
        // Distinct start seed per rep -> disjoint, independent Lean corpora.
        params.start_seed = seed;
        let duration = Duration::from_secs(args.duration);
        let output_dir = PathBuf::from(&args.output_dir);

        let result = if args.guided {
            use cedar_drt_coverage::experiment::guided;
            eprintln!("Rep {}: running guided:{} for {}s (seed={})",
                rep_id, args.fuzz_target, args.duration, seed);
            guided::run_guided_throughput(
                &args.fuzz_target, duration, rep_id, seed, &output_dir, &params,
            )
        } else {
            let generator = make_generator(&args.generator, &params);
            let target = make_target(&args.target);
            eprintln!("Rep {}: running {} -> {} for {}s (seed={})",
                rep_id, generator.name(), target.name(), args.duration, seed);
            let snap_interval = Duration::from_secs(args.snapshot_interval);
            run_throughput_rep(&*generator, &*target, rep_id, seed, duration, snap_interval, &params)
        };

        eprintln!("Rep {}: {} valid from {} attempts ({:.1} valid/sec)",
            rep_id, result.valid_count, result.attempt_count, result.throughput_valid_per_sec);

        write_throughput_result(&output_dir, &result);
        return;
    }

    // Orchestrator mode: spawn R child processes
    let output_dir = PathBuf::from(&args.output_dir);
    std::fs::create_dir_all(output_dir.join("throughput")).ok();

    let exe = std::env::current_exe().expect("failed to get current exe path");
    let cores = num_cores();
    let mut children = Vec::new();

    eprintln!("Launching {} throughput reps ({} cores available, cpu_pin={})",
        args.reps, cores, args.cpu_pin);

    for rep in 0..args.reps {
        let cmd_args: Vec<String> = vec![
            "throughput".to_string(),
            "--generator".to_string(), args.generator.as_str().to_string(),
            "--target".to_string(), args.target.as_str().to_string(),
            "--duration".to_string(), args.duration.to_string(),
            "--seed-base".to_string(), args.seed_base.to_string(),
            "--seed-stride".to_string(), args.seed_stride.to_string(),
            "--output-dir".to_string(), args.output_dir.clone(),
            "--buffer-size".to_string(), args.buffer_size.to_string(),
            "--lean-size".to_string(), args.lean_size.to_string(),
            "--strategy".to_string(), args.strategy.clone(),
            "--snapshot-interval".to_string(), args.snapshot_interval.to_string(),
            "--single-rep".to_string(), rep.to_string(),
        ];

        let core = if args.cpu_pin { Some(core_for_rep(rep, cores)) } else { None };

        let child = if let Some(c) = core {
            std::process::Command::new("taskset")
                .arg("-c")
                .arg(c.to_string())
                .arg(&exe)
                .args(&cmd_args)
                .spawn()
        } else {
            std::process::Command::new(&exe)
                .args(&cmd_args)
                .spawn()
        };

        match child {
            Ok(c) => children.push((rep, c)),
            Err(e) => eprintln!("Failed to spawn rep {}: {}", rep, e),
        }
    }

    // Wait for all children
    for (rep, mut child) in children {
        match child.wait() {
            Ok(status) if status.success() => {}
            Ok(status) => eprintln!("Rep {} exited with {}", rep, status),
            Err(e) => eprintln!("Rep {} wait error: {}", rep, e),
        }
    }

    // Collect results and write summary
    let results = cedar_drt_coverage::experiment::orchestrator::collect_throughput_results(
        &output_dir, args.reps,
    );

    if results.is_empty() {
        eprintln!("No results collected!");
        return;
    }

    write_throughput_summary(&output_dir, &results);

    let throughputs: Vec<f64> = results.iter().map(|r| r.throughput_valid_per_sec).collect();
    let (mean_tp, stddev_tp) = mean_stddev(&throughputs);
    let valid_counts: Vec<f64> = results.iter().map(|r| r.valid_count as f64).collect();
    let (mean_n, _) = mean_stddev(&valid_counts);

    eprintln!("\nThroughput summary ({} reps):", results.len());
    eprintln!("  Mean throughput: {:.1} +/- {:.1} valid/sec", mean_tp, stddev_tp);
    eprintln!("  Mean valid count (N): {:.0}", mean_n);
    eprintln!("  Results written to: {}", output_dir.join("throughput").display());
}

fn cmd_collect(args: CollectArgs) {
    let mut params = GeneratorParams {
        buffer_size: args.buffer_size,
        lean_size: args.lean_size,
        scoring: Some(args.strategy.clone()),
        ..Default::default()
    };

    // Single-rep mode
    if let Some(rep_id) = args.single_rep {
        let seed = args.seed_base.wrapping_add(rep_id as u64 * args.seed_stride);
        // Distinct start seed per rep -> disjoint, independent Lean corpora.
        params.start_seed = seed;
        let output_dir = PathBuf::from(&args.output_dir);
        let rep_dir = output_dir.join(format!("collect/rep_{:02}", rep_id));
        let corpus_dir = rep_dir.join("corpus");

        if args.guided {
            use cedar_drt_coverage::experiment::guided;
            // Count-signal mode: match the throughput probe's FINAL valid count. Poll
            // throughput/rep_NN.json (the ThroughputResult, written ONCE when the probe
            // completes) — NOT _fuzz_stats_rep_NN.json, which the fuzz target rewrites
            // periodically and would be read mid-run with an early valid_count of 0.
            let target_stats_path = if args.guided_match_throughput {
                Some(output_dir.join(format!("throughput/rep_{:02}.json", rep_id)))
            } else {
                None
            };
            // -runs count when neither signal nor time bound is set (legacy behavior).
            let total_runs = if args.guided_match_throughput || args.guided_max_secs.is_some() {
                0
            } else {
                args.valid_count
            };
            eprintln!(
                "Rep {}: guided collection (match_throughput={}, max_secs={:?}, runs={}) seed={}",
                rep_id, args.guided_match_throughput, args.guided_max_secs, total_runs, seed
            );

            let count = {
                #[cfg(feature = "s3")]
                {
                    if let Some(ref bucket) = args.s3_bucket {
                        let prefix = args.s3_prefix.clone().unwrap_or_default();
                        let rep_prefix = format!("{}/rep_{:02}/corpus", prefix, rep_id);
                        let mut uploader = cedar_drt_coverage::experiment::s3::BatchUploader::new(
                            bucket.clone(), rep_prefix, 1000,
                        );
                        guided::run_guided_collection_with_drain(
                            &args.fuzz_target, total_runs, args.guided_max_secs,
                            target_stats_path, rep_id, seed,
                            &corpus_dir, &output_dir,
                            move |_name, bytes| {
                                uploader.push(bytes.to_vec());
                            },
                        )
                    } else {
                        guided::run_guided_collection(
                            &args.fuzz_target, total_runs, args.guided_max_secs,
                            target_stats_path, rep_id, seed,
                            &corpus_dir, &output_dir,
                        )
                    }
                }
                #[cfg(not(feature = "s3"))]
                {
                    guided::run_guided_collection(
                        &args.fuzz_target, total_runs, args.guided_max_secs,
                        target_stats_path, rep_id, seed,
                        &corpus_dir, &output_dir,
                    )
                }
            };

            eprintln!("Rep {}: done. {} valid inputs collected", rep_id, count);
            return;
        }

        let generator = make_generator(&args.generator, &params);
        let target = make_target(&args.target);

        eprintln!("Rep {}: collecting {} valid inputs (seed={})",
            rep_id, args.valid_count, seed);

        let snapshot_interval = Some(Duration::from_secs(args.snapshot_interval));

        // Stop the rep at the first DRT mismatch, or keep going (default) to
        // collect coverage data + find more bugs. `ON_VIOLATION=stop` to halt.
        let stop_on_violation = std::env::var("ON_VIOLATION")
            .map(|v| v.eq_ignore_ascii_case("stop"))
            .unwrap_or(false);

        #[cfg(feature = "s3")]
        let mut s3_uploader = args.s3_bucket.as_ref().map(|bucket| {
            let prefix = args.s3_prefix.clone().unwrap_or_default();
            let rep_prefix = format!("{}/rep_{:02}/corpus", prefix, rep_id);
            cedar_drt_coverage::experiment::s3::BatchUploader::new(
                bucket.clone(), rep_prefix, 1000,
            )
        });

        // Violations are streamed to S3 immediately (one object each) so an
        // interrupted / self-terminating instance never loses a bug repro.
        #[cfg(feature = "s3")]
        let viol_uploader = args.s3_bucket.as_ref().map(|bucket| {
            let prefix = args.s3_prefix.clone().unwrap_or_default();
            cedar_drt_coverage::experiment::s3::StreamingUploader::new(
                bucket.clone(),
                format!("{}/rep_{:02}/violations", prefix, rep_id),
            )
        });

        // Skip per-input local file writes when streaming to S3 (avoids the
        // hundreds-of-thousands-of-tiny-files bottleneck for large N).
        #[cfg(feature = "s3")]
        let write_local = args.s3_bucket.is_none();
        #[cfg(not(feature = "s3"))]
        let write_local = true;

        let violations_dir = rep_dir.join("violations");

        let result = run_collection_session(
            &*generator, &*target, seed, args.valid_count,
            snapshot_interval, &corpus_dir, write_local, stop_on_violation,
            |attempts, valid| {
                if attempts % 10000 == 0 {
                    eprintln!("  Rep {}: {} valid / {} attempts", rep_id, valid, attempts);
                }
            },
            |_filename, _bytes| {
                #[cfg(feature = "s3")]
                if let Some(ref mut uploader) = s3_uploader {
                    uploader.push(_bytes.to_vec());
                }
            },
            |index, message, input| {
                // Capture a reproducible repro: proto (round-trippable) + Cedar
                // text + generation provenance (the real seed, not the loop counter).
                use cedar_policy::proto::traits::Protobuf;
                let prov = input.provenance.as_ref();
                let repro = serde_json::json!({
                    "index": index,
                    "message": message,
                    "target": args.target.as_str(),
                    "base_seed": prov.map(|p| p.base_seed),
                    "prov_index": prov.map(|p| p.index),
                    "size": prov.map(|p| p.size),
                    "schema_size": prov.map(|p| p.schema_size),
                    "strategy": prov.map(|p| p.strategy.clone()),
                    "policies_cedar": input.policies.to_string(),
                });
                let json = serde_json::to_vec_pretty(&repro).unwrap_or_default();
                let sbytes = input.schema.encode();
                let pbytes = input.policies.encode();
                std::fs::create_dir_all(&violations_dir).ok();
                std::fs::write(violations_dir.join(format!("viol_{:04}.json", index)), &json).ok();
                std::fs::write(violations_dir.join(format!("viol_{:04}.schema.bin", index)), &sbytes).ok();
                std::fs::write(violations_dir.join(format!("viol_{:04}.policies.bin", index)), &pbytes).ok();
                #[cfg(feature = "s3")]
                if let Some(ref u) = viol_uploader {
                    u.put(format!("viol_{:04}.json", index), json.clone());
                    u.put(format!("viol_{:04}.schema.bin", index), sbytes.clone());
                    u.put(format!("viol_{:04}.policies.bin", index), pbytes.clone());
                }
                eprintln!("  Rep {}: DRT VIOLATION #{} captured (base_seed={:?})",
                    rep_id, index, prov.map(|p| p.base_seed));
            },
        );

        #[cfg(feature = "s3")]
        if let Some(uploader) = s3_uploader {
            let (batches, inputs) = uploader.finish();
            eprintln!("  Rep {}: uploaded {} batches ({} inputs) to S3", rep_id, batches, inputs);
        }
        #[cfg(feature = "s3")]
        if let Some(u) = viol_uploader {
            let n = u.finish();
            if n > 0 { eprintln!("  Rep {}: uploaded {} violation objects to S3", rep_id, n); }
        }

        // Write the inline analysis result (no replay needed) — UNLESS stream-only, where
        // collect skips the per-input analysis and the parallel replay-analyze produces
        // analyze/rep_NN.json instead (writing the empty inline result here would just be
        // overwritten).
        if std::env::var("COLLECT_STREAM_ONLY").is_err() {
            let analyze_dir = output_dir.join("analyze");
            std::fs::create_dir_all(&analyze_dir).ok();
            std::fs::write(
                analyze_dir.join(format!("rep_{:02}.json", rep_id)),
                serde_json::to_string_pretty(&result.analyze).unwrap(),
            ).ok();
        }

        // Write metadata
        let metadata = serde_json::json!({
            "rep_id": rep_id,
            "generator": generator.name(),
            "target": target.name(),
            "seed": seed,
            "valid_count": result.stats.valid,
            "attempt_count": result.stats.attempts,
            "elapsed_secs": result.stats.elapsed_secs,
            "inputs_saved": result.inputs_saved,
            "violations": result.violation_count,
        });
        std::fs::write(
            rep_dir.join("metadata.json"),
            serde_json::to_string_pretty(&metadata).unwrap(),
        ).ok();

        // Write edge snapshots
        if !result.stats.snapshots.is_empty() {
            let json = serde_json::to_string_pretty(&result.stats.snapshots).unwrap();
            std::fs::write(rep_dir.join("edge_snapshots.json"), json).ok();
        }

        eprintln!("Rep {}: done. {} valid from {} attempts in {:.1}s ({} violations)",
            rep_id, result.stats.valid, result.stats.attempts, result.stats.elapsed_secs,
            result.violation_count);
        return;
    }

    // Orchestrator mode
    let output_dir = PathBuf::from(&args.output_dir);
    let exe = std::env::current_exe().expect("failed to get current exe path");
    let cores = num_cores();
    let mut children = Vec::new();

    eprintln!("Launching {} collection reps (target: {} valid inputs each)",
        args.reps, args.valid_count);

    for rep in 0..args.reps {
        let cmd_args: Vec<String> = vec![
            "collect".to_string(),
            "--generator".to_string(), args.generator.as_str().to_string(),
            "--target".to_string(), args.target.as_str().to_string(),
            "--valid-count".to_string(), args.valid_count.to_string(),
            "--seed-base".to_string(), args.seed_base.to_string(),
            "--seed-stride".to_string(), args.seed_stride.to_string(),
            "--output-dir".to_string(), args.output_dir.clone(),
            "--buffer-size".to_string(), args.buffer_size.to_string(),
            "--lean-size".to_string(), args.lean_size.to_string(),
            "--strategy".to_string(), args.strategy.clone(),
            "--snapshot-interval".to_string(), args.snapshot_interval.to_string(),
            "--single-rep".to_string(), rep.to_string(),
        ];

        let core = if args.cpu_pin { Some(core_for_rep(rep, cores)) } else { None };

        let child = if let Some(c) = core {
            std::process::Command::new("taskset")
                .arg("-c")
                .arg(c.to_string())
                .arg(&exe)
                .args(&cmd_args)
                .spawn()
        } else {
            std::process::Command::new(&exe)
                .args(&cmd_args)
                .spawn()
        };

        match child {
            Ok(c) => children.push((rep, c)),
            Err(e) => eprintln!("Failed to spawn rep {}: {}", rep, e),
        }
    }

    for (rep, mut child) in children {
        match child.wait() {
            Ok(status) if status.success() => {}
            Ok(status) => eprintln!("Rep {} exited with {}", rep, status),
            Err(e) => eprintln!("Rep {} wait error: {}", rep, e),
        }
    }

    eprintln!("Collection complete. Results in: {}", output_dir.join("collect").display());
}

fn cmd_analyze(args: AnalyzeArgs) {
    use cedar_drt_coverage::experiment::analyze;

    let output_dir = PathBuf::from(&args.output_dir);
    let analyze_dir = output_dir.join("analyze");
    std::fs::create_dir_all(&analyze_dir).ok();

    let mut all_results = Vec::new();

    // S3 source: stream corpus directly from S3
    #[cfg(feature = "s3")]
    if let (Some(bucket), Some(prefix)) = (&args.s3_bucket, &args.s3_prefix) {
        let rt = tokio::runtime::Runtime::new().unwrap();
        for rep in 0..args.reps {
            let rep_prefix = format!("{}/rep_{:02}/corpus", prefix, rep);
            eprintln!("Analyzing rep {} from s3://{}/{}...", rep, bucket, rep_prefix);

            let result = rt.block_on(async {
                let client = cedar_drt_coverage::experiment::s3::make_client().await;
                analyze::replay_and_analyze_from_s3(&client, bucket, &rep_prefix, &args.format).await
            });

            let result_path = analyze_dir.join(format!("rep_{:02}.json", rep));
            let json = serde_json::to_string_pretty(&result).unwrap();
            std::fs::write(&result_path, &json).unwrap();
            eprintln!("  corpus_size={} unique={} mean_nodes={:.1} 3-paths={}",
                result.corpus_size, result.unique_inputs, result.mean_node_count,
                result.cumulative_3paths);

            all_results.push(result);
        }
    } else {
        // Local source
        for rep in 0..args.reps {
            let rep_dir = output_dir.join(format!("collect/rep_{:02}", rep));
            if !rep_dir.exists() {
                eprintln!("Warning: {} does not exist, skipping", rep_dir.display());
                continue;
            }

            eprintln!("Analyzing rep {}...", rep);
            let result = if args.format == "jsonl" {
                analyze::analyze_collection_dir(&rep_dir)
            } else {
                analyze::replay_and_analyze(&rep_dir, &args.format)
            };

            let result_path = analyze_dir.join(format!("rep_{:02}.json", rep));
            let json = serde_json::to_string_pretty(&result).unwrap();
            std::fs::write(&result_path, &json).unwrap();
            eprintln!("  corpus_size={} unique={} mean_nodes={:.1} 3-paths={}",
                result.corpus_size, result.unique_inputs, result.mean_node_count,
                result.cumulative_3paths);

            all_results.push(result);
        }
    }

    #[cfg(not(feature = "s3"))]
    {
        for rep in 0..args.reps {
            let rep_dir = output_dir.join(format!("collect/rep_{:02}", rep));
            if !rep_dir.exists() {
                eprintln!("Warning: {} does not exist, skipping", rep_dir.display());
                continue;
            }

            eprintln!("Analyzing rep {}...", rep);
            let result = if args.format == "jsonl" {
                analyze::analyze_collection_dir(&rep_dir)
            } else {
                analyze::replay_and_analyze(&rep_dir, &args.format)
            };

            let result_path = analyze_dir.join(format!("rep_{:02}.json", rep));
            let json = serde_json::to_string_pretty(&result).unwrap();
            std::fs::write(&result_path, &json).unwrap();
            eprintln!("  corpus_size={} unique={} mean_nodes={:.1} 3-paths={}",
                result.corpus_size, result.unique_inputs, result.mean_node_count,
                result.cumulative_3paths);

            all_results.push(result);
        }
    }

    if all_results.is_empty() {
        eprintln!("No results to summarize.");
        return;
    }

    // Aggregate summary
    let n = all_results.len() as f64;
    let mean_corpus: f64 = all_results.iter().map(|r| r.corpus_size as f64).sum::<f64>() / n;
    let mean_unique: f64 = all_results.iter().map(|r| r.unique_inputs as f64).sum::<f64>() / n;
    let mean_nodes: f64 = all_results.iter().map(|r| r.mean_node_count).sum::<f64>() / n;
    let mean_2paths: f64 = all_results.iter().map(|r| r.cumulative_2paths as f64).sum::<f64>() / n;
    let mean_3paths: f64 = all_results.iter().map(|r| r.cumulative_3paths as f64).sum::<f64>() / n;

    let summary = serde_json::json!({
        "reps": all_results.len(),
        "mean_corpus_size": mean_corpus,
        "mean_unique_inputs": mean_unique,
        "mean_node_count": mean_nodes,
        "mean_2paths": mean_2paths,
        "mean_3paths": mean_3paths,
        "per_rep": all_results,
    });

    let summary_path = analyze_dir.join("summary.json");
    let json = serde_json::to_string_pretty(&summary).unwrap();
    std::fs::write(&summary_path, &json).unwrap();
    eprintln!("\nSummary written to {}", summary_path.display());
    eprintln!("  mean_corpus={:.0} mean_unique={:.0} mean_nodes={:.1} mean_3paths={:.0}",
        mean_corpus, mean_unique, mean_nodes, mean_3paths);

    // S3 result upload
    #[cfg(feature = "s3")]
    {
        if let (Some(bucket), Some(prefix)) = (&args.s3_upload_bucket, &args.s3_upload_prefix) {
            eprintln!("Uploading analyze results to s3://{}/{}/", bucket, prefix);
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async {
                let client = cedar_drt_coverage::experiment::s3::make_client().await;
                cedar_drt_coverage::experiment::s3::upload_directory(
                    &client, bucket, prefix, &analyze_dir,
                ).await.unwrap();
            });
            eprintln!("Upload complete.");
        }
    }
}

fn cmd_run_all(args: RunAllArgs) {
    eprintln!("=== Phase 1: Throughput ===");
    let tp_args = ThroughputArgs {
        generator: args.generator.clone(),
        target: args.target.clone(),
        guided: false,
        fuzz_target: "validation-drt-type-directed".to_string(),
        duration: args.duration,
        reps: args.reps,
        seed_base: args.seed_base,
        seed_stride: args.seed_stride,
        output_dir: args.output_dir.clone(),
        cpu_pin: args.cpu_pin,
        buffer_size: args.buffer_size,
        lean_size: args.lean_size,
        strategy: args.strategy.clone(),
        snapshot_interval: 1,
        single_rep: None,
    };
    cmd_throughput(tp_args);

    // Read summary to get mean N
    let output_dir = PathBuf::from(&args.output_dir);
    let summary_path = output_dir.join("throughput/summary.json");
    let mean_n = if let Ok(data) = std::fs::read_to_string(&summary_path) {
        if let Ok(summary) = serde_json::from_str::<serde_json::Value>(&data) {
            summary["mean_valid_count"].as_f64().unwrap_or(1000.0) as u64
        } else {
            1000
        }
    } else {
        eprintln!("Warning: could not read throughput summary, using N=1000");
        1000
    };

    eprintln!("\n=== Phase 2: Collection (N={}) ===", mean_n);
    let collect_args = CollectArgs {
        generator: args.generator.clone(),
        target: args.target.clone(),
        guided: false,
        fuzz_target: "validation-drt-type-directed".to_string(),
        guided_match_throughput: false,
        guided_max_secs: None,
        valid_count: mean_n,
        reps: args.reps,
        seed_base: args.seed_base,
        seed_stride: args.seed_stride,
        output_dir: args.output_dir.clone(),
        cpu_pin: args.cpu_pin,
        buffer_size: args.buffer_size,
        lean_size: args.lean_size,
        strategy: args.strategy.clone(),
        snapshot_interval: 10,
        single_rep: None,
        #[cfg(feature = "s3")]
        s3_bucket: None,
        #[cfg(feature = "s3")]
        s3_prefix: None,
    };
    cmd_collect(collect_args);

    eprintln!("\n=== Done ===");
    eprintln!("Results in: {}", args.output_dir);
}

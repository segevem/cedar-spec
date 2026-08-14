pub mod hll;
use std::time::{Duration, Instant};

use cedar_policy::{PolicySet, Schema, ValidationMode, Validator};

pub mod generators;
pub mod kpath;
pub mod edge_tracker;
pub mod target;
pub mod experiment;
#[cfg(feature = "profraw")]
pub mod source_cov_tracker;
#[cfg(feature = "lean-gen")]
pub mod lean_gen;
#[cfg(feature = "lean-gen")]
pub mod timeout_ffi;

pub use target::{Target, TargetResult};

/// llvm-cov `--ignore-filename-regex` for measuring *input-driven validator*
/// line coverage. Excludes the test harness and anything not exercised by the
/// inputs themselves, so the number reflects what the generated schemas/policies
/// drive through the typechecker — NOT the harness's protobuf decode or
/// `ValidatorSchema::try_from`/`compute_tc` construction.
///
/// Excludes (in order): rust stdlib + cargo deps; protobuf decode
/// (`cedar-policy/src/proto*`); `ValidatorSchema` construction (`validator/schema.rs`
/// and `validator/schema/*` — note this is a *mixed* file, so its accessor
/// coverage is dropped too, but consistently for every approach); the schema-text
/// parser / JSON / deprecated-compat (not input-driven); all test modules; and the
/// generation/DRT harness crates. Keeps `validator/typecheck*`, `types*`, `rbac`,
/// `str_checks`, `extensions*`, `diagnostics*`, and the core AST the typechecker
/// traverses. Tunable — kept in sync with `experiment_scripts/coverage_analyze.py`.
pub const COVERAGE_IGNORE_REGEX: &str = concat!(
    r"/\.cargo/registry|/rustc/",
    r"|/proto\.rs|/proto/",
    r"|/validator/schema\.rs|/validator/schema/",
    r"|/validator/cedar_schema|/validator/json_schema\.rs|/validator/deprecated_schema",
    r"|/tests/|/test/|_test\.rs|/test\.rs|test_579",
    // Harness crates + the in-process analysis that runs during a *fused* collect
    // (k-path/skeleton hashing etc.). `cedar-drt` already substring-matches
    // `cedar-drt/coverage`, but `kpath` is called out explicitly for clarity.
    r"|/kpath|cedar-policy-generators|cedar-drt|cedar-lean-ffi|cedar-policy-symcc",
);

#[cfg(feature = "profraw")]
pub mod profraw {
    use std::process::Command;
    use std::ffi::CString;

    extern "C" {
        pub fn __llvm_profile_write_file() -> i32;
        pub fn __llvm_profile_set_filename(name: *const std::os::raw::c_char);
    }

    /// Point the profiling runtime at `path` and flush the current (cumulative)
    /// counters to it. Used to take `.profraw` snapshots during a replay so the
    /// analysis can derive line coverage *over time*.
    pub fn dump_profraw_to(path: &str) {
        if let Ok(cpath) = CString::new(path) {
            unsafe {
                __llvm_profile_set_filename(cpath.as_ptr());
                __llvm_profile_write_file();
            }
        }
    }

    pub fn get_current_coverage() -> Option<u64> {
        unsafe { __llvm_profile_write_file(); }

        let profraw = std::env::var("LLVM_PROFILE_FILE").ok()?;
        let sysroot = String::from_utf8(
            Command::new("rustc").arg("--print").arg("sysroot").output().ok()?.stdout
        ).ok()?;
        let sysroot = sysroot.trim();

        let profdata_bin = find_llvm_tool(sysroot, "llvm-profdata")?;
        let cov_bin = find_llvm_tool(sysroot, "llvm-cov")?;

        let exe = std::env::current_exe().ok()?;
        let profdata_path = format!("{}.profdata", profraw);

        let status = Command::new(&profdata_bin)
            .args(["merge", "-sparse", &profraw, "-o", &profdata_path])
            .output().ok()?;
        if !status.status.success() { return None; }

        let output = Command::new(&cov_bin)
            .args(["export", exe.to_str()?, &format!("-instr-profile={profdata_path}"),
                   "-format=text",
                   &format!("--ignore-filename-regex={}", super::COVERAGE_IGNORE_REGEX),
                   "-summary-only"])
            .output().ok()?;
        if !output.status.success() { return None; }

        let json: serde_json::Value = serde_json::from_slice(&output.stdout).ok()?;
        json["data"][0]["totals"]["lines"]["covered"].as_u64()
    }

    fn find_llvm_tool(sysroot: &str, name: &str) -> Option<String> {
        let output = Command::new("find")
            .args([sysroot, "-name", name])
            .output().ok()?;
        let paths = String::from_utf8(output.stdout).ok()?;
        paths.lines().next().map(|s| s.to_string())
    }
}

#[cfg(feature = "profraw")]
pub use profraw::get_current_coverage;

/// Reproduction coordinates for a generated input. For the Lean schema
/// generator (whose per-input seed lives inside a batch, not in the collect
/// loop), this is what makes a single input regenerable and lets violation
/// repros / per-input metadata reference the real seed rather than the
/// meaningless attempt counter.
#[derive(Clone, Debug, serde::Serialize)]
pub struct GenProvenance {
    /// Base seed handed to the FFI for the batch this input came from.
    pub base_seed: u64,
    /// Index of this input within its batch.
    pub index: usize,
    pub size: u32,
    pub schema_size: u32,
    pub strategy: String,
}

/// The input to the validation coverage harness.
pub struct ValidationInput {
    pub schema: Schema,
    pub policies: PolicySet,
    /// Raw bytes for corpus saving (protobuf-encoded for Lean generators,
    /// None for Rust generators that don't have a serialized form).
    pub raw_bytes: Option<Vec<u8>>,
    /// Generation coordinates for reproducing this exact input. `None` for
    /// generators whose `raw_bytes` already reproduce it (the ABAC PRNG buffer).
    pub provenance: Option<GenProvenance>,
}

/// Trait for generators that produce validation inputs from a seed.
/// Implement this for each generator you want to compare.
pub trait ValidationGenerator {
    fn name(&self) -> &str;
    fn generate(&self, seed: u64) -> Option<ValidationInput>;
}

/// Run the Rust validator on a single input.
pub fn run_validation(input: &ValidationInput) {
    let validator = Validator::new(input.schema.clone());
    let _result = validator.validate(&input.policies, ValidationMode::Strict);
}

pub struct SessionStats {
    pub valid: u64,
    pub attempts: u64,
    pub elapsed_secs: f64,
    pub total_nodes: u64,
    pub kpath2_count: usize,
    pub kpath3_count: usize,
    pub top_constructor_counts: std::collections::HashMap<&'static str, u64>,
    pub novel_inputs: u64,
    pub total_features: usize,
    pub snapshots: Vec<EdgeSnapshot>,
    pub violations: Vec<ViolationRecord>,
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct ViolationRecord {
    pub seed: u64,
    pub message: String,
    /// The raw bytes that reproduce this input. For Rust generators this is
    /// the PRNG buffer (same format as libfuzzer corpus files). For Lean
    /// generators this is the protobuf-encoded output.
    #[serde(skip)]
    pub raw_bytes: Option<Vec<u8>>,
}

#[derive(Clone, serde::Serialize)]
pub struct EdgeSnapshot {
    pub elapsed_secs: f64,
    pub attempts: u64,
    pub valid: u64,
    pub novel_inputs: u64,
    pub total_features: usize,
}

/// Run the generator until either `max_attempts` is reached or `duration` elapses
/// (whichever comes first). If duration is None, only the attempt limit applies.
/// Tracks k-path coverage and input size stats.
/// If sancov edge counters are active, also tracks novel inputs (corpus-equivalent).
///
/// The `target` parameter controls what happens with each generated input.
/// Use `target::RustValidation` for the old behavior (Rust-only validation).
pub fn run_coverage_session(
    generator: &dyn ValidationGenerator,
    target: &dyn Target,
    start_seed: u64,
    max_attempts: u64,
    duration: Option<Duration>,
    snapshot_interval: Option<Duration>,
    corpus_dir: Option<std::path::PathBuf>,
    mut on_attempt: impl FnMut(u64, u64), // (attempt_number, valid_so_far)
) -> SessionStats {
    use std::collections::{HashMap, HashSet};

    let start = Instant::now();
    let mut valid = 0u64;
    let mut attempts = 0u64;
    // Same reject gate as the collect loop + the validation-welltyped-drt Corpus::Reject:
    // when set, the throughput RATE (and hence the derived N) counts WELL-TYPED inputs only.
    let welltyped_only = std::env::var("COLLECT_WELLTYPED_ONLY").is_ok();
    let mut total_nodes = 0u64;
    let mut all_2paths: HashSet<kpath::KPath> = HashSet::new();
    let mut all_3paths: HashSet<kpath::KPath> = HashSet::new();
    let mut top_constructors: HashMap<&'static str, u64> = HashMap::new();
    let tracking_active = edge_tracker::is_initialized();
    let mut tracker = edge_tracker::EdgeTracker::new(corpus_dir, 1000);
    let mut snapshots: Vec<EdgeSnapshot> = Vec::new();
    let mut violations: Vec<ViolationRecord> = Vec::new();
    let mut next_snapshot = snapshot_interval.unwrap_or(Duration::from_secs(u64::MAX));

    loop {
        if attempts >= max_attempts {
            break;
        }
        if let Some(dur) = duration {
            if start.elapsed() >= dur {
                break;
            }
        }

        if tracking_active && snapshot_interval.is_some() && start.elapsed() >= next_snapshot {
            snapshots.push(EdgeSnapshot {
                elapsed_secs: start.elapsed().as_secs_f64(),
                attempts,
                valid,
                novel_inputs: tracker.novel_count,
                total_features: tracker.total_features(),
            });
            next_snapshot += snapshot_interval.unwrap();
        }

        let seed = start_seed.wrapping_add(attempts);
        if let Some(input) = generator.generate(seed) {
            // Reject ill-typed inputs so the measured throughput rate (and derived N)
            // reflects WELL-TYPED generation only — same predicate as the collect gate.
            if welltyped_only && !crate::target::is_well_typed(&input.schema, &input.policies) {
                attempts += 1;
                on_attempt(attempts, valid);
                continue;
            }
            let stats3 = kpath::analyze_policy_set(&input.policies, 3);
            let stats2 = kpath::analyze_policy_set(&input.policies, 2);
            total_nodes += stats3.node_count as u64;
            all_3paths.extend(stats3.kpaths);
            all_2paths.extend(stats2.kpaths);
            for ctor in stats3.top_constructors {
                *top_constructors.entry(ctor).or_insert(0) += 1;
            }
            if tracking_active {
                tracker.run_tracked(|| { target.run(&input); }, input.raw_bytes.as_deref());
            } else {
                let result = target.run(&input);
                if let TargetResult::Violation(ref msg) = result {
                    violations.push(ViolationRecord {
                        seed,
                        message: msg.clone(),
                        raw_bytes: input.raw_bytes.clone(),
                    });
                }
            }
            valid += 1;
        }
        attempts += 1;
        on_attempt(attempts, valid);
    }

    // Final snapshot
    if tracking_active && snapshot_interval.is_some() {
        snapshots.push(EdgeSnapshot {
            elapsed_secs: start.elapsed().as_secs_f64(),
            attempts,
            valid,
            novel_inputs: tracker.novel_count,
            total_features: tracker.total_features(),
        });
    }

    SessionStats {
        valid,
        attempts,
        elapsed_secs: start.elapsed().as_secs_f64(),
        total_nodes,
        kpath2_count: all_2paths.len(),
        kpath3_count: all_3paths.len(),
        top_constructor_counts: top_constructors,
        novel_inputs: tracker.novel_count,
        total_features: tracker.total_features(),
        snapshots,
        violations,
    }
}

/// Run the adaptive generator with periodic coverage checks and weight updates.
pub fn run_adaptive_session(
    generator: &mut generators::AdaptiveGenerator,
    target: &dyn Target,
    start_seed: u64,
    max_attempts: u64,
    duration: Option<Duration>,
    mut on_attempt: impl FnMut(u64, u64),
) -> SessionStats {
    let start = Instant::now();
    let mut valid = 0u64;
    let mut attempts = 0u64;
    let mut violations: Vec<ViolationRecord> = Vec::new();

    #[cfg(feature = "profraw")]
    { generator.last_coverage = get_current_coverage().unwrap_or(0); }
    #[cfg(not(feature = "profraw"))]
    { generator.last_coverage = 0; }

    loop {
        if attempts >= max_attempts {
            break;
        }
        if let Some(dur) = duration {
            if start.elapsed() >= dur {
                break;
            }
        }
        let seed = start_seed.wrapping_add(attempts);
        let config_idx = {
            let config = generator.pick_config(seed);
            generator.configs.iter().position(|c| std::ptr::eq(c, config)).unwrap_or(0)
        };

        if let Some(input) = generator.generate(seed) {
            let result = target.run(&input);
            if let TargetResult::Violation(ref msg) = result {
                violations.push(ViolationRecord {
                    seed,
                    message: msg.clone(),
                    raw_bytes: input.raw_bytes.clone(),
                });
            }
            valid += 1;
            generator.configs[config_idx].hits += 1;
        }
        attempts += 1;
        on_attempt(attempts, valid);

        if attempts % generator.check_interval == 0 {
            generator.update_weights();
        }
    }
    SessionStats {
        valid,
        attempts,
        elapsed_secs: start.elapsed().as_secs_f64(),
        total_nodes: 0,
        kpath2_count: 0,
        kpath3_count: 0,
        top_constructor_counts: std::collections::HashMap::new(),
        novel_inputs: 0,
        total_features: 0,
        snapshots: Vec::new(),
        violations,
    }
}

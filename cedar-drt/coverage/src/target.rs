use std::fmt;
#[cfg(any(feature = "lean-gen", feature = "symcc"))]
use std::panic::{self, AssertUnwindSafe};

use cedar_policy::{PolicySet, Schema, ValidationMode, Validator};

use crate::ValidationInput;

/// Outcome of running a target on one input.
#[derive(Debug)]
pub enum TargetResult {
    /// Target executed without issue.
    Ok,
    /// Target detected a violation (DRT mismatch, assertion failure).
    /// Contains the panic message for logging/debugging.
    Violation(String),
    /// Input was skipped (e.g., schema conversion failed, compilation failed).
    Skipped,
}

impl TargetResult {
    pub fn is_violation(&self) -> bool {
        matches!(self, Self::Violation(_))
    }
}

impl fmt::Display for TargetResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ok => write!(f, "ok"),
            Self::Violation(msg) => write!(f, "VIOLATION: {msg}"),
            Self::Skipped => write!(f, "skipped"),
        }
    }
}

/// Runs a closure that may panic (e.g., DRT assertion), capturing the panic
/// as a `Violation` and returning `Ok` on success.
#[cfg(any(feature = "lean-gen", feature = "symcc"))]
fn catch_violation(f: impl FnOnce()) -> TargetResult {
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(()) => TargetResult::Ok,
        Err(payload) => {
            let msg = if let Some(s) = payload.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown panic".to_string()
            };
            TargetResult::Violation(msg)
        }
    }
}

/// Well-typedness predicate SHARED with the `validation-welltyped-drt` fuzz target's
/// `Corpus::Reject` gate (`cedar_drt_inner::validation_drt::is_well_typed`): an input is
/// "well-typed" iff the Rust strict validator accepts it with **no errors**. Kept
/// identical on both sides so the guided fuzzer and the experiment collect reject
/// exactly the same inputs — "if the corpus would reject it, we reject it too."
pub fn is_well_typed(schema: &Schema, policies: &PolicySet) -> bool {
    Validator::new(schema.clone())
        .validate(policies, ValidationMode::Strict)
        .validation_passed()
}

/// What to do with a generated (Schema, PolicySet) — the "test oracle."
/// Separates generation from execution so any generator can target any oracle.
pub trait Target: Sync {
    fn name(&self) -> &str;
    fn run(&self, input: &ValidationInput) -> TargetResult;
}

/// Just runs the Rust validator. No differential comparison. Never panics.
pub struct RustValidation;

impl Target for RustValidation {
    fn name(&self) -> &str {
        "rust-only"
    }

    fn run(&self, input: &ValidationInput) -> TargetResult {
        let validator = Validator::new(input.schema.clone());
        let _result = validator.validate(&input.policies, ValidationMode::Strict);
        TargetResult::Ok
    }
}

/// Differential test: runs both Rust and Lean validators, panics on disagreement.
/// This is exactly what the `validation-drt` fuzz target does.
#[cfg(feature = "lean-gen")]
pub struct ValidationDrt {
    ffi: cedar_lean_ffi::CedarLeanFfi,
}

#[cfg(feature = "lean-gen")]
impl ValidationDrt {
    pub fn new() -> Self {
        Self {
            ffi: cedar_lean_ffi::CedarLeanFfi::new(),
        }
    }
}

#[cfg(feature = "lean-gen")]
impl Target for ValidationDrt {
    fn name(&self) -> &str {
        "validation-drt"
    }

    fn run(&self, input: &ValidationInput) -> TargetResult {
        let ffi = &self.ffi;
        let schema = input.schema.clone();
        let policies = &input.policies;
        // Non-panicking compare: a mismatch is returned as data (captured +
        // continue), not a panic. Panic unwinding is unreliable here — a
        // Lean-object Drop during unwind double-faults ("failed to initiate
        // panic"), aborting the whole run on the first mismatch.
        match cedar_drt::tests::run_val_test_checked(ffi, schema, policies, ValidationMode::Strict) {
            Ok(()) => TargetResult::Ok,
            Err(msg) => TargetResult::Violation(msg),
        }
    }
}

/// Differential test with level-based validation.
/// This is exactly what the `level-validation-drt` fuzz target does.
/// The level is derived per-input from the raw bytes, just as the real
/// fuzz target derives it from the `Unstructured` buffer.
#[cfg(feature = "lean-gen")]
pub struct LevelValidationDrt {
    ffi: cedar_lean_ffi::CedarLeanFfi,
    max_depth: usize,
}

#[cfg(feature = "lean-gen")]
impl LevelValidationDrt {
    pub fn new(max_depth: usize) -> Self {
        Self {
            ffi: cedar_lean_ffi::CedarLeanFfi::new(),
            max_depth,
        }
    }

    fn level_for_input(&self, input: &ValidationInput) -> i32 {
        let byte = input
            .raw_bytes
            .as_ref()
            .and_then(|b| b.last().copied())
            .unwrap_or(0);
        (byte as usize % (self.max_depth + 2)) as i32
    }
}

#[cfg(feature = "lean-gen")]
impl Target for LevelValidationDrt {
    fn name(&self) -> &str {
        "level-validation-drt"
    }

    fn run(&self, input: &ValidationInput) -> TargetResult {
        let ffi = &self.ffi;
        let schema = input.schema.clone();
        let policies = &input.policies;
        let level = self.level_for_input(input);
        catch_violation(|| {
            cedar_drt::tests::run_level_val_test(
                ffi,
                schema,
                policies,
                ValidationMode::Strict,
                level,
            );
        })
    }
}

/// SymCC term DRT: compares SMT asserts produced by Rust and Lean for a given check.
/// Iterates over all request environments in the schema.
#[cfg(feature = "symcc")]
pub struct SymccTermDrt {
    ffi: cedar_lean_ffi::CedarLeanFfi,
    check: SymccCheck,
}

/// Which SymCC property to check (single policy set).
#[cfg(feature = "symcc")]
#[derive(Clone, Copy)]
pub enum SymccCheck {
    AlwaysAllows,
    AlwaysDenies,
    NeverErrors,
}

#[cfg(feature = "symcc")]
impl SymccTermDrt {
    pub fn new(check: SymccCheck) -> Self {
        Self {
            ffi: cedar_lean_ffi::CedarLeanFfi::new(),
            check,
        }
    }
}

#[cfg(feature = "symcc")]
impl Target for SymccTermDrt {
    fn name(&self) -> &str {
        match self.check {
            SymccCheck::AlwaysAllows => "symcc-term-always-allows",
            SymccCheck::AlwaysDenies => "symcc-term-always-denies",
            SymccCheck::NeverErrors => "symcc-term-never-errors",
        }
    }

    fn run(&self, input: &ValidationInput) -> TargetResult {
        use cedar_drt_inner::symcc::asserts_match_result;
        use cedar_policy_symcc::{
            CompiledPolicy, CompiledPolicySet, always_allows_asserts, always_denies_asserts,
            never_errors_asserts,
        };

        let lean_schema = match self.ffi.load_lean_schema_object(&input.schema) {
            Ok(s) => s,
            Err(_) => return TargetResult::Skipped,
        };

        let ffi = &self.ffi;
        let schema = &input.schema;
        let policies = &input.policies;
        let check = self.check;

        // COLLECT-AND-CONTINUE (symcc must be kind to crashes): instead of `.unwrap()`/`assert`
        // (which under `panic=abort` hard-crash the whole rep — `catch_violation` can't catch an
        // abort), record each Lean-compile error and each Rust-vs-Lean term mismatch as a
        // violation string and keep going over the remaining (req_env, policy) pairs. `run`
        // returns one `Violation` aggregating them (the collect harness dumps the input so the
        // offending case can be reproduced/minimized), or `Ok` if none.
        let mut violations: Vec<String> = Vec::new();
        // Bound how many we accumulate so a pathologically mismatchy input can't balloon memory /
        // the dumped message (the diffs are huge).
        const MAX_V: usize = 8;
        for req_env in schema.request_envs() {
            match check {
                SymccCheck::AlwaysAllows | SymccCheck::AlwaysDenies => {
                    let Ok(compiled) = CompiledPolicySet::compile(policies, &req_env, schema) else {
                        continue;
                    };
                    let rust_asserts = match check {
                        SymccCheck::AlwaysAllows => always_allows_asserts(&compiled),
                        SymccCheck::AlwaysDenies => always_denies_asserts(&compiled),
                        _ => unreachable!(),
                    };
                    let lean = match check {
                        SymccCheck::AlwaysAllows => {
                            ffi.asserts_of_check_always_allows(policies, lean_schema.clone(), &req_env)
                        }
                        SymccCheck::AlwaysDenies => {
                            ffi.asserts_of_check_always_denies(policies, lean_schema.clone(), &req_env)
                        }
                        _ => unreachable!(),
                    };
                    let lean_asserts = match lean {
                        Ok(Ok(a)) => a,
                        Ok(Err(e)) => { violations.push(format!("[{req_env:?}] lean encode err: {e}")); continue; }
                        Err(e) => { violations.push(format!("[{req_env:?}] lean compile failed: {e}")); continue; }
                    };
                    if let Err(diff) = asserts_match_result(rust_asserts, lean_asserts) {
                        violations.push(format!("[{req_env:?}] {diff}"));
                    }
                }
                SymccCheck::NeverErrors => {
                    for policy in policies.policies() {
                        let Ok(compiled) = CompiledPolicy::compile(policy, &req_env, schema) else {
                            continue;
                        };
                        let rust_asserts = never_errors_asserts(&compiled);
                        let lean_asserts = match ffi
                            .asserts_of_check_never_errors(policy, lean_schema.clone(), &req_env)
                        {
                            Ok(Ok(a)) => a,
                            Ok(Err(e)) => { violations.push(format!("[{req_env:?}] lean never_errors encode err: {e}")); continue; }
                            Err(e) => { violations.push(format!("[{req_env:?}] lean never_errors compile failed: {e}")); continue; }
                        };
                        if let Err(diff) = asserts_match_result(rust_asserts, lean_asserts) {
                            violations.push(format!("[{req_env:?}] {diff}"));
                        }
                    }
                }
            }
            if violations.len() >= MAX_V {
                break;
            }
        }
        if violations.is_empty() {
            TargetResult::Ok
        } else {
            TargetResult::Violation(violations.join("\n----\n"))
        }
    }
}

/// Input for targets that need two policy sets (implies, equivalent, disjoint).
pub struct TwoPolicySetInput {
    pub schema: Schema,
    pub policies1: PolicySet,
    pub policies2: PolicySet,
}

/// Target for two-policy-set inputs.
pub trait PairTarget: Sync {
    fn name(&self) -> &str;
    fn run(&self, input: &TwoPolicySetInput) -> TargetResult;
}

/// SymCC term DRT for two-policy-set checks (implies, equivalent, disjoint).
#[cfg(feature = "symcc")]
pub struct SymccPairTermDrt {
    ffi: cedar_lean_ffi::CedarLeanFfi,
    check: SymccPairCheck,
}

#[cfg(feature = "symcc")]
#[derive(Clone, Copy)]
pub enum SymccPairCheck {
    Implies,
    Equivalent,
    Disjoint,
}

#[cfg(feature = "symcc")]
impl SymccPairTermDrt {
    pub fn new(check: SymccPairCheck) -> Self {
        Self {
            ffi: cedar_lean_ffi::CedarLeanFfi::new(),
            check,
        }
    }
}

#[cfg(feature = "symcc")]
impl PairTarget for SymccPairTermDrt {
    fn name(&self) -> &str {
        match self.check {
            SymccPairCheck::Implies => "symcc-term-implies",
            SymccPairCheck::Equivalent => "symcc-term-equivalent",
            SymccPairCheck::Disjoint => "symcc-term-disjoint",
        }
    }

    fn run(&self, input: &TwoPolicySetInput) -> TargetResult {
        use cedar_drt_inner::symcc::assert_that_asserts_match;
        use cedar_policy_symcc::{
            CompiledPolicySet, disjoint_asserts, equivalent_asserts, implies_asserts,
        };

        let lean_schema = match self.ffi.load_lean_schema_object(&input.schema) {
            Ok(s) => s,
            Err(_) => return TargetResult::Skipped,
        };

        let ffi = &self.ffi;
        let schema = &input.schema;
        let policies1 = &input.policies1;
        let policies2 = &input.policies2;
        let check = self.check;

        catch_violation(move || {
            for req_env in schema.request_envs() {
                let Ok(cpset1) = CompiledPolicySet::compile(policies1, &req_env, schema) else {
                    continue;
                };
                let Ok(cpset2) = CompiledPolicySet::compile(policies2, &req_env, schema) else {
                    continue;
                };

                let rust_asserts = match check {
                    SymccPairCheck::Implies => implies_asserts(&cpset1, &cpset2),
                    SymccPairCheck::Equivalent => equivalent_asserts(&cpset1, &cpset2),
                    SymccPairCheck::Disjoint => disjoint_asserts(&cpset1, &cpset2),
                };

                let lean_asserts = match check {
                    SymccPairCheck::Implies => ffi
                        .asserts_of_check_implies(
                            policies1,
                            policies2,
                            lean_schema.clone(),
                            &req_env,
                        )
                        .unwrap()
                        .unwrap(),
                    SymccPairCheck::Equivalent => ffi
                        .asserts_of_check_equivalent(
                            policies1,
                            policies2,
                            lean_schema.clone(),
                            &req_env,
                        )
                        .unwrap()
                        .unwrap(),
                    SymccPairCheck::Disjoint => ffi
                        .asserts_of_check_disjoint(
                            policies1,
                            policies2,
                            lean_schema.clone(),
                            &req_env,
                        )
                        .unwrap()
                        .unwrap(),
                };

                assert_that_asserts_match(rust_asserts, lean_asserts);
            }
        })
    }
}

/// SymCC solver check (PBT): compiles and runs solver, asserts no crash.
/// This is what the `symcc-check-*-ok` targets do.
#[cfg(feature = "symcc")]
pub struct SymccCheckOk {
    check: SymccCheck,
}

#[cfg(feature = "symcc")]
impl SymccCheckOk {
    pub fn new(check: SymccCheck) -> Self {
        Self { check }
    }
}

#[cfg(feature = "symcc")]
impl Target for SymccCheckOk {
    fn name(&self) -> &str {
        match self.check {
            SymccCheck::AlwaysAllows => "symcc-check-always-allows-ok",
            SymccCheck::AlwaysDenies => "symcc-check-always-denies-ok",
            SymccCheck::NeverErrors => "symcc-check-never-errors-ok",
        }
    }

    fn run(&self, input: &ValidationInput) -> TargetResult {
        use cedar_drt_inner::symcc::{PolicySetTask, PolicyTask, RUNTIME, ValidationTask};

        let schema = input.schema.clone();
        let policies = input.policies.clone();
        let check = self.check;

        catch_violation(move || {
            match check {
                SymccCheck::AlwaysAllows => {
                    RUNTIME
                        .block_on(PolicySetTask::CheckAlwaysAllows.check_ok(schema, policies))
                        .unwrap();
                }
                SymccCheck::AlwaysDenies => {
                    RUNTIME
                        .block_on(PolicySetTask::CheckAlwaysDenies.check_ok(schema, policies))
                        .unwrap();
                }
                SymccCheck::NeverErrors => {
                    for policy in policies.policies() {
                        RUNTIME
                            .block_on(
                                PolicyTask::CheckNeverErrors
                                    .check_ok(schema.clone(), policy.clone()),
                            )
                            .unwrap();
                    }
                }
            }
        })
    }
}

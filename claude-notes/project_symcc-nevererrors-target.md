---
name: symcc-nevererrors-target
description: "SymCC never-errors DRT experiment target: handwritten arms instrumented + welltyped variant + dep-staleness fix; built, not yet launched"
metadata:
  node_type: memory
  type: project
---

# SymCC never-errors term-DRT experiment target (2026-08-06)

Parallel to the validation experiment ([[project_welltyped-generator-soundness-bugs]]), on the
symbolic compiler. Target = `symcc-term-never-errors`: compile each policy per request env, compare
Rust `never_errors_asserts` vs Lean `asserts_of_check_never_errors` (SMT `Term`s) — NO solver/cvc5.
Chosen over always-allows/denies (single-policy too, but never-errors exercises full condition
compilation) and equivalent/implies/disjoint (need TWO policysets). SymCC uses STATIC policies by
construction (`StaticABACPolicy`/`arbitrary_static_policy`) so no `-noslots` variant needed.

## What was already there
- Coverage/replay side COMPLETE: `coverage/src/target.rs` `SymccTermDrt` + `SymccCheck::NeverErrors`
  (`#[cfg(feature="symcc")]`), selected via `main.rs` `TargetKind::SymccTermNeverErrors`
  (`--target symcc-term-never-errors`). Consumes `ValidationInput{schema,policies}` = same as the
  Lean welltyped-policy generator produces. So specimen arm works out of the box.

## STALENESS FIX (the "out of date" — was a duplicate crate, not API drift)
Two `cedar_policy_symcc` in the coverage graph: local `./cedar/cedar-policy-symcc` = **0.5.0**, plus a
stray **crates.io 0.5.1** pulled by `cedar-drt-inner`'s `cedar-policy-symcc = "*"`. `Term` types didn't
unify (`cedar_lean_ffi::Term` ↔ `symcc::term::Term` vs `err::Term`). FIX: added
`cedar-policy-symcc = { path = "../../cedar/cedar-policy-symcc" }` to `coverage/Cargo.toml`
`[patch.crates-io]` + `cargo update -p cedar-policy-symcc@0.5.1` to drop the stale lock entry → all on
local 0.5.0. `symcc` feature now compiles.

## Handwritten instrumentation (mirrors validation-drt-type-directed edits — [[guided-handwritten-rebuild]])
- `fuzz/src/symcc.rs`: `run_never_errors_drt(schema,pset)->bool` (mirrors the coverage replay body;
  returns compiled_any) + `fuzz_never_errors` (PLAIN: note_attempt + log_input ON COMPILE-SUCCESS, no
  reject) + `fuzz_never_errors_welltyped` (`Corpus::Reject` on `!is_well_typed`, steers libFuzzer to
  compilable). Reuses `validation_drt::{is_well_typed, encode_replayable}` + `guided_log`. "valid" for
  symcc = COMPILED (reached comparison), not just schema-converts.
- `fuzz_targets/symcc-term-drt-never-errors.rs` (rewritten to use shared body + install_stats_at_exit)
  + NEW `fuzz_targets/symcc-welltyped-term-drt-never-errors.rs`; both registered in `fuzz/Cargo.toml`.
- `coverage/src/bin/experiment.rs`: added `SymccTerm{AlwaysAllows,AlwaysDenies,NeverErrors}` to
  `TargetArg`/as_str/make_target (`#[cfg(symcc)]`) — cedar-experiment runs the oracle in the throughput
  probe, so it needs the target too.
- Build wiring: `run_experiment.sh` COV_FEATURES + `user_data_body.sh` PHASE1_FEATURES/DRTCOV_FEATURES
  append `,symcc` when `TARGET == symcc-*` (both cedar-experiment AND cedar-drt-coverage).

## VERIFIED (all compile clean)
fuzz lib, `cedar-drt-coverage`+symcc, `cedar-experiment`+symcc, AND `cargo fuzz build -s none` of BOTH
targets (sancov, links Lean) — binaries present at fuzz/target/.../release/symcc-*never-errors.

## NOT YET DONE (needs user go — validation 6-arm run i-0d8a3545 still in flight)
- Write symcc approaches file (specimen `symcc-term-never-errors` via lean-schema-typeof welltyped-policy
  + hw plain `symcc-term-drt-never-errors` + hw `symcc-welltyped-term-drt-never-errors`).
- Repackage under a SEPARATE `SRC_PREFIX` (e.g. bootstrap-symcc) so it never overwrites the validation
  run's src.tgz. Launch as a 2nd instance (quota 1152 ok). TARGET=symcc-term-never-errors.

## SMOKE TEST FOUND: non-transitive action hierarchy (BLOCKS specimen arm) — 2026-08-06
Local smoke (cedar-experiment throughput, specimen welltyped-policy -> symcc-term-never-errors)
PANICKED at coverage/src/target.rs:281 `.unwrap()`:
`LeanBackendError("failed to validate environment ...: action hierarchy is not transitive from
Action::"b" to Action::"c"")`. ROOT CAUSE: `WfActionAncestors` (CedarGen/Relational/Schema.lean)
picks action ancestors from defined UIDs but does NOT transitively close them. Rust
`CompiledPolicy::compile` accepts the schema; Lean symcc `SymEnv` well-formedness validation
REQUIRES a transitively-closed action hierarchy -> rejects -> unwrap panics. The ENTITY hierarchy
already closes (via `PickClosedAncestors`; the enum-hierarchy fix) — the ACTION hierarchy never got
the same treatment. Handwritten arm unaffected (cedar-policy-generators closes action hierarchies).
NEW gap, distinct from [[reference_relational-action-type-soundness-gap]] (action TYPE) and the
validation soundness bugs. FIX: make action ancestors transitively closed in the generator (mirror
PickClosedAncestors — build actions in order, each ancestor contributes itself + its closed ancestor
set), then rebuild static libs + repackage. BLOCKS the symcc launch until fixed.

## RE-CHECK: validation runs UNAFFECTED by the non-transitive-action-hierarchy gap
`validateWellFormed` (the transitivity check, Cedar/Validation/EnvironmentValidator.lean:181) is
called ONLY from CedarFFI/Main.lean:184 (the SymCC compile path). `Cedar.Validation.validate` uses
`checkEntities` but NEVER `validateWellFormed` → never checks action-hierarchy transitivity. So both
Lean+Rust validate silently accept non-transitive schemas → no crash/mismatch/abort. The in-flight
6-arm validation run (i-0d8a3545) is FINE. Only caveat: mild input-realism (some generated action
hierarchies aren't transitively closed; descendentOf is one-hop so a few transitive action-`in` edges
are just absent). The gap ONLY crashes symcc.

## COVERAGE SCOPE for symcc: measure COMPILER, ignore VALIDATOR (implemented)
Per user: symcc target coverage = the symbolic compiler (cedar-policy-symcc), NOT the validator.
- `instrument_cedar_only.sh`: now param by `$INSTRUMENT_CRATES` (default cedar_policy+core+drt_coverage).
- symcc runs set `INSTRUMENT_CRATES="cedar_policy_symcc cedar_drt_coverage"` → validator crates NOT
  instrumented at all (no validator coverage collected).
- `coverage_analyze.py` IGNORE_REGEX now `os.environ.get("COVERAGE_IGNORE_REGEX", <default>)`; default
  still drops cedar-policy-symcc (validator mode). symcc runs set COVERAGE_IGNORE_REGEX to KEEP
  cedar-policy-symcc and EXPLICITLY drop cedar-policy-core|cedar-policy-validator (+harness/deps).
- Wired in BOTH user_data_body.sh (EC2) and run_experiment.sh (local), keyed off `TARGET == symcc-*`.
All compile-verified; NOT yet launched. STILL BLOCKED on the generator transitive-action-closure fix.

## TRANSITIVE-CLOSURE FIX DONE + VERIFIED (2026-08-06)
Schema.lean: added `AppendUID` (EntityUID append) + `PickClosedActionAncestors` (action analogue of
`PickClosedAncestors`) + `WfActionsGo` (topological build threading `built: List (EntityUID × List
EntityUID)`, each action picks closed ancestors from EARLIER-built actions only → acyclic +
transitively closed). Inlined the old `WfActionEntry` into `WfActionsGo`; removed `ActionUIDDefined`
+ `WfActionAncestors` + old 4-index `WfActionSchema`; new `WfActionSchema` is 2-index (ets, entries)
running `WfActionsGo ets [] actionEidPool`. `WfTypeEnv.mk` updated (dropped actionUIDs). SelectRemove
kept (still used by WfActionsGo). VERIFIED: pure-Lean closure check 250 actions / 0 violations; static
libs rebuilt; end-to-end smoke (cedar-experiment throughput specimen→symcc-term-never-errors) =
30788/30788 valid, 0 panics, 0 mismatches, 1539/s. Blocker cleared.

## SymCC RUN LAUNCHED (2026-08-06)
Instance **i-0535e9ae5dea12243** (c7i.48xlarge), S3ROOT **ci-run-20reps-900s-20260806T230400Z**,
TARGET=symcc-term-never-errors, SRC_PREFIX=**bootstrap-symcc** (isolated from validation run's
bootstrap/), REPS=20 RUN_SECS=900 SEED_BASE=23e12 ON_FINISH=stop, golden AMI, AWS_PROFILE
cedar-experiment. approaches.symcc-nevererrors.txt: symcc-wt-policy-sz12 (specimen) + hw-symcc-plain
+ hw-symcc-welltyped. 3×20×2=120 jobs. Coverage = symbolic COMPILER (INSTRUMENT_CRATES=
cedar_policy_symcc+cedar_drt_coverage; COVERAGE_IGNORE_REGEX keeps symcc, drops validator). Runs
INDEPENDENT of the 6-arm validation run i-0d8a3545 (different instance/S3ROOT/SRC_PREFIX). Do NOT
kill either w/o direction. Results → s3://.../ci-run-20reps-900s-20260806T230400Z/results/.

## SYMCC COVERAGE-ZERO BUG FIXED (2026-08-07)
Root cause: `main.rs` `replay_s3_corpus`/`replay_proto_corpus` HARDCODED `ValidationDrt`, ignoring
`--target` — so PHASE 3.5 replay ran the VALIDATOR, but INSTRUMENT_CRATES=cedar_policy_symcc only →
0 symcc coverage. FIX: both replay fns take `&Args` and use `make_target(args)` (respect --target).
`coverage_analyze.py`: new `REPLAY_TARGET=os.environ.get("TARGET","validation-drt")` appended as
`--target` to BOTH replay cmds (validation runs default-safe). `run_experiment.sh`: `export TARGET`.
VALIDATOR EXCLUSION CONFIRMED: validator lives in cedar_policy_core::validator (Validator/Typechecker)
+ cedar_policy wrapper — NOT in cedar-policy-symcc (which only calls into core). So
INSTRUMENT_CRATES="cedar_policy_symcc cedar_drt_coverage" excludes it at instrumentation; COVERAGE_IGNORE_REGEX
drops cedar-policy-core|cedar-policy-validator as backup. Compiles clean (symcc,lean-gen,profraw,s3).

## PLOT FIX: over-time grid to MIN endpoint (2026-08-07)
plot_over_time.py gridded each arm to MAX rep endpoint → sz20's slow-gen reps (a pathological seed
hits the 50s GENERATE_TIMEOUT near window end → last snapshot at ~937/943s) stretched sz20 curves
past the other arms + drew the 900→940 tail from only 1-2 reps (survivorship). Changed to MIN kept-rep
endpoint (drop-incomplete already removes undershooters) → all arms end at common window, every point
backed by all reps. NOTE finding: sz20 generation still has occasional ~50s stalls (backtrack-fuel
explosion at large size) — guard handles (skip+continue), but a per-generate fuel cap would be cleaner.

## 1-HOUR 2-SIZE RUNS LAUNCHED (2026-08-07) — hw-slots-off vs wt-policy sz12/sz20, NO filtered/welltyped
- VALIDATION: i-0dbb2550a5477dcc9, S3ROOT ci-run-20reps-3600s-20260807T041135Z, TARGET=validation-drt,
  approaches.validation-2size.txt (wt-policy-sz12, wt-policy-sz20, hw-slots-off).
- SYMCC:      i-0a30416229ef8b0d2, S3ROOT ci-run-20reps-3600s-20260807T041143Z, TARGET=symcc-term-never-errors,
  approaches.symcc-2size.txt (symcc-wt-policy-sz12, symcc-wt-policy-sz20, hw-symcc-plain).
Both REPS=20 RUN_SECS=3600 (1h) SEED_BASE=24e12/25e12 ON_FINISH=stop, golden AMI, SRC_PREFIX=bootstrap-symcc
(has coverage-replay fix + transitive-closure Lean + min-endpoint plot fix + validator-excluded symcc cov).
120 jobs each. Do NOT kill w/o direction.

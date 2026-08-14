---
name: illtyped-policy-error-corpus
description: Wired the TypeOfError error generator into the FFI as strategy=illtyped-policy for a validation error-path coverage corpus; the CedarGen.lean native-compile gotcha; 30s smoke results
metadata: 
  node_type: memory
  type: project
  modified: 2026-08-11T20:12:24.285Z
  originSessionId: 80b33588-72ac-4fb9-a607-0ff17df90158
---

# illtyped-policy: error-semantics coverage corpus (2026-08-11)

Wired the error generator ([[typeof-error-spec]], `PolicyGenError.generateErrorPolicies` over
`IllTypedPolicy`/`PolicyBodyErr`) into the FFI as a new **strategy `illtyped-policy`**, mirroring
`welltyped-policy` (same wire format, real scopes via `encodePolicies`). Goal: an all-ill-typed
corpus to cover the Rust validator's ERROR paths. See [[generator-weight-tuning]] for run mechanics.

## Edits (all uncommitted working tree)
- `CedarFFI/Generate.lean`: added `import CedarGen.Relational.PolicyGenError`; an `illtyped-policy`
  branch in `generateSchemaTypeOfProtoFFI` calling `generateErrorPolicies`; added it to
  `listStrategies`. Also added `@[export illtypedSelfCheck]` (compiled generate + in-Lean validate,
  returns JSON `{envs,generated,rejected,accepted,samples}`) for a soundness self-check.
- `cedar-lean-ffi/src/lean_ffi.rs`: `fn illtypedSelfCheck` extern + `illtyped_self_check(params)->Vec<u8>` wrapper.
- **`CedarGen.lean`: added `import CedarGen.Relational.PolicyGenError`** — THE CRITICAL FIX (below).
- Scratch bins `cedar-drt/coverage/src/bin/errsmoke.rs` (corpus smoke: err/warn/clean tally, kind
  histogram, `COMPARE_LEAN`, `COMPARE_DRT`, `DUMP_BATCH0`) and `errselfcheck.rs` (calls the FFI self-check).
- Approaches file `cedar-drt/coverage/experiment_scripts/aws/approaches.illtyped.txt` (4 arms).

## ⚠️ THE GOTCHA (cost me a long misdiagnosis): native-compile of the generator
A relational generator called from the FFI must be **natively compiled into a `:static` archive**,
which means it must be transitively imported by a library ROOT that's built with `:static`.
`PolicyGenError` lives under `CedarGen/Relational/` but `CedarGen.lean` did NOT import it, so
`CedarGen:static` never compiled it to native `.o`. The FFI still LINKED (symbols resolved via the
`CedarFFI:static` transitive olean→C path) and RAN, but produced a **broken/mis-initialized
generator that emitted ~96% WELL-TYPED policies** — which looked exactly like generator unsoundness
or a proto round-trip bug (both Lean-via-FFI and Rust agreed the outputs were well-typed; only the
INTERPRETER `#eval` self-check said 400/400 ill-typed). Fix = `import CedarGen.Relational.PolicyGenError`
in `CedarGen.lean`, rebuild `CedarGen:static CedarFFI:static`. After the fix: compiled self-check =
**1000/1000 rejected, 0% unsound**; corpus smoke = **0 clean-leaks, 100% flagged, perfect Lean/Rust
agreement**, throughput ~130k policies/25s. LESSON: when a new FFI-called generator behaves
differently compiled vs `lake env lean`, suspect the native-compile/import chain FIRST; use the
compiled self-check FFI to isolate generator soundness from the proto round-trip.

## Corpus characteristics (local errsmoke, size 20, after fix)
- 100% ill-typed. Rust diagnostic split: ~55% ERROR, ~45% WARN-only. The WARN-only are
  `impossiblePolicy` (`when { false }`): Cedar emits a WARNING, the Lean spec emits an ERROR.
  `validation_passed()` is errors-only so it MISSES these — count warnings too (`validation_warnings()`
  / `validation_passed_without_warnings()`). User confirmed the DRT harness does NOT count the
  impossiblePolicy error-vs-warning split as a mismatch, so a `validation-drt` run is safe.
- Error-kind mix (Debug variant names): UnexpectedType dominant, then IncompatibleTypes (lubErr/
  set), EmptySetForbidden, UnsafeAttributeAccess (attrNotFound), UnsafeTagAccess (tagNotFound),
  UnrecognizedEntityType (unknownEntity). All 9 kinds present; impossiblePolicy heavy (~45%).

## 30s smoke run (validation-drt, 4 arms x 20 reps, c7i.48xlarge, 2026-08-11)
S3ROOT `ci-illtyped-smoke-30s`; instance i-08c189bb971e634f6 (STOPPED). SRC_PREFIX `bootstrap-illtyped`.
Pipeline works end-to-end (build via LEAN_CACHE, generate, coverage, bootstrap CI, plots, upload, stop).
Median source_lines_covered: err-policy-sz20 **4543**, wt-policy-sz20 **5264**, hw-slots-off/
hw-welltyped-noslots **2406** (guided cargo-fuzz is COLD in 30s → subset of specimen; needs the full
hour). err-policy unique_inputs ~85k/30s (vs wt ~11k) — error policies are cheap → high diversity.
validator module: specimen covers 2683 lines (1701 only-spec + 982 shared), only_hw=0 (handwritten cold).
Plots in `~/illtyped_smoke_graphs/`.

## Remaining
- 1-hour run (same 4 arms, RUN_SECS=3600) — the real deliverable; handwritten arms only meaningful there.
- Idea (user): a specimen strategy producing a MIX of well+ill-typed (currently illtyped-policy is
  100% error; hw-slots-off is the only mixed arm). Would need a new relation/strategy.
- Possibly downweight `PolicyBodyErr.impossible` if 45% impossiblePolicy is too skewed for error-path value.

---
name: local-line-coverage-analysis
description: "How to get per-line/region coverage of a specific cedar file LOCALLY (30s, welltyped gen only) via an instrumented harness + llvm-cov, with the correct exclusion sets"
metadata:
  node_type: memory
  type: reference
  originSessionId: afda0cfd-9bab-4c71-962e-e70942c9f7af
  modified: 2026-08-10T17:28:47.889Z
---

# Local per-line coverage of a cedar file (no EC2, ~30s run)

Goal: see which lines of e.g. `cedar-policy-core/src/validator/typecheck.rs` OUR welltyped generator
covers/misses, fast and locally. See also [[generator-weight-tuning]], [[error-annotation-coverage-exclusion]].

## Recipe
1. Instrumented harness bin `cedar-drt/coverage/src/bin/covrun.rs`: `CedarLeanFfi::new()` → loop for N secs
   calling `ffi.generate_schema_typeof_proto({seed,size:20,schema_size:20,strategy:"welltyped-policy",count:100})`
   (returns Result — use `.ok()`/`Ok(b)`), decode schema+each policy, `Validator::new(schema).validate(&ps,
   ValidationMode::Strict)`. (This drives cedar_policy_core::validator = typecheck.rs.)
2. Build INSTRUMENTED (coverage only on the cedar crates) via the RUSTC_WRAPPER:
   `source cedar-drt/set_env_vars.sh` (for the .lake FFI libs), then from cedar-drt/coverage:
   `RUSTC_WRAPPER=$PWD/experiment_scripts/instrument_cedar_only.sh INSTRUMENT_CRATES="cedar_policy cedar_policy_core covrun" cargo build --release --bin covrun --features lean-gen --target-dir target_cov`
   (instrument_cedar_only.sh scopes `-C instrument-coverage` to the named crates; include the bin so the
   LLVM runtime links). ~45s if deps cached.
3. Run: `LLVM_PROFILE_FILE=/tmp/cov/covrun-%p.profraw ./target_cov/release/covrun 30` (10k+ policies in 30s).
4. `llvm-profdata merge -sparse /tmp/cov/*.profraw -o m.profdata` then
   `llvm-cov export target_cov/release/covrun -instr-profile=m.profdata --ignore-filename-regex="$IGNORE"`
   (tools in `$(rustc --print sysroot)/lib/rustlib/*/bin/`). Parse JSON functions[].regions[] =
   [l1,c1,l2,c2,count,fileid,…]; region-line COVERED if any region over it has count>0; total = any region.

## Exclusions (apply these for a FAIR uncovered set)
- IGNORE_REGEX (file-level, default in coverage_analyze.py): drops
  `.cargo/registry|/rustc/|/tests?|_test.rs|/kpath|cedar-policy-generators|cedar-drt|cedar-lean-ffi|cedar-policy-symcc`
  → keeps cedar_policy(_core) validator. Override via `COVERAGE_IGNORE_REGEX` (symcc run keeps symcc, drops validator).
- LINE-level elision (COVERAGE_EXCLUDE_LINES = a "relpath:line" file): the runner uses
  `cedar-drt/coverage/spec_unreachable_exclude.txt` (2681 lines; also error_only_exclude.txt / annotation_exclude.txt / mir_error_only_lines.json). `_excl_norm` matches on the `cedar-policy-core/…` path suffix.

## Findings on typecheck.rs (SingleEnvTypechecker) coverage (2026-08-10)
Welltyped gen covers 1060/1382 region-lines; after IGNORE+spec_unreachable elision, ~267 "fair" uncovered.
Reading them: the OVERWHELMING majority are **ill-typed-input error/diagnostic branches** a well-typed
generator can't reach (`expected_one_of_types` for wrong comparison/arith operands, `UnexpectedTypeHelp`
hints, `no_tags_allowed`/`incompatible_types`/`undefined_extension`/`wrong_number_args`, has_attr/getTag/is_in
FAIL arms). The rest are features THIS target doesn't drive: **template slots** (Slot typing, possible_slot_links
— gen makes static policies), **partial mode** (`mode.is_partial()` — we use Strict), **entity-LUB/AnyEntity**
receivers (tag_types/is_entity_type on AnyEntity — gen uses single concrete entity types). LESSON: the
error-only elision (spec_unreachable_exclude.txt) is INCOMPLETE for typecheck.rs — it caught only ~55 of ~250
error-branch lines; extend it if you want "fair coverage" to reflect real logic not error handling.

## Latent Rust bug found by reading covered code (typecheck.rs:636) — NOT differential-catchable
`&&` typecheck `(Bool(True), _)` arm does `capability_right.union(&capability_right)` (self-union) — drops
`capability_left`; symmetric arm (628) correctly unions both; Lean typeOfAnd is correct (`c₁ ∪ c₂`). INERT:
a `Bool(True)`-typed expr provably never carries a capability (caps only produced on `anyBool` hasAttr/hasTag
branches; combinators yield `tt` only from cap-empty `tt` operands), so `c₁=∅` there and `∅∪c₂ = c₂∪c₂`.
So line 636 is covered + runs but can't produce a wrong result → no mismatch. Real typo worth an upstream
defensive fix, but unobservable via DRT.

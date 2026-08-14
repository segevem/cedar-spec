---
name: error-annotation-coverage-exclusion
description: "Sound error+annotation line-exclusion set for fair line-coverage comparison (what, where, how it was computed)"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 60db3c98-5034-4030-861c-4468d8c04ec7
  modified: 2026-08-07T23:18:53.221Z
---

# Excluding spec-unrepresentable lines (error + annotation) from line coverage

Goal: fair specimen-vs-hw line-coverage comparison by eliding code the Lean spec CANNOT
represent, so hw isn't credited for coverage no spec-derived generator can reach.

## Two categories elided (both structurally unreachable by specimen)
1. **Error-handling code** — Cedar has 34 error ctors / 10 inductive types; policy-relevant =
   8 `Validation.TypeError` (Typechecker.lean:28) + 6 `Spec.Error` eval (Value.lean:30).
   Rust warnings = 6 `ValidationWarning` (5 Unicode-lint via `str_checks.rs` + `impossiblePolicy`);
   the gate `validation_passed()` = errors.is_empty() IGNORES warnings, so warnings are NOT error
   and are NOT elided (they're reachable on passing runs).
2. **Annotation code** — annotations aren't in the Lean spec. = whole `ast/annotation.rs`+
   `est/annotation.rs` (88 lines) + the annotation-key decode chain reached via
   `proto/policy.rs:119 AnyId::from_normalized_str` → `parser.rs parse_anyid` → `cst_to_ast to_any_ident`
   + `ast/id.rs` AnyId Display (45 lines). Total ~133.

## THREE error models in cedar (KEY — determines what's provably error-only)
- **Result-propagation** (parser/evaluator/extensions): returns `Result<_,DomainError>`; MIR CFG
  reachability (below) SOUNDLY finds error-only lines here (112 lines).
- **Accumulation** (the VALIDATOR): `typecheck_*` returns `TypecheckAnswer`, `validate` returns
  `ValidationResult`; errors are `type_errors.push(...)` SIDE-EFFECTS on continuing paths → NO
  Result Err-return → CFG reachability finds ~nothing; error-only = the push/detection arms only.
- **Render** (`err.rs` modules, Display/Diagnostic): only run when an error VALUE exists (data property).

## How the sound set was computed (MIR CFG, corpus-independent)
`RUSTC_BOOTSTRAP=1 cargo rustc --lib -- --emit=mir -Zmir-include-spans=on` (in cedar/cedar-policy-core
and cedar/cedar-policy) → textual MIR. Parse bb terminators (switchInt/goto/call `-> [return:..]`,
ignore `unwind`/`cleanup`); error-only = reachable-from-entry MINUS on-any-`Ok`-exit-path, keyed on
`_0 = Result::Ok/Err(` commits. Then add whole `err.rs` modules + verified construction sites
(`type_errors.push`, `ValidationError::`, `TypecheckAnswer::fail`, `extension_err`). FALSIFY with the
spec (all-passing) corpus: any candidate line a PASSING input covers is NOT error-only (removed).

## Result
- Error-only elision ≈ **2,547** region-lines; + annotation **133** = **2,680** total.
- CAVEAT: specimen is NOT perfectly well-typed — it rejects **0.06%** (122/200k) with
  `unsafe_attribute_access`/`unsafe_optional_attribute_access` (a `HasType` capability/optional-attr
  gap, distinct from the earlier Bug1/Bug2). hw rejects 1.9%. So spec DOES cover ~a few error lines
  via its own bad outputs; the sound set re-includes error-only lines regardless (they're error by
  construction). Fixing that HasType gap is a real TODO.

## Durable artifacts (in cedar-drt/coverage/, survive compaction)
- `spec_unreachable_exclude.txt` (2,680 relpath:line) — THE elision set, feed via `COVERAGE_EXCLUDE_LINES`.
- `error_only_exclude.txt`, `annotation_exclude.txt` (the components).
- `error_only_lines_SOUND.tsv`, `only_hw_error_classification.tsv`, `mir_error_only_lines.json` — per-line detail.
- coverage_analyze.py honors `COVERAGE_EXCLUDE_LINES` (drops from covered+total in `file_sets`/
  `covered_line_set_by_function`; `covered_counts()` returns (raw, excluded) for the over-time overlay).
See [[coverage-only-reuse-workflow]] (how to run it) and [[specimen-vs-hw-coverage-findings]] (results).

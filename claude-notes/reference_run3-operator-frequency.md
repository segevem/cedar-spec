---
name: run3-operator-frequency
description: "Run#3 corpus operator-frequency diff (specimen vs hw-slots-off); cold-start sampling pitfall; offset is the one specimen=0 gap"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 01c084b2-8df7-4bc5-913e-f57d20956638
  modified: 2026-08-06T00:00:23.569Z
---

# Run #3 corpus operator frequencies: specimen (wt-policy-sz12) vs hw-slots-off

Measured by decoding collected corpus `.bin` files (`[u32 len ‖ [schema_len:u32 ‖
schema-proto ‖ policies-proto]]`) and walking each policy condition AST. Tool:
`cedar-drt/coverage/src/bin/op_hist.rs` (SCRATCH; recursive dir walk; reuses decode_batch +
cedar_policy_core ExprKind). Build: `cargo build --bin op_hist` (needs Lean env vars).

## CRITICAL SAMPLING PITFALL (got this wrong first)
Sampling only the FIRST ~100 batches of rep_00 = libFuzzer COLD-START corpus (trivial,
tiny inputs) → falsely showed hw-slots-off with ZERO arithmetic/extensions. WRONG.
FIX: stratify — sample batches spread across ALL reps AND the full batch-index range
(e.g. idx 10/120/240/360/450 × reps 00-19). Then the real distribution appears.

## Corrected result (stratified: 76k specimen policies, 98k hw policies)
Both generators exercise the FULL operator set; specimen just packs MORE per policy:
- specimen richer: Lit 6.9 vs 2.3, And 4.0 vs 1.0, In 0.72 vs 0.24, Not 0.87 vs 0.08,
  Is 1.0 vs 0.10, Less/LessEq ~0.19 vs ~0.005 (35x), HasTag 0.18 vs 0.006 (30x),
  Sub/Mul/Neg ~40x, datetime/duration 7-8x, toTime/toDate 8-29x.
- roughly EQUAL: ip, isMulticast, decimal.
- hw LEADS (modestly): Record 0.075 vs 0.006, GetAttr 0.069 vs 0.019, IsEmpty, decimal.

## The ONE robust operator gap — REVERSED from cold-start claim
**ExtFun::offset is HW-ONLY: hw=863, specimen=0** (across 76k policies). Also
durationSince hw=162 vs spec=3. These are the "compose TWO extension-typed args"
constructors (offset(datetime,duration), durationSince(datetime,datetime)) — specimen's
budget-aware gen almost never completes the nested construction, even though it emits
datetime/duration constructors heavily on their own. Matches the `.offset` residual from
[[id-bty-condition-speedup]] discussion. Only truly hw=0 op: toHours (238 vs 0) = noise.

## Ties to coverage diff (run#3 wt-policy vs hw-slots-off: shared 5429, specimen-only 117,
## hw-only 390, jaccard 0.915)
- specimen-only (117) = typecheck SUCCESS continuations (== continuation 47 lines,
  expect_one_of_types<F> monomorphizations) — real, because specimen packs more operators.
- hw-only (390) = NOT operators-hw-has-that-specimen-lacks (specimen generates more of
  nearly everything). It's offset/durationSince ext paths + VALIDATOR ERROR paths from
  hw's ill-typed schemas/scopes (wrong_number_args, failed_extension_function_application,
  invalid_enum_entity, confusable/mixed_script identifier warnings, extension_err).
  Structurally unreachable by well-typed-only specimen.
- CAVEAT: coverage by_function counts are region-lines, over-sum (239 vs 117) from
  monomorphization/inlining; error-builder lines showing under specimen are attribution
  artifacts (specimen produced 0 violations / 0 type errors).

See [[project_guided-handwritten-rebuild]] for run#3 (5616/5928/6420 lines) and run#4 (new gen).

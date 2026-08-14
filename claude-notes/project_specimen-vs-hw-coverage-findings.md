---
name: specimen-vs-hw-coverage-findings
description: "Fair (error+annotation-excluded) validator line-coverage: specimen vs hw-slots-off results + the == operand-diversity gap"
metadata: 
  node_type: memory
  type: project
  originSessionId: 60db3c98-5034-4030-861c-4468d8c04ec7
  modified: 2026-08-07T23:20:14.106Z
---

# specimen (wt-policy) vs hw-slots-off — fair coverage comparison (2026-08-07)

Run `ci-cov-excl-20260807T185731Z` (reuse of corpus `…041135Z`, 20 reps, error+annotation excluded).

## Headline: after excluding spec-unrepresentable code, they're ~95% overlapping
Region-lines (error+annotation excluded): hw 5050, wt-sz12 4995, wt-sz20 4987. Venn (Jaccard ~0.95):
- **shared ≈ 4,900**
- **only-specimen ≈ 98** — ALL core typechecking: `typecheck_binary` (47), `expected_comparison_op_types`
  (10), `typecheck_in`/unary, `ExtensionSchema::types_with_operator_overloading`. Robust to the
  exclusion (spec covers ~0 error/annotation, so only-spec is untouched).
- **only-hw ≈ 146** — NOT core validator logic: `Expr::eq_shape` (35, == structural-equality plumbing),
  Unicode-lint WARNINGS (`str_checks`+`ValidationWarning` confusable/mixed-script ≈54), enum-entity
  checks (`validate_enum_entity`+`invalid_enum_entity` ≈12, partly leaked error), expr-shape/`Display`.
So on the fair axis specimen's unique coverage is the HIGHER-value half (real typechecking); hw's is
plumbing+lint. Raw (un-excluded) gap was ~451 hw-only, ~60% error-attributable + annotations.

## The one real specimen weakness: `==` operand diversity
- specimen's `==` operands are ~99% `Lit`/`Var` (measured local + corpus): `Eq→Lit`≈52%, `Eq→Var`≈48%,
  everything else ~0. hw's `==` operands span GetAttr/HasAttr/Record/Set/nested-Eq/ExtFun at 10–1000×
  spec's rate (some ExtFun operands hw-only). Confirmed via `Binary::Eq→<operand>` 2-path histogram
  (kpath2_frequency in analyze/rep_NN.json).
- WHY it shows as coverage: the typechecker calls `Expr::eq_shape` on the two `==` operands (to
  special-case `a==a`); it only covers the arm for operand-kind K when `== K` appears. spec covers only
  the `Lit`/`Var`/`If` arms; hw uniquely covers `BinaryApp`/`GetAttr`/`HasAttr`/`Record`/`ExtFun` arms.
- (Small-sample trap: 200 batches showed spec covering eq_shape and hw 0 — eq_shape's trigger is rare;
  need the FULL hw corpus (1.6M) to see hw's 35 hw-only eq_shape lines. Verify at full scale.)

## Weight-tuning the `==` rules DOES NOT fix it (negative result — don't retry weights)
Tried down-weighting `binaryAppEqLitSame/Diff` + boosting `getAttrEntity/getAttrRecord/set/callExt`
in `favorHasTag` (BudgetAware.lean). Rebuilt, measured: `==` operands UNCHANGED (~99% Lit/Var).
Reason: `binaryAppEqNonLitLub` picks operand TYPES via `Lub` — and **Lub is a scheduler CHECK, inert
to weights** (same lesson as `Lub.record` boost). For the common scalar types it lands on, the
scheduler generates the CHEAPEST inhabitant = `Var`/`Lit`; boosting getAttr/set globally doesn't help
(those types rarely selected as `==` operand types; getAttr backtracks). REAL FIX = STRUCTURAL: add a
dedicated `eq` constructor that REQUIRES a rich operand (getAttr/record/set) on one side, not the free
`HasType x t`. (The BudgetAware.lean == edit is INEFFECTIVE — candidate to revert.) See [[generator-weight-tuning]].

## Uncommitted working-tree edits from this session (survive compaction)
- `experiment_scripts/coverage_analyze.py` (COVERAGE_EXCLUDE_LINES + covered_counts raw/excl over-time)
- `experiment_scripts/plot_over_time_excl.py` (NEW overlay plotter, real time_map, --ymin/--ymax)
- `experiment_scripts/run_experiment.sh` (REUSE_CORPUS_S3ROOT, COV_FEATURES override, default exclusion)
- `experiment_scripts/aws/launch.sh` (propagate REUSE_CORPUS_S3ROOT/COV_FEATURES)
- `coverage/src/main.rs` (REJECTED-count in replay — harmless diagnostic)
- `cedar-lean/CedarGen/Relational/Variants/BudgetAware.lean` (== bias edit — INEFFECTIVE, revert)
- `cedar-spec/scratch_eq.lean` (local == operand measurement harness — see [[generator-weight-tuning]])
`.bak` files kept for coverage_analyze.py / run_experiment.sh / BudgetAware.lean.

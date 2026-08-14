---
name: generator-weight-tuning
description: "How to tune welltyped-policy generator op frequencies (weight modifiers), measure them locally in Lean, and validate at scale on AWS"
metadata:
  node_type: memory
  type: reference
  originSessionId: 80b33588-72ac-4fb9-a607-0ff17df90158
  modified: 2026-08-07T23:20:40.205Z
---

# Tuning the welltyped-policy generator: weights, local measurement, AWS validation

Workflow used to bias op frequencies (records, isEmpty, tags…) and confirm the effect. See also
[[specimen-weight-modifier]] and [[experiment-harness-pitfalls]].

## 1. WHERE the active generator + weights live
- FFI entry `CedarGen.Relational.PolicyGen.generatePolicies` (`PolicyGen.lean`) reuses the `HasType`
  generator from **`Variant.BudgetAware`** (`cedar-lean/CedarGen/Relational/Variants/BudgetAware.lean`).
  That file's `scoped derive_mutual … HasType …` with `set_option specimen.weightModifier "favorHasTag"`
  is what produces the corpus. PolicyGen itself uses `favorConditions` (its own modifier) for clause count.
- So to change EXPRESSION-op frequencies, edit **`favorHasTag` in BudgetAware.lean** (NOT the same-named
  copy in TypeOfLeanTest.lean, which only feeds that test file — not imported by CedarGen).

## 2. HOW to change a weight
Add a match arm to `favorHasTag (baseWeight ctorName …outputIndices deriveSort scoreBadness isRec size
numBase numRec numRecCalls) : Nat`. Return `baseWeight * K + 1` to boost, `max 1 (baseWeight/2)` to suppress.
- Match unique ctor names by last component: `| .str _ "unaryAppIsEmpty" => …`, `"hasTagAnyBool"`.
- Match names that COLLIDE across inductives by parent: `| .str (.str _ "HasType") "record"`,
  `| .str (.str _ "HasTypeRecord") "cons"` (there are many `record`/`cons`/`nil` ctors).
- Def MUST be root-namespace (not namespaced) or the same-file derive won't resolve it.
- The modifier also gets `size` → could make boosts size-dependent.
- Rebuild: `lake build CedarGen.Relational.Variants.BudgetAware CedarGen.Relational.PolicyGen`.

### Lever findings (2026-08-07, config record×8/cons×6/isEmpty×10 landed)
- Expression ctors (`record`, `unaryAppIsEmpty`, `hasTag*`) DO respond to weight.
- **`Lub.record`/`LubCompat.record` boosts are INERT — do not retry.** `Lub` is scheduled as a CHECK,
  not a generator, in the derive, so weighting it never enters a generation decision. `LubRecord`
  coverage is driven only by the SUPPLY of record-typed eq/ite operands = the `record`-rule boost.
- `HasTypeRecord.cons` vs `nil` sets record fullness (~0.3→0.6 fields) but is size-gated (weight can't
  beat a small fuel budget); it's ~free on throughput.
- Diminishing returns + throughput: `isEmpty` ×10→×50 barely moves sz12 (size-capped ~0.002) and the
  ×50 backtracking (attempts isEmpty, needs a set arg, backtracks) is the ENTIRE ~40% throughput cost.
  Records/cons cost ~nothing. So **isEmpty weight is the throughput dial**, not records.

## 3. Local measurement harness (fast, no EC2) — the reliable way to A/B weights
Scratch `.lean` at repo root, run `cd cedar-lean && lake env lean ../scratch_measure.lean`.
- Imports: `CedarGen.Relational.SchemaTest` (gives `generateSchemaOnly seed schemaSize : IO (Option
  TypeEnv)` = random canonicalized WfTypeEnv, the real pipeline) + `CedarGen.Relational.PolicyGen`
  (`generatePolicies env size count (some seed)`).
- Loop over MANY seeds → random envs (NOT a fixed `testEnv`: one schema gives unrepresentative set/record
  rates — e.g. testEnv gave 0.026 sets/pol vs corpus 0.29).
- **Tally `p.toExpr`** (folds scopes+conditions like Rust `policy.condition()`), NOT `cond.body` — else you
  miss scope nodes and rates don't match the corpus. VALIDATE the harness by checking unchanged ops match
  the archived corpus (Is ~1.0, Not ~0.75, ~18/pol nodes at sz12, ~27 at sz20). Then changed ops are a
  clean A/B vs the corpus baseline.
- `#eval show IO Unit from do …` (pins the IO monad). Time with `IO.monoMsNow` around `generatePolicies`
  for pol/s. Test at BOTH sizes (schemaSize=termSize=12 and 20) — size gates a lot.
- LubRecord proxy: count eq / ite-with-nonliteral-guard sites whose operand/branch is "record-ish"
  (`.record _` OR `.var .context` — context is record-typed). `iteTt`/`iteFf` (literal guard) short-circuit,
  no Lub. Baseline already gets ~0.026 LubRecord sites/pol free via `context`.

## 4. AWS corpus run (validate coverage/throughput at scale)
After a Lean generator change:
1. Rebuild static libs (populates `.lake` the package ships):
   `cd cedar-lean && lake build Cedar:static Protobuf:static CedarProto:static Cedar.SymCC:static CedarFFI:static CedarGen:static Batteries:static`
2. Package (LEAN_CACHE=1 REQUIRED when Lean changed — ships `.lake` so instance verifies, not rebuilds):
   `cd cedar-drt/coverage/experiment_scripts/aws && SRC_PREFIX=bootstrap-boost LEAN_CACHE=1 ./package_and_upload.sh`
3. Launch (dry-run unless CONFIRM=1):
   `AWS_PROFILE=cedar-experiment SRC_PREFIX=bootstrap-boost TARGET=<validation-drt|symcc-term-never-errors> \
    APPROACHES_FILE=$PWD/approaches.{validation,symcc}-2size.txt REPS=20 RUN_SECS=3600 ON_FINISH=stop CONFIRM=1 ./launch.sh`
   - 2size approaches = wt-policy-sz12/sz20 (new gen) + hw arm (guided, 5-col line w/ fuzz_target).
   - launch.sh autosizes instance from JOBS = arms×reps×2; results → `s3://__S3_BUCKET__/<S3ROOT>/`.
   - Matching REPS/RUN_SECS to the archived old-gen runs (`ci-run-…041135Z` validation, `…041143Z` symcc)
     gives a free new-vs-old coverage comparison on top of new-vs-hw.
   - Instances STOP (not terminate) on finish — reusable; never terminate without direction.

## 5. NEGATIVE RESULT: weights CANNOT diversify `==` operands (2026-08-07)
specimen `==` operands are ~99% `Lit`/`Var` (both corpus + local harness); hw's span
GetAttr/Record/Set/ExtFun. Tried down-weighting `binaryAppEqLitSame/Diff` + boosting
`getAttrEntity/getAttrRecord/HasType.set/callExt` in `favorHasTag` → operand distribution UNCHANGED.
Reason: `binaryAppEqNonLitLub` selects operand TYPES via `Lub`, and **`Lub` is a scheduler CHECK,
inert to weights** (same as the `Lub.record` lesson); for common scalar types the scheduler emits the
CHEAPEST inhabitant (`Var`/`Lit`). Fix must be STRUCTURAL — a dedicated `eq` ctor in TypeOfLean.lean
that REQUIRES a rich operand (getAttr/record/set) on one side. The BudgetAware.lean `==` edit is
ineffective (candidate to revert). Matters because the typechecker's `eq_shape` (== `a==a` special-case)
covers an operand-kind arm only when `== <that kind>` is generated → specimen misses those arms. See
[[specimen-vs-hw-coverage-findings]].
- `==`-operand measurement harness = `cedar-spec/scratch_eq.lean` (durable): imports SchemaTest +
  PolicyGen + Variants.BudgetAware, `open Variant.BudgetAware` AND `open …PolicyGen` (generatePolicies
  is in the PolicyGen sub-namespace), walks `p.toExpr` matching `.binaryApp .eq a b` → tally
  `Eq→kindOf(operand)`. **Use `#eval!`** (the HasType derive carries a termination `sorry`, so `#eval`
  refuses). Validate via Is/Not/nodes-per-pol vs corpus.

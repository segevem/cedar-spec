---
name: specimen-weight-modifier
description: Tune how often a Specimen constructor is chosen by registering a weight modifier that pattern-matches the constructor name
metadata: 
  node_type: memory
  type: reference
  originSessionId: 7b0a8cee-4967-4ee4-83e5-e3101bc6a809
  modified: 2026-07-23T20:31:23.539Z
---

# Specimen weight modifiers — bias constructor selection frequency

To make a derived generator pick a specific rule more/less often, register a
**weight modifier**: a function that rewrites each constructor's selection weight,
keyed by matching the last component of its name.

## Pattern (from Specimen `SpecimenTest/DeriveArbitrarySuchThat/ForwardRefListGenerator.lean`)

```lean
open Scoring Schedules   -- provides `DeriveSort`

def favorHasTag (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Float) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) : Nat :=
  match ctorName with
  | .str _ "hasTagAnyBool" => baseWeight * 10 + 8   -- multiplicative boost + additive floor
  | .str _ "hasTagTt"      => baseWeight * 10 + 8
  | .str _ "hasTagFf"      => baseWeight * 10 + 8
  | _                      => baseWeight             -- everything else untouched

initialize registerWeightModifier `favorHasTag favorHasTag ``favorHasTag

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightModifier "favorHasTag" in
#time derive_mutual generator (fun env c ty => ∃ x cout, HasType x c env ty cout)
```

## The modifier def MUST be root-namespace (or a registered builtin) — else silently inert

`getActiveWeightModifier` resolves the `specimen.weightModifier "foo"` option by (1)
looking up `foo` in the `initialize`-populated registry, then (2) falling back to
`env.contains \`foo` (the option string as a **literal root Name**) + `evalConst`.
For a **same-file** derive the registry is still EMPTY at derive-elaboration time
(the module's `initialize` runs only at load/import, too late), so only the
`env.contains` fallback applies — and it uses the bare option string. Therefore:

- If you write `def favorHasTag` **inside** `namespace Variant.BudgetAware`, its real
  name is `Variant.BudgetAware.favorHasTag`; `env.contains \`favorHasTag` (root) is
  FALSE → falls back to `idWeightModifier` → **modifier silently does nothing.**
- Fix: define the modifier at **root namespace** (mirroring how `steepQualityWeight`
  weightFn is defined at root in `Steep.lean`), then `weightModifier "favorHasTag"`
  resolves. Alternatively set the option to the fully-qualified name, or register it
  as a builtin in an **imported** module (then the registry path works cross-file).
- Symptom of the bug: with/without the modifier produce **byte-identical**
  deterministic corpora. Verify a modifier is actually live by diffing deterministic
  runs (`--strategy X` with vs without) — they MUST differ, because the boosted
  constructors are considered at every choice point and reweighting them perturbs the
  PRNG stream **even if that constructor is never emitted** (confirmed 2026-07-23:
  5995/6000 files differ on schema-gen once the def was moved to root). Beware:
  `lean-typeof`'s FFI defaults to `deterministic=false` (`seed=none`) — nondeterministic
  run-to-run, so you can't test modifier effects on it without forcing `deterministic`.

## Notes

- The modifier fires for **every** relation in the mutual derivation; use the
  `_ => baseWeight` fall-through so only the named constructors are retuned.
- **Additive floor matters:** `baseWeight * k + c`. `BudgetAwareScore`/balanced
  weights zero out recursive constructors at `size = 0`; the additive `+ c` keeps a
  rule positively weighted so it can still fire near the fuel floor.
- Changing weights **re-derives** the generator (the precompiled-import trick can't
  skip it) — edit at the `derive_mutual` site and rebuild.
- Verify by re-running the generation harness and reading the op/ctor breakdown.
- The modifier is invoked at **runtime** per constructor choice (its signature takes
  `size`), but the `Lean.Name` string-matching is **cheap** — a control that kept the
  match arms but returned `baseWeight` everywhere ran at baseline speed (37s vs the
  boosted run's >12 min). So string-matching is not a perf concern.

## Aggressive multipliers can cause backtracking blowup

A large multiplier on a rule that is **often infeasible** for the current inputs
is pathological. Example: `hasTag` needs `HasTagSchema` (a tagged entity). In
`SchemaTest` (random `WfTypeEnv`), ~42% of schemas have *no* tagged entity, so
`hasTag` is infeasible there. `*10+8` forced the generator to re-pick `hasTag` at
every bool node and, with `Gen.runUntil (attempts := .none)` (unbounded retries),
it ground for >12 min. `*2+1` (mild) steered without forcing: hasTag expr-rate
17% → 35%, still 35s. Rule of thumb: **use a small multiplier (`*2+1`..`*3+2`) when
the boosted rule can be infeasible; large boosts are only safe when the rule is
always satisfiable** (e.g. `TypeOfLeanTest`'s fixed testEnv always has tags, where
`*10+8` was fine and fast — hasTag 14 → 281). Bounding retries (`attempts := .some k`)
also caps the blowup.

## Result (2026-07, cedar-spec `TypeOfLeanTest.lean`)

Boosting the three `hasTag` rules with `* 10 + 8` took `binOp:hasTag` from **14 →
281** in `propertyTest 200 30` (~20×), 200/200 still passing, 0 type failures.
`getTag` rose too (~2 → 5) as a side effect: more `hasTag` guards produce more
capabilities, which enable more `getTag`. See [[reference_specimen-id-force-check-mode]]
and [[reference_functional-to-relational-pitfalls]].

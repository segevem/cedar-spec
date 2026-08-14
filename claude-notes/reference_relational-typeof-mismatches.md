---
name: relational-typeof-mismatches
description: "Diff-testing mismatches found between the relational HasType spec and Cedar's functional typeOf, with causes and fixes"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 7b0a8cee-4967-4ee4-83e5-e3101bc6a809
  modified: 2026-07-22T20:41:27.871Z
---

# HasType (relational) vs functional typeOf — mismatches log

Running generated exprs through `Cedar.Validation.typeOf` (in `propertyTest` /
`schemaPropertyTest`) surfaces cases where the relational spec over- or
under-generates relative to the functional validator. Log them here.

## 1. hasAttr-in-caps typed anyBool instead of tt (FIXED 2026-07)

**Symptom:** `FAIL type … expected=bool anyBool got=bool tt` on top-level `or`/`and`
exprs, e.g.
`or (hasAttr principal "manager") (…)` where `(principal, .attr "manager")` was in
the seeded caps.

**Cause:** functional `hasAttrInRecord` returns `.bool .tt` when
`(x, .attr a) ∈ c` (cap already present). The relational `found_not_known` and
`found_optional_known` rules produced `.bool .anyBool` (+ a new cap) **without a
`¬CapMem` guard**, so they overlapped with `found_in_caps` and fired even when the
cap was present. Then in an enclosing `or`, functional short-circuits to `.tt`
(`hasAttr = tt`) while the relational spec had it as `.anyBool`.

**Fix:** added `¬ CapAttrMem x a c` to `found_not_known` and `found_optional_known`
in `HasAttrInRecord` (TypeOfLean.lean) — the anyBool branch may fire only when the
cap is absent, matching functional's `if (x,.attr a) ∈ c … else …`.

See [[reference_functional-to-relational-pitfalls]] pitfall #2/#8 (fall-through
branch needs explicit negation of the earlier case).

## 2. `mem` on a non-action reflexive entity typed tt instead of anyBool (FIXED 2026-07)

**Symptom:** `TYPE ERROR: TypeError.lubErr (bool anyBool) (int)` on
`ite (foo::bob in foo::bob) (not (… : bool)) (… : int)` — `foo` a normal entity type.

**Cause:** `ActionDescendentOf.refl` was `∀ acts uid, ActionDescendentOf acts uid uid`
— **ungated**, firing for any entity. So `binaryAppMemActionLitTt` typed
`foo::bob in foo::bob` as `.tt`. Functional `typeOfInₑ` only takes the action path
(→ tt) when `actionUID? x₁` holds (foo is an action type); a non-action `e in e` is
generic → `.anyBool`. Chain: relational `.tt` → `iteTt` ignores the else-branch type
→ accepts `bool`-then/`int`-else; functional `.anyBool` → `typeOfIf`-anyBool needs
`Lub(bool,int)` → `lubErr` → rejects. (Also non-deterministic: both
`binaryAppMemActionLitTt` and `binaryAppMemEntitySame` fired for the same expr.)

**Fix:** gate `refl` on the action being in the schema:
`| refl : ∀ acts uid entry, MapContains uid entry acts → ActionDescendentOf acts uid uid`.
Now the tt path fires only for real actions (matching `actionUID?`), and non-action
reflexive `mem` types as `.anyBool` via `binaryAppMemEntitySame` only. See pitfall #9
(syntactic/action-literal dispatch must be guarded).

## 3. action `in` set typed tt/ff without checking set membership (FIXED 2026-07)

**Symptom:** `MISMATCH relational=bool tt functional=bool ff` on
`mem (owner::"doc1") (set [name::d::"doc1"])` where `owner::doc1` is an *action*.

**Cause:** functional `typeOfInₛ` is `if uids.any (acts.descendentOf uid₁ ·) then tt else ff`
— tt requires the set to actually *contain* an ancestor of `uid₁`. The relational
`binaryAppMemActionLitSetTt` required only `ActionDescendentOf acts uid₁ uid₂` for
*some* `uid₂` plus a set whose *element type* is `uid₂.ty` — it never tied `uid₂` to
being an element of the set. So it fired tt whenever the action had *any* ancestor of
a type matching the set's element type, even if that ancestor wasn't in the set. And
`binaryAppMemActionLitSetFf` had *no* guard, so tt/ff overlapped.

**Fix:** added helper `ActionInSet acts uid₁ xs` (some literal element of `xs` is a
descendent-target of `uid₁`; DecOpt uses `acts.descendentOf`). `binaryAppMemActionLitSetTt`
now requires `ActionInSet acts uid₁ xs`; `binaryAppMemActionLitSetFf` requires
`¬ ActionInSet acts uid₁ xs`. Matches functional exactly. Same class as bug #2 (action
`mem` typing over-generalized) — a schema-membership fact matched by *type* instead of
*identity*.

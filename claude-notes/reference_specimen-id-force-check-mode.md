---
name: specimen-id-force-check-mode
description: "Wrap an output var in `id` to force Specimen check-mode (it can't produce an output from under a function application)"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 7b0a8cee-4967-4ee4-83e5-e3101bc6a809
  modified: 2026-07-21T22:26:05.221Z
---

# Forcing a premise into check-mode with `id`

Specimen's mode analysis is **syntactic** and **cannot produce an output from under
a function application**. Wrapping a variable in `id` (e.g. `id x₂`) in a premise
makes that occurrence non-invertible, so Specimen can only *check* it there, never
*generate* it — the variable must then be produced by some other premise.

## When to use

When a variable can be produced by two premises and Specimen picks the "wrong"
(cheap/Total) one, starving the premise you actually want to source it from.

**Concrete case (getTag, 2026-07):** the `getTag`/`hasTagTt` rules draw the tag key
`x₂` from the capability set via `CapTagMem x₁ x₂ c`. But the premise
`HasType x₂ … .string` is a cheap Total string generator, so Specimen's scheduler
bound `x₂` to an **arbitrary string first**, degrading `CapTagMem` to producing only
`x₁` (or a pure check) — so `getTag` was generated ~0 times. The derive trace showed
`ArbitrarySizedSuchThat Expr (fun a => CapTagMem a b c)` (produces x₁ given x₂,c) and
`check CapTagMem x₁ x₂ …`.

**Fix:** write the type premise as `HasType (id x₂) c env .string []`. Now Specimen
can't produce `x₂` under `id`, so `CapTagMem` becomes its sole producer (drawing the
key from `c`) while the string typecheck is still enforced (since `id x₂ ≡ x₂`). This
is preferable to *deleting* the `HasType x₂ .string` premise, which would only be
sound under the invariant that all tag capabilities have string keys.

## Crucial refinement: wrap EVERY operand you want the relation to produce

`id`-wrapping only `x₂` was **not enough** for `getTag`. Its rule also had
`HasType x₁ … (.entity ety)`, and because the requested type fixed `ety` early, the
scheduler produced `x₁` there — demoting `CapTagMem` back to a *check* (only the
`∃ a b`/checker modes were derived, no "given x₁ produce x₂" mode), so the id-wrapped
`x₂` had no producer and `getTag` generated **0** times. `hasTagTt` worked with only
`x₂` wrapped *by luck*: its conclusion type is concrete (`.bool .tt`), so `ety` stayed
existential and `HasType x₁ (.entity ety)` couldn't grab `x₁`.

**Rule:** if you want a membership relation like `CapTagMem x₁ x₂ c` to be the sole
producer of *several* outputs, `id`-wrap **all** of them in their competing premises
(`HasType (id x₁) …` *and* `HasType (id x₂) …`). Any un-wrapped operand that some
other premise can produce will be produced there, collapsing the membership relation
to a check. Verify with the derive trace: you want `[x₁, x₂] ← CapTagMem` (the
`∃ a b` generator mode), not `check CapTagMem x₁ x₂`.

Result (2026-07, string/int probe, n=600): getTag 0 → 28, all 600 passed.

## Related

- [[reference_functional-to-relational-pitfalls]] pitfall #7 (compound constructor
  args) — the sibling problem: there, specialize the relation (e.g. `CapMem x (.tag x₂) c`
  → `CapTagMem x₁ x₂ c`) to lift a buried output to a top-level argument so it can be
  produced at all. The `id` trick is the complement: suppress an *unwanted* producer.
- [[reference_specimen-derive-mutual-syntax]]

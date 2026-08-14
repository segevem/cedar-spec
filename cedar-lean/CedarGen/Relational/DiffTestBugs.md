# Differential Testing Bugs: Relational Spec vs. Functional Typechecker

Bugs found by generating well-typed expressions from the relational spec
(`HasType` in `TypeOfLean.lean`) and cross-checking against the functional
typechecker (`Cedar.Validation.typeOf`).

---

## 1. `or` rules overlap with `orFfThen` (2026-06-25)

**Symptom:**
```
FAIL: or (lit (bool false)) (lit (bool false))
  expected=bool anyBool  got=bool ff

FAIL: or (hasAttr (record []) "b") (binaryApp hasTag (var resource) (lit (string "bar")))
  expected=bool anyBool  got=bool ff
```

"expected" = relational (what the generator targeted), "got" = functional.

**Root cause:**
The relational rules `orAnyTt`, `orAnyFf`, and `orAnyAny` used a free
variable `b₁` for the first operand's bool type:

```
orAnyFf:  x₁ : bool b₁, x₂ : bool .ff → result: bool .anyBool
```

Since `b₁` is unconstrained, the generator could instantiate it with `.ff`,
making `orAnyFf` overlap with `orFfThen` on the same input (`or(ff, ff)`).
The two rules disagree on the output type: `orFfThen` returns `ff`, while
`orAnyFf` returns `anyBool`.

The functional typechecker uses pattern-match priority: `.ff` is caught
before the wildcard `_` branch, so `or(ff, ff)` always returns `ff`.

**Fix:** Restrict `b₁` to `.anyBool` in `orAnyTt`, `orAnyFf`, and
`orAnyAny`, eliminating the overlap:

```
orFfThen:  x₁ : bool .ff,      x₂ : bool b₂       → result: bool b₂
orAnyTt:   x₁ : bool .anyBool, x₂ : bool .tt      → result: bool .tt
orAnyFf:   x₁ : bool .anyBool, x₂ : bool .ff      → result: bool .anyBool
orAnyAny:  x₁ : bool .anyBool, x₂ : bool .anyBool → result: bool .anyBool
```

**Lesson:** When translating a functional definition (with match priority) to
a relational/inductive spec (no priority), every wildcard/catch-all must
exclude the cases already handled by earlier branches. Otherwise the
relational spec is non-deterministic and can produce types the functional
never assigns.

---

## 2. `and` rules overlap with `andShort` (2026-06-25)

**Symptom:**
```
FAIL: and (lit (bool false)) (binaryApp lessEq (lit (int ...)) (lit (int ...)))
  expected=bool anyBool  got=bool ff

FAIL: and (and (lit (bool false)) (lit (bool true))) (unaryApp (like ...) (lit (string "a")))
  expected=bool anyBool  got=bool ff
```

Same class as bug #1 but for `and`. Also manifests transitively: `and(ff, tt)`
types as `ff` in the functional (short-circuit), but generates an intermediate
expression that then feeds into outer `and`/`or` nodes at `anyBool`.

**Root cause:**
The relational rules `andAnyFf`, `andAnyTt`, and `andAnyAny` used a free
variable `b₁` for the first operand's bool type:

```
andAnyTt:  x₁ : bool b₁, x₂ : bool .tt → result: bool b₁
andAnyAny: x₁ : bool b₁, x₂ : bool .anyBool → result: bool .anyBool
```

The functional `typeOfAnd` dispatches `.ff` first (short-circuit, returns `.ff`),
then handles the remaining `.tt` and `.anyBool` cases. When the generator picks
`andAnyAny` with `b₁ = .ff`, it claims the result is `.anyBool`, but the
functional always returns `.ff` for `and(ff, _)`.

**Fix:** Restrict `b₁` to `.anyBool` in `andAnyFf`, `andAnyTt`, and
`andAnyAny`, eliminating the overlap:

```
andShort:  x₁ : bool .ff      → result: bool .ff  (short-circuit)
andTtFf:   x₁ : bool .tt,      x₂ : bool .ff      → result: bool .ff
andTtTt:   x₁ : bool .tt,      x₂ : bool .tt      → result: bool .tt
andTtAny:  x₁ : bool .tt,      x₂ : bool .anyBool → result: bool .anyBool
andAnyFf:  x₁ : bool .anyBool, x₂ : bool .ff      → result: bool .ff
andAnyTt:  x₁ : bool .anyBool, x₂ : bool .tt      → result: bool .anyBool
andAnyAny: x₁ : bool .anyBool, x₂ : bool .anyBool → result: bool .anyBool
```

Note: the functional returns `bool ty₁` for `and(ty₁, tt)`, meaning
`and(anyBool, tt) → anyBool`. The relational `andAnyTt` now correctly
reflects this by hardcoding `.anyBool` as both input and output.

---

## 3. Generic `mem` rules fire for action-literal inputs (2026-06-25)

**Symptom:**
```
BUG (type):
  expr=binaryApp mem (lit (entityUID {Action, "view"})) (lit (entityUID {Action, "view"}))
  expected=bool anyBool  got=bool tt

BUG (type):
  expr=binaryApp mem (lit (entityUID {Action, "view"})) (set [lit (entityUID {Action, "view"})])
  expected=bool anyBool  got=bool tt
```

**Root cause:**
The functional `typeOfInₑ`/`typeOfInₛ` checks whether `x₁` is an action-schema
literal and `x₂` is an entity literal (or set of entity literals) FIRST. When
both conditions hold, it uses action-hierarchy logic which yields `.tt` (via
`ActionSchema.descendentOf` refl) or `.ff`. Only when the action-literal check
fails does it fall through to the entity-type hierarchy (yielding `.anyBool`
or `.ff`).

The relational generic `mem` rules (`binaryAppMemEntityEntity`,
`binaryAppMemEntitySame`, `binaryAppMemEntitySet`, `binaryAppMemEntitySetSame`,
`binaryAppMemEntityEntityFf`, `binaryAppMemEntitySetFf`) had no guard excluding
action-literal inputs. So the generator could pick a generic rule for an
action-literal `mem`, producing `.anyBool` where the functional returns `.tt`.

**Fix:**
1. Added `IsActionLitMem` and `IsActionLitMemSet` predicates with `DecOpt`
   instances that mirror the functional's `actionUID?`/`entityUID?`/`entityUIDs?`
   checks.
2. Added `¬ IsActionLitMem x₁ x₂ acts` guards to all generic entity-entity
   `mem` rules and `¬ IsActionLitMemSet x₁ x₂ acts` guards to all generic
   entity-set `mem` rules.
3. Added `binaryAppMemActionLitSetTt` and `binaryAppMemActionLitSetFf` rules
   for the set case (matching the existing entity-entity action-literal rules).

**Lesson:** When the functional dispatches on the *syntactic form* of
expressions (e.g., "is this a literal?") before dispatching on types, the
relational spec must add explicit guards excluding those syntactic forms from
the generic rules. Pattern-match priority in the functional silently ensures
mutual exclusion; the relational doesn't have that luxury.

---

# Generation non-termination bugs

The bugs below are *not* type-correctness mismatches — the rules assigned the
right types. Instead they made Specimen's *derived generator/checker* diverge
(hang) at larger sizes, because a premise variable was drawn from an **unbounded
domain**. The `budget-aware` strategy exposed them (it selects the affected
constructors); `steep` masked them by down-weighting those constructors.

**Diagnostic method (for future hangs):** attach `eu-stack -p <pid>` to the
hung worker. A hang shows a repeating
`lazyListBacktrackOpt → roundRobinConcat → append → mapLazyList` cycle (an
infinite lazy enumeration) under a `HasType___lam__N` frame. Map `lam__N` (and
its hygiene scope, e.g. `_hyg_307`) to a constructor by reading its body in the
generated C (`.lake/build/ir/.../Variants/BudgetAware.c`): the `lean_obj_tag`
checks reveal the matched `Expr` constructor, and the enumerator closure reveals
the offending relation. Cross-reference the `specimen.textOutput` schedule dump
(printed at derive time) — a `[x] ← Relation` binding means the checker
*enumerates* `x`; if that domain is unbounded (`Name`/`CedarType`/`RecordType`),
it diverges.

## 4. Free entity-type operands enumerate `EntityType = Name` unbounded (2026-07-28)

**Symptom:** `budget-aware` `lean-typeof` at size ≥ 12 hangs (0 valid/sec, one
worker pinned at 100% CPU). `steep` runs fine.

**Root cause:** Rules whose operands have an *intermediate* entity type — e.g.
`is`, entity `eq`, and the generic `mem` rules — carried a free `ety` that
appears only in an operand premise `HasType x (.entity ety)`, never in the
conclusion's expression or target type. When such a rule's **checker** runs
(and the derived `HasType` checker is invoked recursively all over generation),
`ety` is an existential the checker must *enumerate* — over `Enum EntityType`,
i.e. `Enum Name`, an infinite domain. It never terminates.

**Fix:** Added a `ValidEntityType ety ets acts` helper (`ety` is a key of the
entity schema `ets`, or the type of some action in `acts`) and used it as the
first premise of these rules, giving the checker a **finite** producer (a walk
of the schema) instead of `Enum Name`. This is *implied* by the operand
typecheck under a well-formed env (the only producers of `.entity ety` are
entity literals — themselves `ValidEntityUID`-guarded — request-type variables,
and schema-derived attribute accesses), so it rejects nothing `typeOf` accepts.

**Faithfulness note:** an earlier attempt used the existing `ValidEntityUID`,
which requires the type to be *inhabited*. That **overconstrains**: `typeOf`
accepts `x is T` / entity `eq` / `mem` for any *declared* type `T`, including an
empty `enum` entity type (which has no inhabitant). `ValidEntityType` drops the
inhabitant requirement to match `typeOf` exactly.

**Refinement (positive `mem`):** for `binaryAppMemEntityEntity` /
`binaryAppMemEntitySet`, only `ety₁` is pinned with `ValidEntityType`;
`DescendentOf ets acts ety₁ ety₂` then *produces* `ety₂` (via its
`ancestor`/`refl` constructors), yielding exactly the valid descendents rather
than enumerating all schema types and filtering — cheaper and cleaner. The
false (`…Ff`) rules keep `ValidEntityType ety₂`, since `NotDescendentOf` produces
only `ety₁`, not `ety₂`.

## 5. `GetAttrInRecord`'s phantom receiver type enumerates all of `CedarType` (2026-07-28)

**Symptom:** after fix #4, `budget-aware` still hangs at size ≥ 12; `eu-stack`
points at the `getAttr`-on-entity checker enumerating via `GetAttrInRecord`.

**Root cause:** `GetAttrInRecord` carried a leading `CedarType` argument (the
receiver type) that mirrors the functional `getAttrInRecord`, where it is used
*only* to build the `.attrNotFound ty a` error message. The relation models no
error case, so that argument was a **phantom** — bound but never used in either
constructor. When the checker scheduled `GetAttrInRecord` to produce a result,
it enumerated the phantom over *all* of `CedarType` (an infinite recursive
domain: `set (set …)`, `entity <any Name>`, …), filtering with a later
`match … with entity ety` that never terminates.

**Fix:** removed the phantom first argument from `GetAttrInRecord` entirely
(definition + both use sites `getAttrRecord`/`getAttrEntity`). This deletes the
enumeration at its source.

## 6. Record type `rty` drawn from the attr relation instead of the schema (2026-07-28)

**Symptom:** after fix #5, `budget-aware` runs fast for ~12 s then a *rarer*
seed hangs; `eu-stack` points at the `getAttr`-on-record checker enumerating
`GetAttrInRecord`.

**Root cause:** in the attribute rules the record type `rty` appears in two
premises — the schema/inference source (`MapContainsAttrs ety rty ets` for the
entity case, `HasType x₁ (.record rty)` for the record case) and the
`(Has/Get)AttrInRecord` / `MapNotContainsKey` premise. The scheduler is free to
*produce* `rty` from the latter, which enumerates record types over `Enum Map`
(unbounded — arbitrary attribute lists) rather than walking the finite schema.

**Fix:** wrapped `rty` in `id` inside the `(Has/Get)AttrInRecord` /
`MapNotContainsKey` premise of all six attr rules
(`hasAttrRecord`, `hasAttrRecordNotFound`, `getAttrRecord`,
`hasAttrEntity`, `hasAttrEntityNotFound`, `getAttrEntity`). `id rty` is
definitionally `rty` (so the check is unchanged and sound) but prevents Specimen
from *producing* `rty` at that position, forcing it to come from the finite
source: `MapContainsAttrs` (schema walk) for entity attrs, or the record-type
inference `HasType x₁ (.record rty)` for record attrs. Same `id`-trick already
used for the tag operands in `getTag`/`hasTagTt`.

**Lesson (bugs #4–6):** in a relational spec compiled by Specimen, a premise
variable that is not pinned by the conclusion or by a finite relation becomes an
*enumerated existential* in the derived checker. If its type is unbounded
(`Name`, `CedarType`, `Map`/`RecordType`), generation diverges. Pin every such
variable to a finite, schema-derived producer — via a dedicated relation
(`ValidEntityType`), by deleting a phantom argument, or by `id`-wrapping the
positions that must stay check-only.

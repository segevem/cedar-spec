---
name: functional-to-relational-pitfalls
description: "Pitfalls when converting Cedar's functional typechecker to a relational (inductive) specification for Specimen generators"
metadata: 
  node_type: memory
  type: reference
  originSessionId: ff372413-d48e-4aed-97ea-673cb1595dcf
---

# Converting Functions to Relations: Pitfalls Reference

When converting a functional definition (like `typeOf` in `Cedar/Validation/Typechecker.lean`) to a relational/inductive specification (like `HasType` in `CedarGen/Relational/TypeOfLean.lean`) for use with Specimen's `derive_mutual`, the following issues arise repeatedly.

## 1. Shortcut rules must still validate subexpressions

**Problem:** A functional typechecker computes bottom-up — it typechecks subexpressions first, and only reaches a shortcut (like literal-equality comparison) after all children pass. A relational rule that pattern-matches on syntax can skip validating children entirely.

**Example:** The functional `typeOfEq` calls `typeOfLit` on each literal before comparing them. `typeOfLit` enforces `isValidEntityUID`. The naive relational translation:
```lean
| binaryAppEqLitSame : ∀ p c env,
    HasType (.binaryApp .eq (.lit p) (.lit p)) c env (.bool .tt) []
```
...never checks that the entity UID in `p` is valid, producing expressions the functional version rejects with `unknownEntity`.

**Fix:** Add `HasType (.lit p) c env ty []` premises for every subexpression that the functional version typechecks before reaching the shortcut:
```lean
| binaryAppEqLitSame : ∀ p c env ty,
    HasType (.lit p) c env ty [] →
    HasType (.binaryApp .eq (.lit p) (.lit p)) c env (.bool .tt) []
```

**General rule:** If the function `f(x)` calls `g(x.child)` and can fail there, the relation must include a premise `G x.child ...` even when the conclusion pattern-matches `x.child` directly.

## 2. Side conditions that are implicit in pattern matching

**Problem:** A functional `match` branch is only reached when earlier branches fail. A relation has no fall-through — each constructor fires independently.

**Example:** `typeOfEq` has two branches: literal-vs-literal, and "everything else". The relational `binaryAppEqNonLitLub` rule must add `¬ BothLit x₁ x₂` to avoid overlap with the literal rules. Without it, an expression could satisfy multiple rules that produce different types.

**General rule:** When the function uses a catch-all or fall-through branch, the corresponding relational rule needs explicit negation of the earlier cases (or use a `DecOpt` guard).

## 3. Environment threading vs. explicit destructuring

**Problem:** The functional version passes `env : TypeEnv` opaquely to recursive calls. A relational rule that destructures `env` into `⟨ets, acts, reqty⟩` for one premise must use the *same* destructuring for all premises that share the environment.

**General rule:** If one premise needs fields from `env`, destructure in the quantifier and use the struct literal `⟨ets, acts, reqty⟩` everywhere in that rule. Don't mix opaque `env` with field access.

## 4. Schema lookups produce witnesses, not booleans

**Problem:** The function calls `env.ets.find? ety` and branches on `some`/`none`. The relation needs a `MapContains` witness for the `some` case — and the *value* found matters (e.g., `.standard entry` vs `.enum eids`).

**General rule:** Every `find?`/`contains` in the function becomes a `MapContains`/`SetContains` premise in the relation. Include the found value in the premise so downstream premises can use it.

## 5. Capability merging is not union

**Problem:** `CapMerge c₁ c₂ c` is relational — it can interleave, and `c` is an output. If you accidentally constrain `c` in the conclusion (e.g., `cout = c₁ ++ c₂`), the generator can't find witnesses.

**General rule:** Leave merged capabilities as free output parameters; let `CapMerge` produce them.

## 6. Lub is partial — the relation must handle the failure case

**Problem:** `t₁ ⊔ t₂` returns `Option CedarType` in the function. The relation `Lub t₁ t₂ lubTy` only covers the `some` case. If you need to model the `none` case (types are incompatible), you need a separate rule or a `¬ ∃ t, Lub t₁ t₂ t` premise.

**General rule:** Check whether the function branches on `some`/`none` from `lub` and make sure you have relational coverage for both paths if both are reachable.

## 7. Compound constructor arguments mix bound and fresh variables (Specimen scheduling)

**Problem:** Specimen schedules each variable in a premise as either fully-input (already bound) or fully-output (fresh). When a compound constructor term in a premise contains a *mix* of bound and fresh variables, Specimen can't treat it as either input or output and refuses to schedule the premise.

**Example:** A rule needs to look up an entity's record type from the schema:
```lean
| getAttrEntity : ∀ ... ancs rty tags,
    MapContains ety (.standard ⟨ancs, rty, tags⟩) ets →
    ...
```
Here `ety` and `ets` are bound (inputs), but `ancs`, `rty`, `tags` are fresh (outputs). They all appear inside one compound term (`.standard ⟨ancs, rty, tags⟩`) that is an argument to `MapContains`. Specimen can't partially destructure this — it needs to either *build* the term (all parts input) or *receive* it (the whole term is one output variable). The mix is rejected.

**Fix:** Create a specialized map-lookup inductive that lifts the needed field(s) to top-level arguments, hiding the rest as universally quantified wildcards inside the constructor:
```lean
inductive MapContainsAttrs : EntityType → RecordType → EntitySchema → Prop where
  | here : ∀ ety ancs attrs tags rest,
    MapContainsAttrs ety attrs (.mk ((ety, .standard ⟨ancs, attrs, tags⟩) :: rest))
  | there : ∀ ety attrs k' v' rest,
    MapContainsAttrs ety attrs (.mk rest) →
    MapContainsAttrs ety attrs (.mk ((k', v') :: rest))
```
Then in the rule: `MapContainsAttrs ety rty ets →`. Now `ety` is input (bound from conclusion), `ets` is input, and `rty` is the sole output — all at top-level argument positions.

**When you need different fields from the same entry,** make separate helpers for each:
- `MapContainsAncestors` — extracts `Set EntityType` ancestors
- `MapContainsAttrs` — extracts `RecordType` attributes
- `MapContainsTagType` — extracts `CedarType` from `.some ty` tags
- `MapContainsNoTags` — matches entries with `.none` tags (no output needed beyond existence)

**General rule:** If a `MapContains` (or similar) premise has a value argument containing *both* already-bound variables and fresh variables inside constructors, split into: (1) a specialized lookup that exposes only the needed field(s) at argument position, or (2) a two-step pattern where `MapContains` extracts an opaque `entry` output, then a separate `IsStandardEntry entry ancs rty tags` destructures it.

## 8. Wildcards in non-first branches must exclude all earlier-matched cases

**Problem:** A functional `match` expression like:
```
match x₁.typeOf with
| .bool .tt  => ...  -- branch A
| .bool .ff  => ...  -- branch B
| .bool _    => ...  -- branch C (wildcard — only reaches .anyBool)
```
The wildcard `_` in branch C only fires for `.anyBool` because `.tt` and `.ff`
are already consumed. In the relational translation, if you write C's rule with
a free variable `b₁`:
```lean
| ruleC : ∀ ... b₁ ..., HasType x₁ c env (.bool b₁) c₁ → ...
```
then `b₁` can be instantiated to `.ff`, making ruleC overlap with ruleB on the
same input — and they may produce different outputs.

**Fix:** Replace free `b₁` with the concrete value that the wildcard actually
covers. If `.tt` and `.ff` are handled above, use `.anyBool` directly:
```lean
| ruleC : ∀ ..., HasType x₁ c env (.bool .anyBool) c₁ → ...
```

**General rule:** For every wildcard/variable in a non-first match branch,
enumerate what values it can actually take (after subtracting earlier patterns)
and hardcode those. If only one remains, use it directly. If multiple remain,
create separate constructors for each, or use a `BoolTypeNeq`-style exclusion
predicate.

**Real-world example (2026-06-25):** The `and`/`or` rules in `TypeOfLean.lean`
used free `b₁` in `andAnyFf`/`andAnyTt`/`andAnyAny` and `orAnyTt`/`orAnyFf`/
`orAnyAny`. With `b₁ = .ff`, these overlapped with `andShort`/`orFfThen` and
produced different types. Fix: restrict to `.anyBool`.

## 9. Syntactic dispatch (expression-form checks) must become explicit guards

**Problem:** The functional may dispatch on the *syntactic form* of an
expression before dispatching on its type. For example:
```
match actionUID? x₁ env.acts, entityUID? x₂ with
| .some uid₁, .some uid₂ => ...  -- action-literal path
| _, _                    => ...  -- generic path
```
The generic path only fires when the action-literal check fails. In the
relational spec, the "generic" rules have no such guard and can fire for any
input — including action literals.

**Fix:** Define a predicate that captures the syntactic condition, give it a
`DecOpt` instance, and add `¬ P` as a premise to the generic rules:
```lean
inductive IsActionLitMem : Expr → Expr → ActionSchema → Prop where
  | mk : ∀ uid₁ uid₂ acts entry,
    MapContains uid₁ entry acts →
    IsActionLitMem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂)) acts

instance : DecOpt (IsActionLitMem x₁ x₂ acts) where ...

| binaryAppMemEntityEntity : ...
    ¬ IsActionLitMem x₁ x₂ acts →  -- exclude action-literal inputs
    ...
```

**General rule:** Whenever the function checks something about the *shape* of
an expression (is it a literal? is it a set of literals? is it a specific
variable?) before falling through to type-based logic, the relational spec
needs an explicit `¬ IsShape ...` guard on the fallback rules. Without it,
the relational spec is non-deterministic and can assign different types to
the same expression depending on which rule the generator picks.

**Real-world example (2026-06-25):** `typeOfInₑ`/`typeOfInₛ` check
`actionUID? x₁` and `entityUID? x₂`/`entityUIDs? x₂` before falling through
to entity-type hierarchy. The relational generic `mem` rules had no such guard,
producing `.anyBool` where the functional returned `.tt` via action-hierarchy
refl.

## Quick checklist for each function → relation conversion

- [ ] Every recursive call in the function body becomes a `HasType` premise
- [ ] Every `find?`/`contains` becomes a `MapContains`/`SetContains` premise
- [ ] Every boolean guard becomes either a premise or a `¬ P` guard
- [ ] Shortcut rules (pattern-matching on subexpression syntax) still validate those subexpressions
- [ ] Fall-through/catch-all branches get explicit negation of earlier patterns
- [ ] **Wildcards in non-first branches** — hardcode the residual values, don't leave as free variables
- [ ] **Syntactic dispatch** — if the function checks expression shape before types, add `¬ IsShape` guards to generic rules
- [ ] Output parameters (capabilities, lub types) are existentially quantified, not hardcoded
- [ ] No compound constructor args mixing bound and fresh vars — split into specialized lookups or two-step extract+destructure

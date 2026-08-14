---
name: relational-action-type-soundness-gap
description: "Why validation-drt aborts on Specimen inputs: relational WfActionEntry generates non-Action-typed action UIDs (generator gap, not a typechecker bug)"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 01c084b2-8df7-4bc5-913e-f57d20956638
  modified: 2026-07-29T21:03:09.507Z
---

On the `validation-drt` (differential) target, the Specimen `lean-schema-typeof`
generators (steep-tags / typeof-check / budget-aware) trigger an **immediate
Rust/Lean validation mismatch** and the DRT panics (`cedar-drt/src/tests.rs:238`).
The handwritten `type-directed` generator does NOT (it runs clean).

**Root cause — a generator soundness gap, NOT a typechecker bug.** Verified 2026-07-29
by running cedar-policy directly (`Schema::from_cedarschema_str`/`from_json_str` +
`Validator::validate`, Strict):
- `Action::"a" in Action::"a"`, `action == Action::"a"`, `C::"x" in C::"x"`,
  `NS::Action::"doc1" in NS::Action::"doc1"` all **pass** in cedar-policy — matching Lean.
- Only an undeclared/reserved-mismatched type (`Bogus::"x"`, or the generated
  `name::"doc1"`) is rejected ("unrecognized entity type"). So **Rust and Lean agree on
  every schema cedar-policy can actually build.**
- **Decisive:** declaring an action `doc1` via JSON (`Schema::from_json_str`) yields action
  UID `Action::"doc1"` (namespaced: `NS::Action::"doc1"`). There is **no** cedar-policy
  schema API (Cedar-syntax or JSON) that produces a `name`-typed action. The generated
  `name::"doc1"` action is not a constructible Cedar schema — it only exists because the
  relational `TypeEnv`→protobuf path injects an arbitrary-typed action UID.

To reproduce & inspect: `tests.rs::schema_debug_repr` (added 2026-07-29) logs
`entity_types` / `actions` / `action_groups` at the mismatch panic. The failing input:
entity_types `["c::c","id::d"]`, action `"name::\"doc1\""`, policy
`... name::"doc1" in name::"doc1" ...`.

The divergence:
- Relational `WfActionEntry.mk` (`CedarGen/Relational/Schema.lean:154`) takes the action
  `uid : EntityUID` as a **free var with no constraint on its entity type** → Specimen
  emits actions like `name::"doc1"`. Real Cedar reserves the `Action` type for every
  action UID (cedar-policy's own generator hardcodes `EntityType::from_normalized_str("Action")`,
  `cedar-policy-generators/src/schema.rs:300`). A `name`-typed action isn't expressible in
  Cedar syntax; it only reaches cedar-policy because the generated `TypeEnv` is serialized
  straight to protobuf, bypassing the Action-type invariant.
- Lean functional validator accepts references to it: `Cedar/Validation/Typechecker.lean:63-64`
  types an entity-UID literal as valid when `env.ets.isValidEntityUID uid || env.acts.contains uid`
  (the `acts.contains` branch ignores the type name), and `ActionSchema.actionType?`
  (`Types.lean:176`) derives "action types" from the actual action set — so `name` counts.
- cedar-policy resolves the literal's type `name` against declared entity types + the
  canonical `Action` type, doesn't find it → rejects.

**Fix (generator-side):** constrain `WfActionEntry`'s action `uid` so its entity type is
the reserved `Action` type (all actions share type `Action`, distinct eids — exactly how
Cedar works). Then generated schemas stay in the well-formed Cedar space and validation-drt
stops mismatching. (Optionally the Lean spec could also enforce the Action-type invariant,
but that's a modeling choice — it doesn't affect agreement on valid inputs.)

See [[functional-to-relational-pitfalls]], [[experiment-harness-pitfalls]], [[experimentation-plan]].

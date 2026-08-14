---
name: reference_enum-hierarchy-drt-mismatch
description: "validation-drt \"Lean accepts/Rust rejects\" mismatches root-caused to enum entity types carrying hierarchy edges"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 01c084b2-8df7-4bc5-913e-f57d20956638
  modified: 2026-08-03T15:18:16.547Z
---

The 14 validation-drt mismatches in run-1h-20reps-v2 (families: attribute-on-entity,
`context.attr`, `getTag`-without-`hasTag`) all reduce to ONE root cause. Every failing
access is on an **enum** entity type behind an `in`-guard.

**Mechanism** (confirmed by running both validators on the isolated proto via
`cedar-drt/coverage/src/bin/probe_bug.rs`): the generated schema has an enum entity as a
hierarchy descendant (e.g. `id::foo.descendants = {owner}`, `owner` enum). Then
`principal in id::foo::"bar"` is statically-false in Lean but not in Rust:
- Rust proto-decode keeps the edge (`new_enum(name, descendants, …)`) → `in` = anyBool →
  typechecks `principal.b` on `owner` (no attrs) → **rejects**.
- Lean models enums with NO ancestors (`Cedar/Validation/Types.lean:123` enum variant has no
  ancestors field; `:139` `.ancestors | .enum _ => ∅`; `CedarProto/Schema.lean:106` `toSchema`
  builds `.enum decl.enums` discarding the ancestorMap) → `descendentOf enum X = false` →
  `typeOfInₑ` returns `.ff` → `typeOfAnd`/`typeOfIf` short-circuit and DROP the error
  (`Typechecker.lean:96`,`82`) → **accepts**. The `getTag` cap rule (`typeOfGetTag`
  `Typechecker.lean:197`) is correct but never reached.

**Direction / who's buggy:** NOT the Lean or Rust typechecker rules, and NOT env enumeration
(bare `principal.b` without the guard: Lean correctly rejects). It's a malformed-input
divergence. Enum entity types cannot participate in the hierarchy in valid Cedar
(`validator/schema/namespace_def.rs:487` enum parents = `iter::empty()`; `entity_type.rs:48`
"always empty"), so `id::foo.descendants ∋ owner` is unrepresentable in source. The generator
(`generateSchemaTypeOfProto` / relational `WfTypeEnv`) emits enum entities with hierarchy edges
over proto. Rust's proto `ValidatorSchema` decode doesn't enforce the enum invariant (keeps the
edge); Lean drops it. Same class as [[reference_relational-action-type-soundness-gap]] (generator
emits schemas outside the valid-Cedar domain). Curated as Bug 2 in
`cedar-lean/CedarGen/Relational/DRT_MISMATCHES.md`. Fix options: (a) generator: don't emit
memberOf/descendant edges for enum types; (b) Rust proto-decode: reject enum types with
descendants. Distinct from [[reference_typeof-check-capmerge-generator-hang]] (a liveness bug).

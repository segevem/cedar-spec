# validation-drt mismatches (Specimen `lean-schema-typeof`)

Real Rust/Lean disagreements that abort the differential `validation-drt`
target. Each is an out-of-spec input from the generator/encoding; the validators
agree on all valid inputs. Target aborts on the first mismatch, so found one at
a time. Crash logs schema+policy via `cedar-drt/src/tests.rs::schema_debug_repr`.

---

## Bug 1 — action UID type not pinned to reserved `Action`   ✅ FIXED

- **Target:** `validation-drt`, `lean-schema-typeof --strategy typeof-check --lean-size 12`, seed 0.
- **Policy:** `permit(principal, action, resource) when { ((name::"doc1" in name::"doc1") && ("baz" like "\u{6}\\**\u{7}B*b")) && (!((ip("192.145.235.130/17")).isIpv6())) };`
- **Schema:** `entity_types: ["c::c","id::d"]`, `actions: ["name::\"doc1\""]`, `action_groups: []`. The action `name::"doc1"` has entity type `name` (not a declared entity type, not `Action`).
- **Rust:** `× for policy \`policy0\`, unrecognized entity type \`name\`; did you mean \`c::c\`?`
- **Lean:** `errors: []` (accepts).
- **Explanation:** both are typing the entity literal `name::"doc1"`.
  - *Rust:* checks the literal's type `name` against declared entity types (`c::c`, `id::d`) plus the reserved `Action` type → not found → rejects.
  - *Lean:* (`Typechecker.lean:63-64`) accepts a UID literal if `env.ets.isValidEntityUID uid || env.acts.contains uid` — `name::"doc1"` is in the action set, so it passes regardless of the type name.
  - On a valid `Action`-typed action both take their accept path and agree.
- **Root cause:** `Schema.lean` `WfActionEntry.mk` left the action `uid` type free. Fixed by pinning to `actionEntityType = {id:="Action", path:=[]}`.
- **Note:** distinctness now rests on `eid`; `canonicalizeEnv` dedups, so correctness is fine — only action diversity drops on eid collisions.

---

## Bug 2 — enum entity types carry hierarchy edges; Lean drops them, Rust keeps them

Covers all 14 mismatches in `run-1h-20reps-v2` (families: attribute-on-entity, `context.attr`, `getTag`-without-`hasTag`). Every failing access is on an **enum** entity type sitting behind an `in`-guard.

- **Target:** `validation-drt`, `lean-schema-typeof` (`steep-tags`/`typeof-check`, sz12 & sz20). Representative: `steep-tags-sz20`, seed 4000449200 (viol_447971).
- **Policy:** `permit(principal, action, resource) when { (principal in id::foo::"bar") && (principal.b) };`
- **Schema:** `entity id::foo { b: ipaddr, id } ` with **`descendants = {owner}`**; `entity owner enum [a,b,…]` (no attrs); `action "owner"` `principal ∈ {owner, id::foo}`, `resource {owner}`.
- **Rust:** `× for policy \`policy0\`, attribute \`b\` on entity type \`owner\` not found` (rejects).
- **Lean:** `Ok(())` (accepts). *(Confirmed by running both on the isolated proto; bare `principal.b` without the `in`-guard, Lean correctly rejects with `attrNotFound` — so it enumerates the `principal=owner` env; the acceptance is caused by the `in`-guard, not env enumeration.)*
- **Explanation:** the guarded access errors iff `principal in id::foo::"bar"` is not statically false.
  - *Rust:* proto decode keeps `id::foo.descendants = {owner}` (`new_enum(name, descendants, …)`), so `any_entity_type_decedent_of(owner, id::foo)` is true → `in` typed `anyBool` → typechecks `principal.b` on `owner` (no attrs) → rejects.
  - *Lean:* `EntitySchemaEntry.enum` (`Types.lean:123`) has **no `ancestors`**, and `.ancestors` returns `∅` for enums (`Types.lean:139`); `Proto/Schema.lean::toSchema` builds `.enum decl.enums` and **discards the `ancestorMap`** for enum decls (`Schema.lean:106`). So `TypeEnv.descendentOf owner id::foo = owner.ancestors.contains id::foo = false` → `typeOfInₑ` returns `.bool .ff` → `typeOfAnd`/`typeOfIf` short-circuit on the false guard and **drop the `principal.b` type error** (`Typechecker.lean:96`, `82`) → accepts. The `getTag`/`context.attr` cases are identical (the correct `typeOfGetTag` cap check at `Typechecker.lean:197` is simply never reached).
- **Root cause:** the generated schema is **not well-formed Cedar** — enum entity types cannot participate in the hierarchy (`validator/schema/namespace_def.rs:487` gives an enum's parents as `iter::empty()`; `entity_type.rs:48` "always empty"), so `id::foo.descendants ∋ owner` (which requires `owner memberOf id::foo`) is unrepresentable in source. The generator (`generateSchemaTypeOfProto` / relational `WfTypeEnv`) emits enum entities with hierarchy edges directly over proto. On that out-of-domain input the two diverge: Rust's proto `ValidatorSchema` decode preserves the enum→hierarchy edge without enforcing the enum invariant; Lean's decode drops it (matching Cedar's "enums have no ancestors"). Same class as Bug 1 (generator emits schemas outside the valid-Cedar domain).

---
name: typeof-error-spec
description: "Relational spec of Cedar VALIDATION errors (ErrorExpr augmenting HasType) for generating ill-typed policies; Phase 1 sound+faithful"
metadata:
  node_type: memory
  type: project
  originSessionId: 60db3c98-5034-4030-861c-4468d8c04ec7
  modified: 2026-08-10T20:43:26.210Z
---

# TypeOfError: relational spec of Cedar validation errors (augments HasType)

Goal: generate ill-typed policies that trigger each Cedar VALIDATOR error, faithfully, for
coverage of Rust validator error paths (and DRT). Target is the VALIDATOR
(`Cedar/Validation/Validator.lean` `validate`/`typecheckPolicyWithEnvironments`), NOT bare
`typeOf`. See [[functional-to-relational-pitfalls]], [[specimen-vs-hw-coverage-findings]].

## Key design (works — Phase 1 proven sound+faithful 2026-08-10)
- **Do NOT change `HasType`'s type.** Add a SIBLING relation
  `ErrorExpr : Capabilities → TypeEnv → Expr → VErrKind → Prop` (mutual-capable with HasType).
  Together they are the graph of `typeOf` (+ validator wrapper): HasType = ok path, ErrorExpr
  = error path. `VErrKind` mirrors `validationErrorToJson` (the LOSSY kind the DRT compares —
  so we match the error KIND, not the `TypeError` payload; big simplifier).
- **Single isolated defect over an entity-clean, well-typed frame** ⇒ error kind unambiguous
  regardless of the validator's pass order (checkEntities-first vs typeOf vs bool-check vs
  impossible). Phase 1 keeps defects on ENV-INDEPENDENT constants so the kind is identical
  under every environment of the schema.
- Validator error sources layered over typeOf: (1) `checkEntities` EAGER whole-tree pre-pass
  → `unknownEntity`, runs FIRST so it preempts everything; (2) `typeOf` short-circuit single
  error; (3) non-bool result → `unexpectedType`; (4) all-false under every env →
  `impossiblePolicy`.

## Files (working-tree, uncommitted)
- `cedar-lean/CedarGen/Relational/TypeOfError.lean` — `VErrKind`, `EntityTypeUndeclared`
  (faithful inductive + DecOpt = `!ets.contains ety && !acts.actionType? ety`), `NonBoolConst`
  (int/string/set-int literals), `ErrorExpr` — Phase 1+2 = 10 ctors covering ALL 9 validator
  error kinds: unknownEntityLit / unknownEntityIs (unknownEntity), emptySet (emptySetErr),
  nonBool (unexpectedType), falseLit (impossiblePolicy), attrNotFound (`getAttr {} a`),
  tagNotFound (`getTag Foo::"e" "t"` via `MapContainsAttrs` = standard entity in ets),
  lubErr (`[i] == "s"`), incompatibleSetTypes (`[i, "s"]`), extensionErr (`decimal(i)`).
  All ENV-INDEPENDENT constants/valid-literals. namespace `CedarGen.Relational.Lean`.
- `cedar-lean/CedarGen/Relational/PolicyGenError.lean` — `IllTypedPolicy` (mirrors
  `WellTypedPolicy`: same WellTyped*Scope + a single `when` body = `ErrorExpr`; pid/effect
  hardcoded "p0"/.permit), derives `generator (fun env => ∃ p, IllTypedPolicy env p)` (opens
  `Variant.BudgetAware`), `generateErrorPolicies` FFI-style entry, `errKind` projection.
- `cedar-lean/CedarGen/Relational/PolicyGenErrorTest.lean` — self-checks over
  `generateSchemaOnly` schemas (NOT testEnv). Build: `lake build
  CedarGen.Relational.PolicyGenErrorTest` (~4min, SchemaTest pulls many variants).

## Results — Phase 1+2 (2026-08-10, 20 generated schemas, 2–11 envs each)
- TEST A (real generator, all 9 kinds): **400 rejected, 0 accepted** (sound).
- TEST B (faithfulness, predicted VErrKind vs validator kind, .any scopes, all 9 kinds):
  **400 match, 0 mismatch** — faithful even under multi-env.
- Phase 1+2 cover the COMPLETE standard-`validate` error surface: all 8 `TypeError` kinds
  (lubErr, unexpectedType, attrNotFound, tagNotFound, unknownEntity, extensionErr, emptySetErr,
  incompatibleSetTypes) + impossiblePolicy. Only `levelError` (needs `validateWithLevel`) is
  out of scope.
- CONFIRMED representative: the Rust coverage harness validates with
  `Validator::new(schema).validate(&policies, Strict)` over the full decoded schema
  (`cedar-drt/coverage/src/main.rs:338,469`) — same multi-env `validate` as the self-check.

## Gotchas learned
- `testEnv` (TypeOfLeanBase) has **0 `Schema.environments`** (actions have empty applies-to
  sets) ⇒ `validate`'s `allFalse []` is vacuously true ⇒ EVERYTHING not caught by
  checkEntities collapses to `impossiblePolicy`, and typeOf never runs. ALWAYS self-check
  against `generateSchemaOnly` schemas (2–11 envs), which is what the real corpus validates.
- `validate` builds environments from `schema.acts` cross-product (`Schema.environments`), NOT
  from the single reqty the generator used → multi-env is REAL; Phase 1 env-independent
  constants stay faithful across all of them (each yields only its intended kind or benign
  ok/ff; the generated env never short-circuits its own well-typed scope).
- `Schema = {ets, acts}`; build from a TypeEnv via `⟨env.ets, env.acts⟩`.
- `generateSchemaOnly` is ROOT namespace (no `CedarGen...` prefix); returns `IO (Option
  TypeEnv)` — annotate the bind `let r : Option TypeEnv ← ...`. `Map` length = `.size`.
- `DecOpt.decOpt : Nat → Except GenError Bool`, return `.ok bool`.

## Phase 3 DONE — faithful RECONSTRUCTION of propagation (not a mutator). 2026-08-10
User steer: "the problem with the mutator idea as opposed to faithfully reconstructing the error
semantics." Correct — the first Phase-3 attempt was a MUTATOR (`ErrorCtx` wrappers that nest an
error leaf in constant contexts) and it FAILED because wrapping assumes error-PRESERVATION, a
per-wrapper×per-kind argument that broke: `impossiblePolicy`/`unexpectedType` aren't typeOf errors
(`false`/`1` are well-typed), so `!false` → a VALID policy, `[false]`/`false+0` → wrong kind.
REVERTED it. Replaced with the faithful reconstruction:
- `TypeErr c env x k` mirrors `typeOf`'s recursion: `leaf` (an `ErrorExpr`) + propagation rules,
  each forwarding a sub-term's error through a position `typeOf` FORCES (short-circuit order +
  branch laziness: `andR`=`true && e`, `orR`=`false || e`, `iteThen`/`iteElse` per literal guard,
  `binL`/`binR`, `getAttr`/`hasAttr`, `setSingleton`, `unaryNot/Neg/IsEmpty`). Correct by
  construction — no preservation lemma. Recursive ⇒ arbitrary depth (Specimen `size`-bounded).
- `PolicyBodyErr` = `TypeErr` (nested) ∪ top-level-only `nonBool`→unexpectedType ∪ `impossible`
  (`false`)→impossiblePolicy. Separating the two validator/policy-level properties (NOT typeOf
  errors) from the propagatable typeOf errors is what the mutator wrongly conflated.
- `ErrorExpr` is now the LEAF true-typeOf/checkEntities errors only (removed nonBool/falseLit;
  added `unexpectedAdd`/`unexpectedNot` as genuine op-errors). `IllTypedPolicy` body uses
  `PolicyBodyErr`.
- 2nd bug the faithful framing surfaced (same class as the reverted `setHead`): FREE inert
  siblings are unsafe because **`checkEntities` is EAGER over the whole tree** — a free `Arbitrary`
  sibling with a junk entity, or a free unary op `.is <undeclared>`, flips the kind to
  unknownEntity even though `typeOf` never types it. FIX/DISCIPLINE: every sub-term checkEntities
  can traverse must be entity-clean → constrain all inert siblings to `StableWt` (int/str/bool
  literals) and restrict the unary op to entity-free ops (exclude `.is`). BinaryOp embeds no
  entity, so free `op` there is fine.
- Results (20 gen schemas, 2–11 envs): TEST A 400 rejected/0 accepted; TEST B 400 match/0 mismatch;
  all defects nested (>1 node, max repr ~1656); all 9 kinds. `nodes`/`sizeOf` under #eval fails
  (LCNF/termination) → use repr-length proxy; the derive carries a termination `sorry` so the
  self-check #evals must be `#eval!`.

## Targeted generation — ask for a specific kind `k` (2026-08-10)
YES, it can generate a REQUESTED kind. `k` is an index pinned in every constructor's conclusion,
so a derive with `k` as INPUT filters to matching constructors and threads `k` down to a leaf of
that kind. Added `derive_mutual generator (fun env c k => ∃ x, PolicyBodyErr c env x k)` +
`generateBodiesOfKind env k size count seed` in PolicyGenError.lean.
- Verified via per-kind `lake env lean` probes (KIND env var → `/tmp/testk.lean`, run one process
  per kind — `#eval` only flushes at process exit, so a hung kind hides all others; isolate them):
  8/9 kinds generate FAST (0–2ms), 5/5 produced and validator-confirmed.
- `impossiblePolicy` targeted was initially SLOW (deep fruitless backtrack): with `k` fixed,
  Specimen explored `PolicyBodyErr.typeErr`→`TypeErr` searching for an impossiblePolicy leaf that
  doesn't exist. FIX: guard `typeErr` with `k ≠ .impossiblePolicy` (logically vacuous for success;
  prunes the targeted search). → 0ms after. General lesson: in targeted mode, guard a recursive
  branch against kinds it can't produce, or the scheduler wastes the whole size budget searching.
- `tagNotFound` targeted throws in `lake env lean`: `(interpreter) unknown declaration
  '…MapContainsAttrs._redArg'` — an INTERPRETER limitation on that compiled generator's reduced
  form, NOT a relation defect (tagNotFound generates fine untargeted in the compiled build, Test
  A/B). Would need a compiled binary (the FFI path) to exercise targeted tagNotFound; not yet done.

## Remaining — NOT done
- **FFI/corpus wiring** (the real integration step): expose `generateErrorPolicies` through
  cedar-lean-ffi / the experiment pipeline to emit an ill-typed corpus for coverage. Decide the
  mix ratio (well-typed vs ill-typed) and whether pid uniqueness matters (currently "p0").
- Optional: reuse the full `HasType` generator for even richer frames — but that reintroduces
  env-sensitivity under multi-env validate (env-varying operands like `principal.attr`); would
  need env-stability analysis or a single-env emitted schema.

---
name: specimen-test-policy-properties
description: "How to test Cedar policy properties over well-typed inputs with specimen_test + a relational (req,es) generator; Specimen scheduling fixes"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 2c2459db-1548-4514-878b-acbbdb1fce71
---

Goal: use Specimen's `specimen_test` command to test properties about Cedar policies (equivalence, never-errors — the John Notes / symcc-style properties) over *well-typed* requests+entities.

## Files (cedar-lean/CedarGen/Relational/)
- `RequestEntities.lean` — derivable relational spec `WellTypedRequestAndEntities env req es` generating a *minimal* store (principal + resource + all declared action entities). Structural style like [[functional-to-relational-pitfalls]]. Helpers: `UIDForType`, `ValueConforms`, `RecordConforms`, `EntityAttrsForType`, `ActionEntities`.
- `RequestEntitiesTest.lean` — derives the generator; `specimen_test` soundness property: relation ⟹ functional validators (`instanceOfRequestType`/`instanceOfSchema`). User owns this file (added all the `Shrinkable` instances).
- `PolicyPropertyTest.lean` — demo: schema `E{foo:Bool,bar:Bool}`, tests `principal.foo && resource.bar ≡ resource.bar && principal.foo` (PASSES on well-typed inputs) + a control inequivalence that finds a counterexample.

## Ground truth = functional spec (user rule)
The relational spec is a **generator/sampler only**. Well-typedness truth is the functional Lean spec (`Cedar.Validation.instanceOf*`, `evaluate`, `typecheckPolicy`). Always validate generated samples against it — `specimen_test (∀ req es, Relation env req es → functional... = true)` tests exactly "relation implies function."

## Two Specimen scheduling fixes that unblocked generation (both needed under multiOutput)
1. **Mixed bound/fresh var in a premise argument** (pitfall #7). `IsValidEntityUID ents ⟨pty, eid⟩` (pty bound, eid fresh) gets scheduled as a CHECK with `eid` never generated → dead-end. Fix: a helper whose OUTPUT is the whole `EntityUID` — `UIDForType ents ety uid` builds `⟨ety, eid⟩` in the conclusion (ety input, eid generated).
2. **Free intermediate output filled arbitrarily.** `Lookup ents ety attrsTy` (checker) + `RecordConforms ents attrsV attrsTy` let the scheduler *generate* a random `attrsTy` via RecordConforms' multi-output and then check the lookup (never matches) → dead-end. Fix: FUSE lookup+conformance into one inductive (`EntityAttrsForType`) so the attr-*type* list is bound by **destructuring the input schema entry** (`Map.mk attrsTy`), never a free existential. `specimen_test` forces `multiOutput:=true`, so this must hold without relying on `multiOutput:=false`.

## Practical knobs
- Scoring: `Scoring.BudgetAwareScore` is NOT in the pinned Specimen version — use `Scoring.BoundedGradedScore`.
- Shrinking: `specimen.shrink` (default true), `specimen.shrinkBreadth` (8), `specimen.shrinkDepth` (100) — raise breadth/depth for more-minimal counterexamples.
- Ext values: don't `Arbitrary Ext.*` (yields ill-formed IPs/datetimes) — deferred; later reuse `Valid{Decimal,Datetime,Duration}` string generators.
- `Map.find?` is linear (no sortedness needed) — unsorted `Map.mk` in conclusions is fine as long as keys are unique (walk the declared schema).
- A counterexample makes `specimen_test` log an error (exit 1); wrap in `#guard_msgs (error, drop info, substring := true)` to keep a build green (Specimen's own TacticTest convention).

## Build
`lake build CedarGen.Relational.<Module>` from cedar-lean builds one module in isolation (CedarGen.lean root pulls in expensive test files, so don't add these there). bg-isolation disabled via `.claude/settings.json` (`worktree.bgIsolation:none`) because `require specimen from "../../specimen"` breaks under a worktree.

## __INTERNAL_ANALYZER__ (John's LLM-prove stream) — clone + specimen integration
- Clone: `git clone ssh://__INTERNAL_GIT_HOST__/pkg/__INTERNAL_ANALYZER__` (that exact URL; other gitfarm hosts failed). It's `__INTERNAL_ANALYZER_PKG__`: transpiles Cedar policies → Lean (deep `Cedar.Spec` or `--shallow` self-contained), states `always-allows`/`never-errors`/`equivalent`, and `--prove` drives headless `claude` then verifies independently via `#print axioms` ≠ `sorryAx` + statement guards. `wellTyped` precond exists **shallow-only** (necessary-consequence-only; deep is a TODO). Key files: emit.rs, shallow.rs, property.rs, validate.rs (RequestEnv), prove.rs.
- **Integration done (uncommitted):** cedar-lean `CedarGen/Relational/SpecimenLoop.lean` bundles instances + WellTypedRequestAndEntities generator for scratch files to import. prove.rs: `--specimen` flag → splices `import CedarGen.Relational.SpecimenLoop` + Specimen set_options into deep scratch + a prompt section. 69 lib tests pass.
- **CRITICAL constraint (measured):** the `specimen` tactic emits GLOBAL declarations, which Lean forbids inside a named `theorem` proof or a `have` ("cannot add declaration … restricted to the prefix <thm>"). It works only in a **separate top-level `example : <prop> := by specimen`** (anonymous). So the agent tests conjectures in throwaway `example`s (deleted after), never inside `policies_*`. Sound: examples never touch the named theorems' verification.
- **Metavariable measurement:** 0/22 intermediate proof states (always-allows/never-errors/equivalent; after intro/simp/cedar_unfold/cases/split) carry a goal metavariable (negative control `apply Eq.trans` correctly showed true). So specimen's `exprToConstructorExpr … ?m` failure on simp-reduced goals is NOT a goal metavariable — it's introduced by specimen's own delaborate→re-elaborate on large `isAuthorized` `match` terms. "Redundant alternative" errors are fixable with `set_option match.ignoreUnusedAlts true`. Robust inputs for specimen: pristine goals or clean `have`/`example` conjectures — never simp-reduced subgoals.
- **Remaining gap:** deep backend emits no `env : TypeEnv`, so specimen can't yet sample req/es on the analyzer's real goals without the agent supplying an env; emitting a deep `wellTyped`/env (their TODO) is the companion step. Files in cedar-lean: SpecimenTacticDemo, MVarMeasure, SpecimenFailGoals, SpecimenLoop.

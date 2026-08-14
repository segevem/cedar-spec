---
name: welltyped-generator-soundness-bugs
description: "Three soundness gaps in the welltyped-policy relational generator vs Rust validate; all resolved (Bug1 & Bug2 fixed, Bug3 non-issue)"
metadata: 
  node_type: memory
  type: project
  originSessionId: 01c084b2-8df7-4bc5-913e-f57d20956638
  modified: 2026-08-06T22:09:12.550Z
---

# Welltyped-policy generator: soundness vs the real `validate`

Investigated why ~7% of `welltyped-policy` (specimen) corpus is REJECTED by Rust strict
`validate` (contaminating the "well-typed" corpus with error-path hits). Key distinction:
`typecheckPolicy` (the generator self-check, and my first PBT) only runs `typeOf` and is
PERMISSIVE; the real `validate` = `typecheckPolicyWithEnvironments` runs, IN ORDER:
`checkEntities schema expr` → `schema.environments.mapM (typecheckPolicy ·)` → `allFalse ⇒ impossiblePolicy`.
So `validate` enforces MORE than `typeOf`. Three gaps found:

## Bug 2 — FIXED (action-UID distinctness) ✅
`WfActionSchema.cons` (Schema.lean) had no key-distinctness → duplicate action UIDs with
different entries. `RequestFromAction` (walks raw list) picked a different entry than
`Map.mk actionEntries` kept → `TypeEnv` with `reqty.context ≠ acts[reqty.action].context`
(context is per-ACTION). Symptom: `attrNotFound` ("attribute id in context not found").
FIX (done, in working tree): added `SelectRemove` relation to Schema.lean + a MANUAL UNIFORM
generator in SchemaTest.lean (before the derive), threaded a fixed `actionEidPool` through
`WfActionSchema` (draws distinct eids without replacement, no backtracking). Verified:
attrNotFound 141→0 (see [[reference_run3-operator-frequency]] tooling / PBT below).

## Bug 3 — NOT A BUG (impossiblePolicy) ✅ by definition
`impossiblePolicy` (always-false policy) is a Rust **ValidationWarning**, and the gate
everywhere (`is_well_typed`) uses `validation_passed()` = `validation_errors.is_empty()`
(IGNORES warnings). So Rust ACCEPTS impossible policies — for BOTH specimen and handwritten
(same gate). Already symmetric; nothing to change. NOTE a spec divergence: Lean `validate`
returns `.error (.impossiblePolicy)` (stricter than Rust's warning) — my pure-Lean PBT
over-counted 141 as rejections; per the real gate they're well-typed. Don't "fix" the Lean
validator (it's the spec under test); just don't treat impossiblePolicy as a rejection.

## Bug 1 — FIXED (undeclared entity type in `is`) ✅
ROOT CAUSE: `CedarGen/Relational/TypeOfLean.lean`, rule `unaryAppIsFalse` left the TESTED type
`ety₁` UNCONSTRAINED. `typeOf` never requires `ety₁` declared, but `validate` runs
`checkEntities` FIRST, which rejects `is <ety>` when `ety ∉ schema.ets` and not an action type
→ "unrecognized entity type". So generator emitted `is <undeclared>` (~4% = `unknownEntity`).
FIX (done, in working tree): added a NEW relation `ValidDifferentEntityType other ety ets acts`
(TypeOfLean.lean, right after `ValidEntityType`) — ctors `inSchema | isAction` mirror
`ValidEntityType` but bind `ety` via `MapContains`/`MapContainsPairKey` FIRST, then guard
`ety ≠ other`. This CONSTRUCTIVELY produces `ety₁` declared *and* ≠ the operand type from the
finite schema (residual reject only over the lone `= other` schema key), instead of the old
`ety₁ ≠ ety₂` check with `ety₁` free over the unbounded `EntityType` space. Rewired
`unaryAppIsFalse` to `ValidEntityType ety₂ … → ValidDifferentEntityType ety₂ ety₁ … → HasType x₁ … (.entity ety₂)`.
Auto-derived by `derive_mutual` (autoDeriveDeps); no manual DecOpt needed (`≠` guard on bound
vars is handled, like `DefinedEntityType`/`NotInET`). VERIFIED: PBT `ok=859 unknownEntity=0
attrNotFound=0 other=141` (all 141 = impossiblePolicy = Bug 3, gate-accepted). `is` still
generates healthily (66/509 unaryApp ≈ 13%, no collapse).

## Cleanup after Bug 1 verified
- `PolicySoundnessPBT.lean` KEPT but made INERT (per user): top-level `#eval` → `def
  runPolicySoundnessPBT`, with commented `-- #eval runPolicySoundnessPBT`. Re-runnable
  regression harness; building the module no longer re-runs the validate loop.
- REMOVE `dump_illtyped_roundtrip` test from `cedar-lean-ffi/src/lean_ffi.rs`.
- Decide keep/remove: `cedar-drt/coverage/src/bin/op_hist.rs`, and the `REPLAY_WELLTYPED_ONLY`/
  `REPLAY_DUMP_ILLTYPED` env additions in `cedar-drt/coverage/src/main.rs` (useful diagnostics).
- `cedar-lean/CedarGen/Relational/target_cov_diag/` local instrumented build — leftover; exclude
  from packaging (it bloated an earlier src.tgz to 120M) or rm.

## Context
Working tree also has (uncommitted): the `id bty` throughput fix + tuned `favorConditions`
(see [[id-bty-condition-speedup]]), the DRT-experiment plotting fixes (per-rep maps, drop-
incomplete, throughput probe source, throughput_rate metric), the guided.rs collect fixes
(rss_limit/stderr — targets wrong phase, harmless), and the coverage_analyze.py shard
retry/stderr fix (the REAL PHASE-3.5 fix: shards silently dropped under 191-way load;
single-thread tokio runtime fix in main.rs). See [[project_guided-handwritten-rebuild]].

## Verification run — 6-ARM (2026-08-06, CURRENT)
Instance **i-0d8a3545d9b914ee4** (c7i.48xlarge, 192 vCPU), S3ROOT **ci-run-16reps-900s-20260806T220849Z**,
REPS=16 RUN_SECS=900 SEED_BASE=21e12 ON_FINISH=stop, golden AMI ami-07994225d79227b05, AWS_PROFILE
cedar-experiment. approaches.welltyped-6arm.txt: wt-policy-sz12, wt-policy-sz12-filtered,
wt-policy-sz20, wt-policy-sz20-filtered, hw-slots-off, hw-welltyped-noslots. 6×16×2=192 jobs (fits).
REPS=16 chosen empirically: run3 subsample showed 3-path CIs widen only ~10% at 16 (√(20/16)); the
specimen-vs-hw gap is ~140 paths vs ~8 CI halfwidth = ~17 halfwidths clearance → 16 is plenty.
`*-filtered` arms = NEW per-approach `COLLECT_WELLTYPED_ONLY=1` (run_experiment.sh edit: name suffix
`-filtered` → reject gate on that arm's collect). Same seed as unfiltered twin ⇒ SOUND generator
rejects 0 ⇒ J=1.000 (end-to-end soundness proof incl. proto round-trip). sz20 safe: welltyped-policy
uses `lean-schema-typeof` (UNAFFECTED by the lean-typeof sz20 blowup) + 50s per-generate backstop.
src.tgz re-uploaded 22:08 (has run_experiment.sh filter + kpath + coverage-compare fix); lean_cache
reused (21:51, has the fix). **Superseded 3-arm run i-0f998371e39ae81b5 (ci-run-20reps-900s-...215257Z):
STOPPED (not terminated) — reusable/terminable, do NOT kill w/o direction.** Ships: Bug1/Bug2 fix (REBUILT static libs
libCedar_CedarGen.a/CedarFFI.a AFTER the edit — verified mtimes 21:44/21:49 vs edit 21:07;
build_lean_lib.sh builds CedarGen:static+CedarFFI:static, which CedarFFI.Generate's
welltyped-policy path links), finer k-paths (kpath.rs op/extfn labels), per-pair
coverage-compare plot fix. Purpose: re-measure the 3-way comparison with the now-SOUND
generator (prior wt-policy corpus was ~7% error-path contaminated) + fair well-typed-only
arm. Do NOT kill w/o direction. Prior l4 run instances left STOPPED.

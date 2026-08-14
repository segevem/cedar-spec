---
name: specimen-tactic-async-fix
description: "How the `specimen` tactic was made to work deep inside a proof (after intro, inside a `have`) without disabling async elaboration"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 2c2459db-1548-4514-878b-acbbdb1fce71
---

The `specimen` *tactic* (Specimen/Tactic.lean, `evalSpecimenTac`) works deep inside
a proof — after `intro`, and inside a `have` — with `Elab.async` left ON.

**Problem.** Inside a proof, the enclosing declaration elaborates on an async
branch whose env restricts `addDecl` to the current declaration's name prefix
(`Environment.AsyncContext.mayContain`: `declPrefix.isPrefixOf (privateToUserName n.eraseMacroScopes)`).
specimen's derived generators/checkers are named after their *types*, so `addDecl`
panics: "cannot add declaration … restricted to the prefix …".

**Fix (the load-bearing one-liner).** In the tactic, right after snapshotting the
env and before running the emitted `specimen_test` command, call
`modifyEnv (·.unlockAsync)`. `Environment.unlockAsync` sets `asyncCtx? := none`,
clearing the restriction. The derived defs are transient (goal is left open, the
tactic restores `savedEnv` afterward), so nothing leaks. No-op when async is off.

**Critical pairing:** `unlockAsync` ONLY works with the original **delab→re-elaborate**
tactic path (delaborate `closedProp` → build `specimen_test` syntax →
`runCommandElabMInCore (elabCommand cmdStx)`). Re-elaborating the proposition from
syntax detaches it from the tactic's local mvar/fvar context, so the checker
compiles cleanly on the async branch.

**Dead end — do NOT reintroduce the "roundtrip refactor"** (extract
`elabSpecimenTestCore (tgt : Expr)`, feed the tactic's Expr straight in, skip
delab). It works after `intro` but BREAKS `specimen` inside a `have`: the direct
Expr carries tactic-context references, so `Meta.evalExpr` reads a `sorryAx` stub
("checker uses 'sorry' and/or contains errors"). Evidence: original+async-off →
have passes 979; refactor+async-off → have fails; original+unlockAsync+async-ON →
after-intro 9798 + have 979 both pass.

**Also dead ends:** per-declaration `set_option Elab.async false in <thm>` fixes
after-`intro` but NOT `have` (its `by` block spawns a nested async task); scope-level
`Elab.async false` inside `runCommandElabMInCore` is a no-op (`snap? := none`
already forces inner defs synchronous). File-level `Elab.async false` works but the
user did not want to disable async.

Demo: CedarGen/Relational/SpecimenTacticDemo.lean (no async-off; builds green).
prove.rs `SPECIMEN_SETUP` needs NO async-off. See [[specimen-test-policy-properties]],
[[specimen-derive-mutual-syntax]].

---
name: partial-typeof-experiment
description: "PartialCedarType demand-threaded variant of the relational typing spec — status, results, open issues"
metadata: 
  node_type: memory
  type: project
  originSessionId: 9f5f5d95-0ccd-4cb3-8852-be99b0596a74
  modified: 2026-07-30T20:58:31.724Z
---

Experimental variant of the relational Cedar typechecker that threads a `PartialCedarType`
demand (input) through `HasType`. The `CedarType` output is the FILLER of the hole in the
demand (NOT the complete type); complete type = `plug pt filler`. Tied by a `Plug pt filler
complete` relation ("composition"). (Earlier draft used `Fills`/complete-type output — the user
corrected: e.g. `HasType x (.set .hole) elemTy` not `... (.set elemTy)`.) Built off `TypeOfLean.lean` (the minimal no-TypedExpr/no-Option
variant), NOT `TypeOf.lean`. Goal: for structured operands (getAttr/getTag/mem), recurse into
the sub-expr with a partial demand (`.entity`/`.ext`/`.set`) so the concrete type flows OUT of
the operand's derivation, instead of producing it from the schema first then pattern-matching
(recurse-then-lookup vs lookup-then-recurse).

Files (untracked, in main checkout `cedar-lean/CedarGen/Relational/`, branch relational-typeof):
`TypeOfPartial.lean` (spec, namespace `CedarGen.Relational.Partial`) and `TypeOfPartialTest.lean`.

`PartialCedarType := hole | entity | ext | set PartialCedarType` (dropped bool/int/string — no
inner element; skipped record — would need list-of-fills). Signature:
`HasType : Expr → Capabilities → TypeEnv → PartialCedarType → CedarType(filler) → Capabilities → Prop`.
Base operands recurse `.hole` (filler = whole base type); entity/ext recurse `.entity`/`.ext`
(filler = whole `.entity ety`/`.ext xty`, leaf); set operands recurse `.set p` and the filler is
the ELEMENT filler (e.g. `.set .hole` → elemTy, `.set .entity` → `.entity ety`). Every conclusion
computes the complete type internally and exposes the filler via `Plug pt filler complete` (except
ite/or, which pass the branch filler through). `plug` (fn) + `Plug` (reln) + `DecOpt`/`plugB` +
an `ArbitrarySizedSuchThat CedarType (Plug pt · complete)` producer.

Results (corrected filler design, size 8, 200 gens each, testEnv): `.hole` → 200/200 (453 ms);
`.entity` → 200/200 (122 ms, ~4× faster than the earlier complete-type draft's 511 ms);
`.set .hole` → 0/200 (all gen-failures, 1906 ms). Zero type/caps failures → complete type
(`plug demand filler`) matches functional `typeOf` in every generated case. Leaner filler output
made generation markedly faster than the complete-type draft.

Open issues: (1) `.set .hole` demand → 0/200, all gen-failures (set generation from a set demand
needs demand threaded into elements and/or more retries/size). (2) `derive_mutual` termination
proof gets a `sorry` (WF-recursion `decreasing_by` simp exceeds max steps because the extra Fills
premise per rule enlarges the goal) — generator runs fine under `#eval!` but `#eval` refuses;
needs a termination fix for a clean build. Derive takes ~237s. See [[experimentation-plan]],
[[functional-to-relational-pitfalls]], [[experiment-harness-pitfalls]].

---
name: id-bty-condition-speedup
description: id-wrapping the bool subtype in WellTypedConditions gives ~10x faster condition gen; retune favorConditions after
metadata: 
  node_type: memory
  type: reference
  originSessionId: 01c084b2-8df7-4bc5-913e-f57d20956638
  modified: 2026-08-05T22:38:36.583Z
---

Welltyped-policy condition generation was slow because `WellTypedConditions.when/unless`
demanded `HasType body caps env (.bool bty) cout` with **`bty` left as a type-index
OUTPUT** — Specimen then generated any-typed terms and rejected non-bools (undirected),
instead of reusing the fully type-directed HasType instance (type-as-input) that the
standalone generator uses. See [[reference_specimen-id-force-check-mode]].

**Fix (Policy.lean WellTypedConditions when+unless):** wrap the subtype in `id` →
`HasType body caps env (.bool (id bty)) cout`. Suppresses HasType as producer of `bty`,
so Specimen sources `bty` from ambient `Arbitrary BoolType` (in scope via
CedarGen.Schema ← TypeOfLeanBase ← Variants/BudgetAware) FIRST, making `.bool bty` a
ground input → fast directed instance.

**Measured (testEnv sz12, n=500, clean A/B, identical weights, only `id` toggled):**
- without id: 35 pol/s, 1.45 conds/pol, **51 conds/s**
- with id:    47 pol/s, 10.58 conds/pol, **500 conds/s**  → **~10x faster per condition**

Policies/s barely moved because it's a BUDGET interaction: cheap bodies let the
budget-aware scheduler pack ~10 clauses/policy instead of ~1.5 (expensive bodies drained
the budget → early nil). So the old aggressive `favorConditions` (`nil→1`,
`when→(base+2)*3`) only *looked* fine — expensive bodies masked it. With cheap bodies the
weights directly control length.

**Retune favorConditions (PolicyGen.lean) for ~1-2 conds/policy** (geometric:
P(continue)=(when+unless)/(nil+when+unless)):
`nil => base*3+1 | when => base*2+1 | unless => base*2+1`  ⇒ (when+unless):nil≈4:3 ⇒ E[len]≈1.3.

**Combined result: 403 pol/s (~8-11x vs 35-47), 1.17 conds/pol, 500/500 well-typed.**
Beats the old "491/s" in effect (that was 71%-empty scope-only policies).

NOT yet deployed to an experiment run — run #3 used the OLD generator. Repackage+redeploy
needed to get this into DRT throughput. Timing harness was a scratch file
(PolicyTimingScratch.lean) — DELETE before any repackage (duplicate-derive glob).
See [[project_guided-handwritten-rebuild.md]], [[specimen-weight-modifier]].

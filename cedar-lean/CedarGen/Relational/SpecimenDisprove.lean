/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import CedarGen.Relational.SpecimenTacticDemo

/-! # Disproving false Cedar policy theorems with `specimen`

Reuses the `fooBar` schema (`entity E { foo: Bool, bar: Bool }; action a`) and
generator boilerplate from `SpecimenTacticDemo`. Each theorem below is a *false*
claim about policies; `specimen` samples well-typed `(req, es)` and reports a
concrete counterexample. A true control at the end survives.

`specimen` is a diagnostic — it never closes the goal — so it can only ever tell
the agent "this is refuted, prove the negation" or "this survived, try to prove
it." That is exactly its role in __INTERNAL_ANALYZER__'s `--prove` loop.
-/

open CedarGen.Relational.ReqEnt
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.richOutput false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ## Extra policies phrased over the `fooBar` schema -/

def eFooOrBar : Expr := .or eFooP eBarR
/-- `permit(...) when { principal.foo || resource.bar };` -/
def fooOrBarPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, eFooOrBar⟩]⟩]

/-- `permit(...) when { !(principal.foo && resource.bar) };` -/
def notAndPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, .unaryApp .not (.and eFooP eBarR)⟩]⟩]
/-- `permit(...) when { !principal.foo && !resource.bar };` (a WRONG De Morgan) -/
def badDeMorganPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, .and (.unaryApp .not eFooP) (.unaryApp .not eBarR)⟩]⟩]

/-! ## FALSE #1 — confusing `&&` with `||`

`permit when { p.foo && r.bar }` is NOT equivalent to `permit when { p.foo || r.bar }`
(they disagree whenever exactly one of foo/bar is true). -/

/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 2, max := 8, tests := 20000)
  (∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    isAuthorized req es fooAndBarPolicies = isAuthorized req es fooOrBarPolicies)

/-! ## FALSE #2 — "this permit always allows"

`permit when { principal.foo }` does not always allow — when `foo = false` the
condition fails and the decision is `deny`. -/

/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 2, max := 8, tests := 20000)
  (∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    (isAuthorized req es fooOnlyPolicies).decision = .allow)

/-! ## FALSE #3 — a WRONG De Morgan law

`!(p.foo && r.bar)` is `!p.foo || !r.bar`, NOT `!p.foo && !r.bar`. The buggy
rewrite disagrees whenever exactly one of foo/bar is true. -/

/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 2, max := 8, tests := 20000)
  (∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    isAuthorized req es notAndPolicies = isAuthorized req es badDeMorganPolicies)

/-! ## FALSE #4 — disproving *inside a proof* with the `specimen` tactic

The realistic loop shape: mid-proof, the agent conjectures a false lemma with
`have` and tests it — `specimen` refutes it, so the agent abandons that lemma.
The `specimen` tactic reports a counterexample via `logError`, captured here. -/

/-- error: Found counter-example! -/
#guard_msgs (error, drop info, drop warning, substring := true) in
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
example :
    ∀ (req : Request) (es : Entities),
      WellTypedRequestAndEntities fooBarEnv req es →
      (isAuthorized req es fooAndBarPolicies) = (isAuthorized req es fooOrBarPolicies) := by
  intro req es hwt
  -- Conjecture the (false) equivalence as a lemma and TEST it before proving:
  have bogus : ∀ (r : Request) (e : Entities),
      WellTypedRequestAndEntities fooBarEnv r e →
      evaluate (.and eFooP eBarR) r e = evaluate (.or eFooP eBarR) r e := by
    specimen (min := 2, max := 8, tests := 5000)  -- reports a counterexample
    sorry
  sorry

/-! ## TRUE control — commutativity of `&&` survives

`permit when { p.foo && r.bar }` ≡ `permit when { r.bar && p.foo }`. -/

/-- tests passed -/
#guard_msgs (info, substring := true, drop warning) in
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 2, max := 8, tests := 20000)
  (∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    isAuthorized req es fooAndBarPolicies = isAuthorized req es barAndFooPolicies)

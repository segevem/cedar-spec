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

import CedarGen.Relational.RequestEntities
import CedarGen.Schema
import Specimen

/-! # Measurement: how often do intermediate proof goals carry unassigned
metavariables (which would break `specimen`)?

`mvarProbe "<tag>"` replicates *exactly* what the `specimen` tactic does to the
goal before handing it to Specimen's converter: abstract the local hypotheses
over the target (`mkForallFVars (← getLocalHyps)`), `instantiateMVars`, and check
`hasExprMVar`. If the closed proposition has an unassigned metavariable,
`specimen` here would crash with `exprToConstructorExpr … ?m`. The probe only
logs — it never changes the goal — so a proof continues normally after it.

We sprinkle it after each tactic step of realistic proofs of the analyzer's
actual goal shapes (`always-allows`, `never-errors`, `equivalent`), using the
real `cedar_unfold` / `cedar_eval` tactics copied verbatim from
`__INTERNAL_ANALYZER__/src/prove.rs`. Grep the `PROBE …` lines and count
`closedMVar=true` vs total.
-/

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open CedarGen.Relational.ReqEnt

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

-- `mvarProbe "<tag>"` replicates `specimen`'s pre-conversion of the goal and
-- logs whether the raw target and the specimen-closed proposition carry an
-- unassigned metavariable.
open Lean Elab Tactic Meta in
elab "mvarProbe " tag:str : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let fvars ← getLocalHyps
  let closed ← instantiateMVars (← mkForallFVars fvars tgt)
  logInfo m!"PROBE {tag.getString} targetMVar={tgt.hasExprMVar} closedMVar={closed.hasExprMVar}"

/-! ## Real `cedar_unfold` / `cedar_eval` (verbatim from prove.rs `CEDAR_TACTIC`) -/

macro "cedar_unfold" : tactic =>
  `(tactic|
    simp only [
      Cedar.Spec.isAuthorized, Cedar.Spec.satisfiedPolicies,
      Cedar.Spec.satisfiedWithEffect, Cedar.Spec.satisfied,
      Cedar.Spec.errorPolicies, Cedar.Spec.errored, Cedar.Spec.hasError,
      Cedar.Spec.evaluate, Cedar.Spec.apply₁, Cedar.Spec.apply₂,
      Cedar.Spec.Result.as,
      Cedar.Spec.Policy.toExpr, Cedar.Spec.Conditions.toExpr,
      Cedar.Spec.Condition.toExpr, Cedar.Spec.Scope.toExpr,
      Cedar.Spec.PrincipalScope.toExpr, Cedar.Spec.ResourceScope.toExpr,
      Cedar.Spec.ActionScope.toExpr,
      Cedar.Spec.Var.eqEntityUID, Cedar.Spec.Var.inEntityUID,
      Cedar.Spec.Var.isEntityType,
      List.filterMap, List.isEmpty, List.reverse, List.reverseAux,
      List.foldl, List.map, Bool.and, Bool.not])

macro "cedar_eval" : tactic =>
  `(tactic| cedar_unfold <;> first | rfl | decide | skip)

/-! ## Schema + policies (analyzer-style deep goals) -/

def eTy : EntityType := { id := "E", path := [] }
def aAction : EntityUID := ⟨{ id := "Action", path := [] }, "a"⟩

def fooBarEnv : TypeEnv :=
  { ets := Map.make [
      (eTy, .standard { ancestors := Set.empty, attrs := Map.make [("foo", .required (.bool .anyBool)), ("bar", .required (.bool .anyBool))], tags := none }) ]
    acts := Map.make [
      (aAction, { appliesToPrincipal := Set.make [eTy], appliesToResource := Set.make [eTy], ancestors := Set.empty, context := Map.empty }) ]
    reqty := { principal := eTy, action := aAction, resource := eTy, context := Map.empty } }

def eFooP : Expr := .getAttr (.var .principal) "foo"
def eBarR : Expr := .getAttr (.var .resource) "bar"

def allowAll : Policy := ⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, []⟩
def allowAllPolicies : Policies := [allowAll]

def fooAndBarPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, .and eFooP eBarR⟩]⟩]
def barAndFooPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, .and eBarR eFooP⟩]⟩]
def fooOnlyPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, eFooP⟩]⟩]

/-! ## Probed proofs (realistic agent-style tactic sequences) -/

-- P1: always-allows on all-`.any` permit (the trivial case cedar_eval closes).
example : ∀ (req : Request) (es : Entities),
    (isAuthorized req es allowAllPolicies).decision = .allow := by
  mvarProbe "P1/pristine"
  intro req es;              mvarProbe "P1/after-intro"
  simp only [allowAllPolicies]; mvarProbe "P1/after-simp-def"
  cedar_unfold;              mvarProbe "P1/after-cedar_unfold"
  sorry

-- P2: never-errors on fooOnly, well-typed precond.
example : ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    (isAuthorized req es fooOnlyPolicies).erroringPolicies.isEmpty = true := by
  mvarProbe "P2/pristine"
  intro req es hwt;          mvarProbe "P2/after-intro"
  simp only [fooOnlyPolicies]; mvarProbe "P2/after-simp-def"
  cedar_unfold;              mvarProbe "P2/after-cedar_unfold"
  sorry

-- P3: equivalent (fooAndBar vs barAndFoo), well-typed precond.
example : ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    (isAuthorized req es fooAndBarPolicies).decision
      = (isAuthorized req es barAndFooPolicies).decision := by
  mvarProbe "P3/pristine"
  intro req es hwt;          mvarProbe "P3/after-intro"
  cedar_unfold;              mvarProbe "P3/after-cedar_unfold"
  sorry

-- P4: the exact ad-hoc simp set that first tripped specimen.
example : ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    (isAuthorized req es fooOnlyPolicies).decision = .deny := by
  mvarProbe "P4/pristine"
  intro req es hwt;          mvarProbe "P4/after-intro"
  simp only [fooOnlyPolicies, isAuthorized, satisfiedPolicies,
    satisfiedWithEffect, satisfied]; mvarProbe "P4/after-partial-simp"
  sorry

-- P5: destructure the well-typed hypothesis, then probe (rcases on a hyp).
example : ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    (isAuthorized req es fooOnlyPolicies).decision = .allow := by
  mvarProbe "P5/pristine"
  intro req es hwt;          mvarProbe "P5/after-intro"
  cases hwt;                 mvarProbe "P5/after-cases-hwt"
  sorry

-- P6: split on the if inside isAuthorized after unfolding (branchy proof).
example : ∀ (req : Request) (es : Entities),
    (isAuthorized req es fooOnlyPolicies).decision = .allow := by
  mvarProbe "P6/pristine"
  intro req es;              mvarProbe "P6/after-intro"
  simp only [fooOnlyPolicies]; mvarProbe "P6/after-simp-def"
  cedar_unfold;              mvarProbe "P6/after-cedar_unfold"
  split;                     mvarProbe "P6/after-split"
  all_goals sorry

-- NEGATIVE CONTROL: `apply Eq.trans` leaves the target `1 = ?mid` — a genuine
-- metavariable in the goal — so the probe MUST report closedMVar=true here.
-- This confirms the instrument is not vacuously reporting `false`.
example : (1 : Nat) = 1 := by
  apply Eq.trans; mvarProbe "CTRL/after-apply-trans"
  all_goals rfl

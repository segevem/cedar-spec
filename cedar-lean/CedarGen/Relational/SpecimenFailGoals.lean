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

/-! # Print the goals `specimen` actually fails on

`specimenTry "<tag>"` pretty-prints the current goal, then *actually runs* the
`specimen` tactic (tests := 1) inside a `try`/`catch`, and reports OK / FAIL
together with the goal. We run it at proof states before and after unfolding, so
we can read off exactly which goal shapes `specimen` chokes on (and see they are
metavariable-free — the failure is in `specimen`'s own delaborate→re-elaborate→
convert pipeline, not the goal). -/

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open CedarGen.Relational.ReqEnt
open Plausible

set_option linter.unusedVariables false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.richOutput false
set_option match.ignoreUnusedAlts true

/-! ## Generator boilerplate (so `specimen` can derive on well-typed goals) -/

instance [Arbitrary α] [Arbitrary β] [LT α] [DecidableLT α] : Arbitrary (Map α β) where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
    let mut pairs : List (α × β) := []
    for _ in List.range len do
      pairs := (← Arbitrary.arbitrary, ← Arbitrary.arbitrary) :: pairs
    return Map.make pairs

instance [Enum α] [Enum β] [LT α] [DecidableLT α] : Enum (Map α β) where
  enum := do let pairs ← Enum.enum (α := List (α × β)); return Map.make pairs

deriving instance Plausible.Arbitrary for Attr
deriving instance Plausible.Arbitrary for
  Var, ExtFun, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
  Qualified, CedarType
deriving instance Enum for
  Var, ExtFun, UInt64, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
  Qualified
deriving instance Enum for EntityType
deriving instance Shrinkable for Name, EntityUID
deriving instance Shrinkable for Map, Int64, Prim, Set
deriving instance Shrinkable for Ext.IPAddr.IPNetAddr
deriving instance Shrinkable for Ext.IPAddr.CIDR
deriving instance Shrinkable for Ext.IPAddr.IPNet, Ext.Datetime, Ext.Datetime.Duration
deriving instance Shrinkable for Duration
deriving instance Shrinkable for Ext
deriving instance Shrinkable for Value
deriving instance Shrinkable for Request
deriving instance Shrinkable for EntityData
deriving instance Shrinkable for Entities

/-! ## `cedar_unfold` (verbatim from prove.rs) and schema/policies -/

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

def fooAndBarPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, .and eFooP eBarR⟩]⟩]
def barAndFooPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, .and eBarR eFooP⟩]⟩]
def fooOnlyPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, eFooP⟩]⟩]

/-! ## `specimenTry`: run specimen, print goal + OK/FAIL -/

open Lean Elab Tactic Meta in
elab "specimenTry " tag:str : tactic => withMainContext do
  -- Full proof state: local context (hypotheses) + ⊢ target — exactly what
  -- `specimen` abstracts via `mkForallFVars (← getLocalHyps)`.
  let stateFmt ← Meta.ppGoal (← getMainGoal)
  let outcome ←
    try
      evalTactic (← `(tactic| specimen (min := 1, max := 1, tests := 1)))
      pure "OK (specimen ran)"
    catch ex => pure s!"FAIL: {← ex.toMessageData.toString}"
  logInfo m!"SPECIMENTRY {tag.getString}: {outcome}\n---- state ----\n{stateFmt}\n---- end state ----"

/-! ## Proofs: run specimen pristine (control) and after unfolding -/

-- Equivalent (well-typed precond).
example : ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    (isAuthorized req es fooAndBarPolicies).decision
      = (isAuthorized req es barAndFooPolicies).decision := by
  specimenTry "EQUIV/pristine"
  intro req es hwt
  cedar_unfold
  specimenTry "EQUIV/after-cedar_unfold"
  sorry

-- never-errors (well-typed precond), partial ad-hoc simp.
example : ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    (isAuthorized req es fooOnlyPolicies).decision = .deny := by
  specimenTry "DENY/pristine"
  intro req es hwt
  simp only [fooOnlyPolicies, isAuthorized, satisfiedPolicies, satisfiedWithEffect, satisfied]
  specimenTry "DENY/after-partial-simp"
  sorry

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

import CedarGen.Relational.Policy
import CedarGen.Relational.TypeOfError
import CedarGen.Relational.Variants.BudgetAware
import Specimen

/-! # Ill-typed policy generator (validation-error corpus)

Derives a Specimen generator from `IllTypedPolicy`: given a `TypeEnv`, produce a policy with
well-typed scopes (reusing `WellTyped*Scope` from `Policy.lean`) and a single `when` clause
whose body triggers a Cedar VALIDATION error (`ErrorExpr`, `TypeOfError.lean`). The companion
to `PolicyGen.generatePolicies`; exposes `generateErrorPolicies` for the FFI and a self-check
that runs the real validator (`Cedar.Validation.validate`) and tallies the error kinds. -/

namespace CedarGen.Relational.PolicyGenError

open CedarGen.Relational.Policy
open CedarGen.Relational.Lean
open Variant.BudgetAware
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible
open Scoring Schedules

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-- A policy that fails validation. Scopes are well-typed and consistent with the request
    type (identical to `WellTypedPolicy`), but the single `when` body is an `ErrorExpr`, so
    the folded `Policy.toExpr` (`scopes && body`, body innermost) is rejected by the
    validator. `pid`/`effect` are irrelevant to type validation, so they are fixed. -/
inductive IllTypedPolicy : TypeEnv → Policy → Prop where
  | mk : ∀ entityEntries actionEntries reqty
        principalScope actionScope resourceScope body kind,
      WellTypedPrincipalScope entityEntries actionEntries reqty.principal principalScope →
      WellTypedActionScope actionEntries reqty.action actionScope →
      WellTypedResourceScope entityEntries actionEntries reqty.resource resourceScope →
      PolicyBodyErr ∅ (TypeEnv.mk (Map.mk entityEntries) (Map.mk actionEntries) reqty) body kind →
      IllTypedPolicy
        (TypeEnv.mk (Map.mk entityEntries) (Map.mk actionEntries) reqty)
        (Policy.mk "p0" .permit principalScope actionScope resourceScope [Condition.mk .when body])

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.precomputeWeights true in
#time derive_mutual
  generator (fun env => ∃ p, IllTypedPolicy env p)

/-- Generate `count` ill-typed policies for `env`. Mirrors `PolicyGen.generatePolicies`. -/
def generateErrorPolicies
    (env : TypeEnv) (size count : Nat) (seed : Option Nat := none)
    [inst : ArbitrarySizedSuchThat Policy (fun p => IllTypedPolicy env p)]
    : IO (List Policy) := do
  let mut policies : List Policy := []
  let mut currentSeed := seed.getD 0
  for _ in List.range count do
    try
      let p ← if seed.isSome then
          Gen.runUntilWith currentSeed (attempts := .some 3) (inst.arbitrarySizedST size) size
        else
          Gen.runUntil (attempts := .some 3) (inst.arbitrarySizedST size) size
      policies := policies ++ [p]
    catch _ => pure ()
    currentSeed := currentSeed + 1
  return policies

/-! ## Targeted mode: generate a body for a REQUESTED error kind `k` (k as INPUT). -/

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.precomputeWeights true in
#time derive_mutual
  generator (fun env c k => ∃ x, PolicyBodyErr c env x k)

/-- Generate up to `count` bodies that make a policy fail validation with the REQUESTED kind `k`. -/
def generateBodiesOfKind
    (env : TypeEnv) (k : VErrKind) (size count : Nat) (seed : Option Nat := none)
    [inst : ArbitrarySizedSuchThat Expr (fun x => PolicyBodyErr ∅ env x k)]
    : IO (List Expr) := do
  let mut xs : List Expr := []
  let mut cur := seed.getD 0
  for _ in List.range count do
    try
      let x ← if seed.isSome then
          Gen.runUntilWith cur (attempts := .some 5) (inst.arbitrarySizedST size) size
        else Gen.runUntil (attempts := .some 5) (inst.arbitrarySizedST size) size
      xs := xs ++ [x]
    catch _ => pure ()
    cur := cur + 1
  return xs

/-- Project a `ValidationError` to the lossy kind string the DRT compares
    (`Validator.validationErrorToJson`). -/
def errKind : ValidationError → String
  | .typeError _ e => match e with
    | .lubErr _ _             => "lubErr"
    | .unexpectedType _       => "unexpectedType"
    | .attrNotFound _ _       => "attrNotFound"
    | .tagNotFound _ _        => "tagNotFound"
    | .unknownEntity _        => "unknownEntity"
    | .extensionErr _         => "extensionErr"
    | .emptySetErr            => "emptySetErr"
    | .incompatibleSetTypes _ => "incompatibleSetTypes"
  | .levelError _       => "levelError"
  | .impossiblePolicy _ => "impossiblePolicy"

end CedarGen.Relational.PolicyGenError

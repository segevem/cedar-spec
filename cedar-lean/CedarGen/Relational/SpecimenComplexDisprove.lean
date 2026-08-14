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

/-! # A harder false theorem: the distributivity trap over two entity types

Schema: `entity User { a: Bool, b: Bool }; entity Doc { c: Bool, d: Bool };
action view appliesTo (principal: User, resource: Doc)`.

* P1 = `permit when { (principal.a && principal.b) || (resource.c && resource.d) }`
* P2 = `permit when { (principal.a || resource.c) && (principal.b || resource.d) }`

The claim `P1 ≡ P2` looks like a distributive law but is FALSE:
`(a∧b)∨(c∧d)` is strictly stronger than `(a∨c)∧(b∨d)`. They diverge only on the
"cross" assignments — e.g. `a=true, b=false, c=false, d=true`. Disproving it by
hand means (i) solving a 4-variable boolean puzzle and (ii) hand-building a
well-typed input spanning *two* distinct entity types. -/

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

/-! ## Two-entity-type schema -/

def userTy : EntityType := { id := "User", path := [] }
def docTy  : EntityType := { id := "Doc",  path := [] }
def viewAction : EntityUID := ⟨{ id := "Action", path := [] }, "view"⟩

def complexEnv : TypeEnv :=
  { ets := Map.make [
      (userTy, .standard { ancestors := Set.empty, attrs := Map.make [("a", .required (.bool .anyBool)), ("b", .required (.bool .anyBool))], tags := none }),
      (docTy, .standard { ancestors := Set.empty, attrs := Map.make [("c", .required (.bool .anyBool)), ("d", .required (.bool .anyBool))], tags := none })]
    acts := Map.make [
      (viewAction, { appliesToPrincipal := Set.make [userTy], appliesToResource := Set.make [docTy], ancestors := Set.empty, context := Map.empty })]
    reqty := { principal := userTy, action := viewAction, resource := docTy, context := Map.empty } }

/-! ## The two policies -/

def pa : Expr := .getAttr (.var .principal) "a"
def pb : Expr := .getAttr (.var .principal) "b"
def rc : Expr := .getAttr (.var .resource) "c"
def rd : Expr := .getAttr (.var .resource) "d"

/-- `permit when { (principal.a && principal.b) || (resource.c && resource.d) }` -/
def policyP1 : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, .or (.and pa pb) (.and rc rd)⟩]⟩]

/-- `permit when { (principal.a || resource.c) && (principal.b || resource.d) }` -/
def policyP2 : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, .and (.or pa rc) (.or pb rd)⟩]⟩]

/-! ## Disprove `P1 ≡ P2` with `specimen` -/

/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 2, max := 10, tests := 40000)
  (∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities complexEnv req es →
    isAuthorized req es policyP1 = isAuthorized req es policyP2)

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

/-! # Shared challenge #2 for the specimen-vs-manual race (harder)

Schema: `entity User { a: Bool, b: Bool }; entity Doc { c: Bool, d: Bool };
action view appliesTo (principal: User, resource: Doc)`.

* `policyP1` — `permit when { (principal.a && principal.b) || (resource.c && resource.d) }`
* `policyP2` — `permit when { (principal.a || resource.c) && (principal.b || resource.d) }`

`complexThm` claims they are equivalent on all well-typed inputs. Disprove it. -/

open CedarGen.Relational.ReqEnt
open Cedar.Spec
open Cedar.Data
open Cedar.Validation

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

/-- The (false) claim to disprove. -/
def complexThm : Prop :=
  ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities complexEnv req es →
    isAuthorized req es policyP1 = isAuthorized req es policyP2

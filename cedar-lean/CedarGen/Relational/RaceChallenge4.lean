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

/-! # Shared challenge #4: a (secretly true) policy-equivalence theorem to PROVE

Schema: `entity E { a: Bool, b: Bool, c: Bool }; action act appliesTo (E, E)`.

* `policyLeft`  — `permit when { principal.a && (principal.b || principal.c) }`
* `policyRight` — `permit when { (principal.a && principal.b) || (principal.a && principal.c) }`

`distribThm` claims the two policies are equivalent on all well-typed inputs.
Determine whether it holds and, if so, prove it (no `sorry`). -/

open CedarGen.Relational.ReqEnt
open Cedar.Spec
open Cedar.Data
open Cedar.Validation

def eTyAbc : EntityType := { id := "E", path := [] }
def actAbc : EntityUID := ⟨{ id := "Action", path := [] }, "act"⟩

def abcEnv : TypeEnv :=
  { ets := Map.make [
      (eTyAbc, .standard { ancestors := Set.empty, attrs := Map.make [("a", .required (.bool .anyBool)), ("b", .required (.bool .anyBool)), ("c", .required (.bool .anyBool))], tags := none })]
    acts := Map.make [
      (actAbc, { appliesToPrincipal := Set.make [eTyAbc], appliesToResource := Set.make [eTyAbc], ancestors := Set.empty, context := Map.empty })]
    reqty := { principal := eTyAbc, action := actAbc, resource := eTyAbc, context := Map.empty } }

def ea : Expr := .getAttr (.var .principal) "a"
def eb : Expr := .getAttr (.var .principal) "b"
def ec : Expr := .getAttr (.var .principal) "c"

/-- `permit when { principal.a && (principal.b || principal.c) }` -/
def policyLeft : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, .and ea (.or eb ec)⟩]⟩]

/-- `permit when { (principal.a && principal.b) || (principal.a && principal.c) }` -/
def policyRight : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, .or (.and ea eb) (.and ea ec)⟩]⟩]

/-- The claim to investigate and (if true) prove. -/
def distribThm : Prop :=
  ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities abcEnv req es →
    isAuthorized req es policyLeft = isAuthorized req es policyRight

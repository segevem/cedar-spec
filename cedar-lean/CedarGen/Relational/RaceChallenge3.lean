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

/-! # Shared challenge #3 for the specimen-vs-manual race (interval overlap)

Beyond boolean algebra: a scheduling policy over integer (`Long`) intervals.

Schema: `entity User { availStart: Long, availEnd: Long };
         entity Doc  { reqStart: Long, reqEnd: Long };
         action view appliesTo (principal: User, resource: Doc)`.

A `User` is available during `[availStart, availEnd]`; a `Doc` is requested for
`[reqStart, reqEnd]`. Permit iff the two intervals OVERLAP.

* `policyOverlap` (correct) — `permit when { principal.availStart <= resource.reqEnd
    && resource.reqStart <= principal.availEnd }`
* `policyBuggy`   (a common mistake) — `permit when { principal.availStart <= resource.reqStart
    && resource.reqStart <= principal.availEnd }`  (only checks the Doc's *start* is inside the User window)

`intervalThm` claims they are equivalent on all well-typed inputs. Disprove it. -/

open CedarGen.Relational.ReqEnt
open Cedar.Spec
open Cedar.Data
open Cedar.Validation

def userTy : EntityType := { id := "User", path := [] }
def docTy  : EntityType := { id := "Doc",  path := [] }
def viewAction : EntityUID := ⟨{ id := "Action", path := [] }, "view"⟩

def intervalEnv : TypeEnv :=
  { ets := Map.make [
      (userTy, .standard { ancestors := Set.empty, attrs := Map.make [("availStart", .required .int), ("availEnd", .required .int)], tags := none }),
      (docTy, .standard { ancestors := Set.empty, attrs := Map.make [("reqStart", .required .int), ("reqEnd", .required .int)], tags := none })]
    acts := Map.make [
      (viewAction, { appliesToPrincipal := Set.make [userTy], appliesToResource := Set.make [docTy], ancestors := Set.empty, context := Map.empty })]
    reqty := { principal := userTy, action := viewAction, resource := docTy, context := Map.empty } }

def availStart : Expr := .getAttr (.var .principal) "availStart"
def availEnd   : Expr := .getAttr (.var .principal) "availEnd"
def reqStart   : Expr := .getAttr (.var .resource) "reqStart"
def reqEnd     : Expr := .getAttr (.var .resource) "reqEnd"

/-- CORRECT overlap: `availStart <= reqEnd && reqStart <= availEnd`. -/
def policyOverlap : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, .and (.binaryApp .lessEq availStart reqEnd) (.binaryApp .lessEq reqStart availEnd)⟩]⟩]

/-- BUGGY: `availStart <= reqStart && reqStart <= availEnd` (Doc's start inside User window). -/
def policyBuggy : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, .and (.binaryApp .lessEq availStart reqStart) (.binaryApp .lessEq reqStart availEnd)⟩]⟩]

/-- The (false) claim to disprove. -/
def intervalThm : Prop :=
  ∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities intervalEnv req es →
    isAuthorized req es policyOverlap = isAuthorized req es policyBuggy

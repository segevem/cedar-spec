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

/-! # Testing *policy properties* over well-typed inputs with `specimen_test`

Reproduces a "John Notes" example. With a schema

    entity E { foo: Bool, bar: Bool };
    action a appliesTo { principal: E, resource: E };

the two policy conditions

    principal.foo && resource.bar        -- `fooAndBar`
    resource.bar && principal.foo        -- `barAndFoo`

are **equivalent for all well-typed requests/entities** (both attributes are
present and boolean, so `&&` cannot short-circuit on an error and `∧` commutes),
even though they are *not* equivalent for arbitrary inputs (a missing/erroring
attribute makes operand order observable).

`specimen_test` generates well-typed `(req, es)` from the relational
`WellTypedRequestAndEntities` generator and checks the equivalence against the
functional evaluator `Cedar.Spec.evaluate` — the ground truth.
-/

open CedarGen.Relational.ReqEnt
open CedarGen.Relational.Policy
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

-- Turn up counterexample shrinking (defaults: breadth 8, depth 100).
set_option specimen.shrink true
set_option specimen.shrinkBreadth 36
set_option specimen.shrinkDepth 300

/-! ## Arbitrary / Enum / Shrinkable boilerplate (as in RequestEntitiesTest) -/

instance [Arbitrary α] [Arbitrary β] [LT α] [DecidableLT α] :
    Arbitrary (Map α β) where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
    let mut pairs : List (α × β) := []
    for _ in List.range len do
      pairs := (← Arbitrary.arbitrary, ← Arbitrary.arbitrary) :: pairs
    return Map.make pairs

instance [Enum α] [Enum β] [LT α] [DecidableLT α] :
    Enum (Map α β) where
  enum := do
    let pairs ← Enum.enum (α := List (α × β))
    return Map.make pairs

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

/-! ## Schema: `entity E { foo: Bool, bar: Bool }; action a appliesTo E, E` -/

def eTy : EntityType := { id := "E", path := [] }
def aAction : EntityUID := ⟨{ id := "Action", path := [] }, "a"⟩

def fooBarEnv : TypeEnv :=
  { ets := Map.make [
      (eTy,
       .standard { ancestors := Set.empty,
                   attrs := Map.make [("foo", .required (.bool .anyBool)),
                                      ("bar", .required (.bool .anyBool))],
                   tags := none }) ]
    acts := Map.make [
      (aAction,
       { appliesToPrincipal := Set.make [eTy], appliesToResource := Set.make [eTy],
         ancestors := Set.empty, context := Map.empty }) ]
    reqty :=
      { principal := eTy
        action := aAction
        resource := eTy
        context := Map.empty } }

/-! ## Policy condition expressions -/

def eFooP : Expr := .getAttr (.var .principal) "foo"   -- principal.foo
def eBarR : Expr := .getAttr (.var .resource) "bar"    -- resource.bar

def fooAndBar : Expr := .and eFooP eBarR                -- principal.foo && resource.bar
def barAndFoo : Expr := .and eBarR eFooP                -- resource.bar && principal.foo

/-! ## Property 1 (should PASS): `foo && bar` ≡ `bar && foo` on well-typed inputs -/

set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 3, tests := 30000)
  (∀ req es, WellTypedRequestAndEntities fooBarEnv req es →
    evaluate fooAndBar req es = evaluate barAndFoo req es)

/-! ## Property 2 (control — should find a COUNTEREXAMPLE):
`principal.foo` is *not* equivalent to `resource.bar` (independent booleans). -/

set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 3, max := 3, tests := 30000)
  (∀ req es, WellTypedRequestAndEntities fooBarEnv req es →
    evaluate eFooP req es = evaluate eBarR req es)

set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 3, max := 3, tests := 30000)
  (∀ req es,
    evaluate eFooP req es = evaluate eBarR req es)

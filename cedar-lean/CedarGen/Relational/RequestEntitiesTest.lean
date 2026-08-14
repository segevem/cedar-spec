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

/-! # Test: derive a generator for well-typed (request, entities) given a TypeEnv

Derives `WellTypedRequestAndEntities` in the mode
`(fun env => ∃ req es, WellTypedRequestAndEntities env req es)` and validates
the samples against the *functional* Lean validators
(`instanceOfRequestType` / `instanceOfSchema`). -/

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
set_option specimen.textOutput 3
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ## Arbitrary/Enum instances for base types (mirrors SchemaTest/TypeOfTest) -/

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

/-! ## Derive the generator -/

set_option trace.Meta.synthInstance false
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
#time derive_mutual
  generator (fun env => ∃ req es, WellTypedRequestAndEntities env req es)

/-! ## Fixed schema for validation (a simple User/Photo schema) -/

def userTy : EntityType := { id := "User", path := [] }
def photoTy : EntityType := { id := "Photo", path := [] }
def viewAction : EntityUID := ⟨{ id := "Action", path := [] }, "view"⟩

def testEnv : TypeEnv :=
  { ets := Map.make [
      (userTy,
       .standard { ancestors := Set.empty,
                   attrs := Map.make [("name", .required .string), ("age", .required .int)],
                   tags := none }),
      (photoTy,
       .standard { ancestors := Set.empty,
                   attrs := Map.make [("private", .required (.bool .anyBool))],
                   tags := none }) ]
    acts := Map.make [
      (viewAction,
       { appliesToPrincipal := Set.make [userTy], appliesToResource := Set.make [photoTy],
         ancestors := Set.empty, context := Map.empty }) ]
    reqty :=
      { principal := userTy
        action := viewAction
        resource := photoTy
        context := Map.empty } }

/-! ## Validate samples against the functional spec -/

def validateReqEnt (n : Nat) (size : Nat) : IO Unit := do
  let env := testEnv
  let mut genOk : Nat := 0
  let mut genFail : Nat := 0
  let mut reqOk : Nat := 0
  let mut esOk : Nat := 0
  let mut bad : Nat := 0
  for _ in List.range n do
    let sample ← try
      let (req, es) ← Gen.runUntil (attempts := .some 2000)
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (req, es) => WellTypedRequestAndEntities env req es) size)
        size
      pure (some (req, es))
    catch _ => pure none
    match sample with
    | none => genFail := genFail + 1
    | some (req, es) =>
      genOk := genOk + 1
      let rOk := instanceOfRequestType req env
      let eOk := (instanceOfSchema es env).isOk
      if rOk then reqOk := reqOk + 1
      if eOk then esOk := esOk + 1
      if !(rOk && eOk) then
        bad := bad + 1
        if bad ≤ 5 then
          IO.println s!"MISMATCH (reqOk={rOk}, esOk={eOk}):"
          IO.println s!"  req = {repr req}"
          IO.println s!"  es  = {repr es}"
  IO.println s!"\n=== (req, es) validation ({n} attempts, size={size}) ==="
  IO.println s!"  Generated:            {genOk}"
  IO.println s!"  Gen failed:           {genFail}"
  IO.println s!"  instanceOfRequestType: {reqOk} / {genOk}"
  IO.println s!"  instanceOfSchema ok:   {esOk} / {genOk}"
  IO.println s!"  Mismatches:           {bad}"

#time #eval validateReqEnt 200 6

/-! ## Soundness via `specimen_test`: the relation implies the functional spec

`specimen_test` generates `(req, es)` from the relation (env fixed to `testEnv`,
a fully-input constant) and checks that the *functional* validators accept them.
A pass means every generated sample is well-typed per the Lean ground truth. -/
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


set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 1, tests := 20000)
  (∀ req es, WellTypedRequestAndEntities testEnv req es →
    instanceOfRequestType req testEnv = true)

set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 1, tests := 20000)
  (∀ req es, WellTypedRequestAndEntities testEnv req es →
    (instanceOfSchema es testEnv).isOk = true)

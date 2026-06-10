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

import CedarGen.Relational.TypeOf
import CedarGen.Schema
import Specimen

/-! # Test: derive generators from the relational typing judgement

Uses `derive_mutual` to derive generators from the `HasType` relation.
Check the derive_mutual widget output for schedule quality (colors).
-/

open CedarGen.Relational
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.textOutput 2
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

#print Map

instance [Arbitrary α] [Arbitrary β] [LT α] [DecidableLT α] :
    Arbitrary (Map α β) where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 4 (by omega)
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

-- instance : Plausible.Arbitrary TypedExpr where
--   arbitrary := do
--     let p ← Plausible.Arbitrary.arbitrary (α := Prim)
--     let ty ← Plausible.Arbitrary.arbitrary (α := CedarType)
--     return .lit p ty

deriving instance Enum for
  Var, ExtFun, UInt64, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
  Qualified

deriving instance Enum for EntityType

instance : Enum CedarType where
  enum := EnumeratorCombinators.oneOfWithDefault (pure .int) [
    pure .int,
    pure .string,
    do let b ← Enum.enum (α := BoolType); return .bool b,
    do let e ← Enum.enum (α := EntityType); return .entity e,
    do let x ← Enum.enum (α := ExtType); return .ext x
  ]

-- Workaround for strata-org/specimen#19: derive_mutual generates overly-restrictive
-- [Enum α] [DecidableEq α] constraints on type parameters of parameterized inductives.
instance : Enum EntitySchemaEntry where
  enum := EnumeratorCombinators.oneOfWithDefault
    (pure (.standard { ancestors := Set.empty, attrs := Map.empty, tags := none })) [
    pure (.standard { ancestors := Set.empty, attrs := Map.empty, tags := none }),
    pure (.enum (Set.make ["a", "b"]))
  ]

instance : Enum ActionSchemaEntry where
  enum := pure { appliesToPrincipal := Set.empty, appliesToResource := Set.empty,
                 ancestors := Set.empty, context := Map.empty }

deriving instance DecidableEq for ActionSchemaEntry

-- instance : Enum TypedExpr where
--   enum := do
--     let p ← Enum.enum (α := Prim)
--     let ty ← Enum.enum (α := CedarType)
--     return .lit p ty

set_option trace.Meta.synthInstance false

derive_mutual
  (fun c env ty => ∃ x tx c', HasType x c env tx ty c')

/-! ## Test: generate well-typed expressions -/

def testEnv : TypeEnv :=
  { ets := Map.make [
      ({ id := "User", path := [] },
       .standard { ancestors := Set.empty, attrs := Map.make [("name", .required .string), ("age", .required .int)], tags := none })]
    acts := Map.make [
      (⟨{ id := "Action", path := [] }, "view"⟩,
       { appliesToPrincipal := Set.empty, appliesToResource := Set.empty, ancestors := Set.empty, context := Map.empty })]
    reqty :=
      { principal := { id := "User", path := [] }
        action := ⟨{ id := "Action", path := [] }, "view"⟩
        resource := { id := "User", path := [] }
        context := Map.empty } }

#eval do
  let caps : Capabilities := []
  let ty : CedarType := .set (.bool .tt)
  IO.println s!"Generating expressions of type: {repr ty}\n"
  for structSize in [20] do
    try
      let (x, _tx, _c') ← Gen.run
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (r : Expr × TypedExpr × Capabilities) => HasType r.1 caps testEnv r.2.1 ty r.2.2) structSize)
          10
      IO.println s!"  structSize={structSize}:\n\n{repr x}\n"
    catch _ =>
      IO.println s!"  structSize={structSize}:\n\n (failed)\n"

/-! ## Property-based test: relational spec agrees with functional spec

Generates 10,000 well-typed expressions from the relational `HasType`,
then checks each against the functional `Cedar.Validation.typeOf`. -/

def checkOne (ty : CedarType) (structSize arbSize : Nat) : IO String := do
  let caps : Capabilities := []
  let env := testEnv
  let (x, tx, c') ← Gen.run
    (ArbitrarySizedSuchThat.arbitrarySizedST
      (fun (r : Expr × TypedExpr × Capabilities) => HasType r.1 caps env r.2.1 ty r.2.2) structSize)
    arbSize
  let funcResult := Cedar.Validation.typeOf x caps env
  match funcResult with
  | .ok (funcTx, funcC') =>
    if funcTx == tx && funcC' == c' then
      return s!"PASS: {repr x}"
    else
      return s!"FAIL:\n  expr={repr x}\n  rel_type={repr tx.typeOf}\n  fun_type={repr funcTx.typeOf}"
  | .error e =>
    return s!"ERROR: {repr e} for {repr x}"

#eval checkOne .int 0 3
#eval checkOne (.bool .ff) 0 3
#eval checkOne .string 0 3
#eval checkOne (.bool .tt) 0 3
#eval checkOne (.bool .anyBool) 2 3
#eval checkOne (.bool .tt) 2 3
#eval checkOne (.bool .ff) 2 3
#eval checkOne (.bool .anyBool) 5 4

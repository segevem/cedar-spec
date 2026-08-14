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

import CedarGen.Relational.TypeOfPartial
import CedarGen.Schema
import Specimen

/-! # Test: derive generators from the PARTIAL-type-directed typing relation

The generator is driven by a `PartialCedarType` *demand* (input) and produces the
expression together with its concrete `CedarType` (output). Compare against
`TypeOfLeanTest.lean`, whose generator is driven by a concrete `CedarType` input.
-/

open CedarGen.Relational.Partial
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible
open Scoring Schedules

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.textOutput 3
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

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

instance : Plausible.Arbitrary Expr where
  arbitrary := return .lit (.bool true)

instance : Plausible.Arbitrary Key where
  arbitrary := return .attr ""

instance : Enum Expr where
  enum := pure (.lit (.bool true))

instance : Enum Key where
  enum := pure (.attr "")

deriving instance Enum for
  Var, ExtFun, UInt64, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
  Qualified

deriving instance Enum for EntityType

instance : Enum CedarType where
  enum := EnumeratorCombinators.oneOfWithDefault (pure .int) [
    pure .int,
    pure .string,
    do let b ← Enum.enum (α := BoolType); return .bool b,
    pure (.entity { id := "User", path := [] }),
    pure (.entity { id := "Group", path := [] }),
    pure (.entity { id := "Document", path := [] }),
    pure (.entity { id := "Action", path := [] }),
    do let x ← Enum.enum (α := ExtType); return .ext x
  ]

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

set_option trace.Meta.synthInstance false
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.precomputeWeights true in
#time derive_mutual
  generator (fun env c pt => ∃ x ty cout, HasType x c env pt ty cout)

/-! ## Test environment (identical to TypeOfLeanTest) -/

def testEnv : TypeEnv :=
  { ets := Map.make [
      ({ id := "User", path := [] },
       .standard {
         ancestors := Set.make [{ id := "Group", path := [] }],
         attrs := Map.make [
           ("name", .required .string),
           ("age", .required .int),
           ("active", .required (.bool .anyBool)),
           ("email", .optional .string),
           ("manager", .optional (.entity { id := "User", path := [] }))],
         tags := .some .string }),
      ({ id := "Group", path := [] },
       .standard {
         ancestors := Set.empty,
         attrs := Map.make [
           ("name", .required .string),
           ("public", .required (.bool .anyBool))],
         tags := none }),
      ({ id := "Document", path := [] },
       .standard {
         ancestors := Set.empty,
         attrs := Map.make [
           ("owner", .required (.entity { id := "User", path := [] })),
           ("title", .required .string),
           ("score", .optional .int)],
         tags := .some .int })]
    acts := Map.make [
      (⟨{ id := "Action", path := [] }, "view"⟩,
       { appliesToPrincipal := Set.empty, appliesToResource := Set.empty,
         ancestors := Set.empty, context := Map.empty }),
      (⟨{ id := "Action", path := [] }, "edit"⟩,
       { appliesToPrincipal := Set.empty, appliesToResource := Set.empty,
         ancestors := Set.make [⟨{ id := "Action", path := [] }, "view"⟩],
         context := Map.empty })]
    reqty :=
      { principal := { id := "User", path := [] }
        action := ⟨{ id := "Action", path := [] }, "edit"⟩
        resource := { id := "Document", path := [] }
        context := Map.make [
          ("ip", .required .string),
          ("mfa", .required (.bool .anyBool)),
          ("level", .optional .int)] } }

/-! ## Property-based test: generated expressions typecheck against the functional spec

Drive the generator with a `PartialCedarType` demand. Since the concrete type is now
an output, we (1) check the produced type `ty` fills the demand `pt`, and (2) check
the functional `typeOf` agrees on both the type and the output capabilities. -/

private def capsSubset (c₁ c₂ : Capabilities) : Bool :=
  c₁.all (c₂.contains ·)

private def capsEq (c₁ c₂ : Capabilities) : Bool :=
  capsSubset c₁ c₂ && capsSubset c₂ c₁

def propertyTest (n : Nat) (s : Nat) (demand : PartialCedarType) : IO Unit := do
  let caps : Capabilities := [
    (.var .principal, .attr "email"),
    (.var .principal, .attr "manager"),
    (.var .resource, .attr "score"),
    (.var .principal, .tag (.lit (.string "role"))),
    (.var .resource, .tag (.lit (.string "priority")))]
  let env := testEnv
  let mut passed : Nat := 0
  let mut failed : Nat := 0
  let mut capsFailed : Nat := 0
  let mut fillFailed : Nat := 0
  let mut genFailed : Nat := 0
  let startNs ← IO.monoNanosNow
  for _ in List.range n do
    try
      let (x, filler, cout) ← Gen.runUntil (attempts := .some 1)
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (e, fe, cout) => HasType e caps env demand fe cout) s)
        5
      -- Reconstruct the complete type by plugging the filler back into the demand.
      let ty := plug demand filler
      let funcResult := Cedar.Validation.typeOf x caps env
      match funcResult with
      | .ok (funcTx, funcCaps) =>
        if funcTx.typeOf != ty then
          failed := failed + 1
          if failed ≤ 5 then
            IO.println s!"FAIL type: {repr x}\n  demand={repr demand} filler={repr filler} rel={repr ty} fun={repr funcTx.typeOf}"
        else if !capsEq cout funcCaps then
          capsFailed := capsFailed + 1
          if capsFailed ≤ 5 then
            IO.println s!"FAIL caps: {repr x}\n  rel={repr cout} fun={repr funcCaps}"
        else
          passed := passed + 1
      | .error e =>
        failed := failed + 1
        if failed ≤ 5 then
          IO.println s!"ERROR: {repr e} for {repr x}"
    catch _ =>
      genFailed := genFailed + 1
  let endNs ← IO.monoNanosNow
  let elapsedMs := (endNs - startNs).toFloat / 1000000.0
  IO.println s!"\n=== demand={repr demand} size={s} ({n} attempted, {elapsedMs}ms) ==="
  IO.println s!"  Passed:        {passed}"
  IO.println s!"  Type failures: {failed}"
  IO.println s!"  Caps failures: {capsFailed}"
  IO.println s!"  Fill failures: {fillFailed}"
  IO.println s!"  Gen failures:  {genFailed}"

-- Any type (hole), entities, and sets — exercises the partial-demand paths.
#time #eval! propertyTest 200 8 .hole
#time #eval! propertyTest 200 8 .entity
#time #eval! propertyTest 200 8 (.set .hole)

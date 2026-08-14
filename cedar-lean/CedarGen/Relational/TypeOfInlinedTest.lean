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

import CedarGen.Relational.TypeOfInlined
import CedarGen.Schema
import Specimen

/-! # Test: derive generators from the INLINED relational typing judgement

Uses `derive_mutual` to derive generators from the inlined `HasType` relation.
Compare performance against `TypeOfTest.lean` (factored version).
-/

open CedarGen.Relational.Inlined
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
    do let e ← Enum.enum (α := EntityType); return .entity e,
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
set_option specimen.scoreType "Scoring.GradedUniformDensityScore" in
#time derive_mutual
  generator (fun env r c ty => ∃ x tx c', HasType x c env tx ty c' r)

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

/-! ## Property-based test: relational spec agrees with functional spec -/

def propertyTest (n : Nat) : IO Unit := do
  let caps : Capabilities := []
  let env := testEnv
  let types := #[CedarType.int]
  let mut passed : Nat := 0
  let mut failed : Nat := 0
  let mut genFailed : Nat := 0
  let mut checkFailed : Nat := 0
  let sizes : Array Nat := #[1]
  let mut timings : Array (String × Nat × Nat × Float) := #[]
  for ty in types do
    for structSize in sizes do
      let iters := n / (types.size * sizes.size)
      let startNs ← IO.monoNanosNow
      let mut localPassed : Nat := 0
      let mut localFailed : Nat := 0
      for _ in List.range iters do
        try
          let (x, otx, oc') ← Gen.runUntil (attempts := .some 1)
            (ArbitrarySizedSuchThat.arbitrarySizedST
              (fun (e, tye, c) => HasType e caps env tye (some ty) c .ok) structSize)
            1
          let (tx, c') := match otx, oc' with
            | some tx, some c' => (tx, c')
            | _, _ => unreachable!
          match true with
          | true =>
            let funcResult := Cedar.Validation.typeOf x caps env
            match funcResult with
            | .ok (funcTx, funcC') =>
              if funcTx == tx && funcC' == c' then
                passed := passed + 1
                localPassed := localPassed + 1
              else
                failed := failed + 1
                localFailed := localFailed + 1
                if failed ≤ 5 then
                  IO.println s!"FAIL: {repr x}\n  rel={repr tx.typeOf} fun={repr funcTx.typeOf}"
            | .error e =>
              failed := failed + 1
              localFailed := localFailed + 1
              if failed ≤ 5 then
                IO.println s!"ERROR: {repr e} for {repr x}"
          | false =>
            checkFailed := checkFailed + 1
            if checkFailed ≤ 5 then
              IO.println s!"CHECKER FALSE: {repr x}\n  ty={repr ty} tx={repr tx.typeOf}"
        catch _ =>
          genFailed := genFailed + 1
      let endNs ← IO.monoNanosNow
      let elapsedMs := (endNs - startNs).toFloat / 1000000.0
      timings := timings.push (s!"{repr ty}", structSize, iters, elapsedMs)
  IO.println s!"\n=== Timing breakdown ==="
  IO.println "type\tsize\titers\tms\tms/iter"
  for (tyStr, sz, iters, ms) in timings do
    let perIter := if iters > 0 then ms / iters.toFloat else 0.0
    IO.println s!"{tyStr}\t{sz}\t{iters}\t{ms}\t{perIter}"
  IO.println s!"\n=== Results ({passed + failed + genFailed + checkFailed} attempted) ==="
  IO.println s!"  Passed:        {passed}"
  IO.println s!"  Failed:        {failed}"
  IO.println s!"  Gen failures:  {genFailed}"
  IO.println s!"  Check failed:  {checkFailed}"

#time #eval propertyTest 1

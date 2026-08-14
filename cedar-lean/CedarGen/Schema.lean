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

import Cedar.Spec
import Cedar.Validation.Types
import Specimen
import CedarGen.Prim
import CedarGen.Data

/-! Arbitrary instances for Cedar.Validation types: CedarType, Schema, etc.

These generators produce *syntactically valid* schemas and types.
For *semantically valid* (well-formed) schemas, see the constrained
generators that use `derive_generator` on well-formedness relations.
-/

namespace CedarGen

open Cedar.Spec
open Cedar.Validation
open Cedar.Data
open Plausible

/-! ## BoolType -/

instance : Arbitrary BoolType where
  arbitrary := Gen.elements [.anyBool, .tt, .ff] (by decide)

/-! ## ExtType -/

instance : Arbitrary ExtType where
  arbitrary := Gen.elements [.decimal, .ipAddr, .datetime, .duration] (by decide)

/-! ## Qualified -/

instance [Arbitrary α] : Arbitrary (Qualified α) where
  arbitrary := do
    let a ← Arbitrary.arbitrary
    let isReq ← Gen.chooseAny Bool
    if isReq then return .required a
    else return .optional a

/-! ## CedarType

CedarType is recursive via .set and .record. We use fuel.
-/

private partial def genCedarType (fuel : Nat) : Gen CedarType := do
  if fuel = 0 then
    Gen.elements [.int, .string, .bool .anyBool, .bool .tt, .bool .ff] (by decide)
  else
    let ⟨choice, _⟩ ← Gen.choose Nat 0 9 (by omega)
    match choice with
    | 0 => return .bool (← Arbitrary.arbitrary)
    | 1 => return .int
    | 2 => return .string
    | 3 => return .entity (← Arbitrary.arbitrary)
    | 4 => return .ext (← Arbitrary.arbitrary)
    | 5 | 6 => return .set (← genCedarType (fuel - 1))
    | _ => do
      let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
      let mut pairs : List (Attr × Qualified CedarType) := []
      for _ in List.range len do
        let k ← Arbitrary.arbitrary (α := String)
        let ty ← genCedarType (fuel - 1)
        let isReq ← Gen.chooseAny Bool
        let qt := if isReq then Qualified.required ty else Qualified.optional ty
        pairs := (k, qt) :: pairs
      return .record (Map.make pairs)

instance arbCedarType : Arbitrary CedarType where
  arbitrary := genCedarType 3

/-! ## EntitySchemaEntry -/

private def genStandardSchemaEntry : Gen StandardSchemaEntry := do
  let ⟨numAncestors, _⟩ ← Gen.choose Nat 0 3 (by omega)
  let mut ancestors : List EntityType := []
  for _ in List.range numAncestors do
    ancestors := (← Arbitrary.arbitrary) :: ancestors
  let ⟨numAttrs, _⟩ ← Gen.choose Nat 0 4 (by omega)
  let mut attrs : List (Attr × Qualified CedarType) := []
  for _ in List.range numAttrs do
    let k ← Arbitrary.arbitrary (α := String)
    let ty ← arbCedarType.arbitrary
    let isReq ← Gen.chooseAny Bool
    let qt := if isReq then Qualified.required ty else Qualified.optional ty
    attrs := (k, qt) :: attrs
  let hasTags ← Gen.chooseAny Bool
  let tags ← if hasTags then (do
      let t ← arbCedarType.arbitrary
      pure (some t))
    else pure none
  return { ancestors := Set.make ancestors, attrs := Map.make attrs, tags }

instance : Arbitrary EntitySchemaEntry where
  arbitrary := do
    let ⟨useEnum, _⟩ ← Gen.choose Nat 0 4 (by omega)
    if useEnum = 0 then
      let ⟨numEids, _⟩ ← Gen.choose Nat 1 5 (by omega)
      let mut eids : List String := []
      for _ in List.range numEids do
        eids := (← Arbitrary.arbitrary (α := String)) :: eids
      return .enum (Set.make eids)
    else
      return .standard (← genStandardSchemaEntry)

/-! ## ActionSchemaEntry -/

instance : Arbitrary ActionSchemaEntry where
  arbitrary := do
    let ⟨numP, _⟩ ← Gen.choose Nat 1 3 (by omega)
    let mut principals : List EntityType := []
    for _ in List.range numP do
      principals := (← Arbitrary.arbitrary) :: principals
    let ⟨numR, _⟩ ← Gen.choose Nat 1 3 (by omega)
    let mut resources : List EntityType := []
    for _ in List.range numR do
      resources := (← Arbitrary.arbitrary) :: resources
    let ⟨numAnc, _⟩ ← Gen.choose Nat 0 2 (by omega)
    let mut ancestors : List EntityUID := []
    for _ in List.range numAnc do
      ancestors := (← Arbitrary.arbitrary) :: ancestors
    let ⟨numCtx, _⟩ ← Gen.choose Nat 0 3 (by omega)
    let mut ctx : List (Attr × Qualified CedarType) := []
    for _ in List.range numCtx do
      let k ← Arbitrary.arbitrary (α := String)
      let ty ← arbCedarType.arbitrary
      let isReq ← Gen.chooseAny Bool
      let qt := if isReq then Qualified.required ty else Qualified.optional ty
      ctx := (k, qt) :: ctx
    return {
      appliesToPrincipal := Set.make principals
      appliesToResource := Set.make resources
      ancestors := Set.make ancestors
      context := Map.make ctx
    }

/-! ## Schema -/

instance arbSchema : Arbitrary Schema where
  arbitrary := do
    let ⟨numEts, _⟩ ← Gen.choose Nat 1 5 (by omega)
    let mut ets : List (EntityType × EntitySchemaEntry) := []
    for _ in List.range numEts do
      let et ← Arbitrary.arbitrary (α := EntityType)
      let entry ← Arbitrary.arbitrary (α := EntitySchemaEntry)
      ets := (et, entry) :: ets
    let ⟨numActs, _⟩ ← Gen.choose Nat 1 4 (by omega)
    let mut acts : List (EntityUID × ActionSchemaEntry) := []
    for _ in List.range numActs do
      let uid ← Arbitrary.arbitrary (α := EntityUID)
      let entry ← Arbitrary.arbitrary (α := ActionSchemaEntry)
      acts := (uid, entry) :: acts
    return { ets := Map.make ets, acts := Map.make acts }

/-! ## RequestType -/

instance : Arbitrary RequestType where
  arbitrary := do
    let principal ← Arbitrary.arbitrary
    let action ← Arbitrary.arbitrary
    let resource ← Arbitrary.arbitrary
    let ⟨numCtx, _⟩ ← Gen.choose Nat 0 3 (by omega)
    let mut ctx : List (Attr × Qualified CedarType) := []
    for _ in List.range numCtx do
      let k ← Arbitrary.arbitrary (α := String)
      let ty ← arbCedarType.arbitrary
      let isReq ← Gen.chooseAny Bool
      let qt := if isReq then Qualified.required ty else Qualified.optional ty
      ctx := (k, qt) :: ctx
    return {
      principal
      action
      resource
      context := Map.make ctx
    }

/-! ## TypeEnv -/

instance : Arbitrary TypeEnv where
  arbitrary := do
    let schema ← arbSchema.arbitrary
    let reqty ← Arbitrary.arbitrary (α := RequestType)
    return { ets := schema.ets, acts := schema.acts, reqty }

end CedarGen

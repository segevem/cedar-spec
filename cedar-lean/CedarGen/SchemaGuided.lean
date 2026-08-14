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
import CedarGen.Expr
import CedarGen.Value
import CedarGen.Schema
import CedarGen.Policy

/-! Schema-guided generators.

These generators produce Cedar values (entities, requests, policies) that
are consistent with a given schema. This mirrors the Rust `SchemaGen` trait
in cedar-policy-generators which generates well-formed inputs guided by schema
information.
-/

namespace CedarGen

open Cedar.Spec
open Cedar.Validation
open Cedar.Data
open Plausible

/-! ## Picking schema-consistent types and UIDs -/

/-- Pick a random entity type that exists in the schema -/
def genEntityTypeFromSchema (schema : Schema) : Gen EntityType := do
  let types := schema.ets.keys.toList
  if h : 0 < types.length then
    Gen.elements types h
  else
    Arbitrary.arbitrary

/-- Pick a random action UID that exists in the schema -/
def genActionUIDFromSchema (schema : Schema) : Gen EntityUID := do
  let actions := schema.acts.keys.toList
  if h : 0 < actions.length then
    Gen.elements actions h
  else
    Arbitrary.arbitrary

/-- Generate a valid EID for a given entity type (respects enum variants) -/
def genValidEid (schema : Schema) (ety : EntityType) : Gen String := do
  match schema.ets.find? ety with
  | some (.enum variants) =>
    let varList := variants.toList
    if h : 0 < varList.length then
      Gen.elements varList h
    else pure "eid0"
  | _ => GeneratorCombinators.elementsWithDefault "eid0" ["eid0", "eid1", "eid2"]

/-- Pick a random entity UID whose type exists in the schema -/
def genEntityUIDFromSchema (schema : Schema) : Gen EntityUID := do
  let ty ← genEntityTypeFromSchema schema
  let eid ← genValidEid schema ty
  return { ty, eid }

/-! ## Generating values conforming to a CedarType -/

/-- Generate a Value that conforms to the given CedarType -/
partial def genValueForType (schema : Schema) (ty : CedarType) (fuel : Nat := 3) : Gen Value := do
  match ty with
  | .bool _ => do
    let b ← Gen.chooseAny Bool
    return .prim (.bool b)
  | .int => do
    let ⟨i, _⟩ ← Gen.choose Int (-1000) 1000 (by omega)
    return .prim (.int (Int64.ofInt i))
  | .string => do
    let s ← Arbitrary.arbitrary (α := String)
    return .prim (.string s)
  | .entity ety => do
    let eid ← genValidEid schema ety
    return .prim (.entityUID { ty := ety, eid })
  | .set elemTy =>
    if fuel = 0 then return .set (Set.make [])
    else do
      let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
      let mut elems : List Value := []
      for _ in List.range len do
        elems := (← genValueForType schema elemTy (fuel - 1)) :: elems
      return .set (Set.make elems)
  | .record rty =>
    if fuel = 0 then return .record (Map.make [])
    else do
      let mut pairs : List (Attr × Value) := []
      for (attr, qty) in rty.toList do
        let req := qty.isRequired
        let shouldInclude ← if req then pure true else Gen.chooseAny Bool
        if shouldInclude then
          let v ← genValueForType schema qty.getType (fuel - 1)
          pairs := (attr, v) :: pairs
      return .record (Map.make pairs)
  | .ext .decimal => do
    let ⟨d, _⟩ ← Gen.choose Int (-10000) 10000 (by omega)
    return .ext (.decimal (Int64.ofInt d))
  | .ext .ipAddr => do
    let v ← Arbitrary.arbitrary (α := Ext.IPAddr.IPNet)
    return .ext (.ipaddr v)
  | .ext .datetime => do
    let v ← Arbitrary.arbitrary (α := Ext.Datetime)
    return .ext (.datetime v)
  | .ext .duration => do
    let v ← Arbitrary.arbitrary (α := Ext.Datetime.Duration)
    return .ext (.duration v)

/-! ## Generating Entities conforming to a Schema -/

/-- Generate entity data conforming to a given EntitySchemaEntry -/
def genEntityData (schema : Schema) (entry : EntitySchemaEntry) : Gen EntityData := do
  let attrs ← match entry with
    | .standard std => do
      let mut pairs : List (Attr × Value) := []
      for (attr, qty) in std.attrs.toList do
        let req := qty.isRequired
        let shouldInclude ← if req then pure true else Gen.chooseAny Bool
        if shouldInclude then
          let v ← genValueForType schema qty.getType
          pairs := (attr, v) :: pairs
      pure (Map.make pairs)
    | .enum _ => pure Map.empty
  let ancestors ← match entry with
    | .standard std => do
      let mut ancs : List EntityUID := []
      for ancTy in std.ancestors.toList do
        -- Only add ancestors whose type exists in the schema
        if schema.ets.contains ancTy then
          let shouldInclude ← Gen.chooseAny Bool
          if shouldInclude then
            let eid ← genValidEid schema ancTy
            ancs := { ty := ancTy, eid } :: ancs
      pure (Set.make ancs)
    | .enum _ => pure Set.empty
  return { attrs, ancestors, tags := Map.empty }

/-- Generate a set of entities conforming to the schema.
    Includes both regular entities and action entities. -/
def genEntities (schema : Schema) : Gen Entities := do
  let mut allEntities : List (EntityUID × EntityData) := []
  -- Generate regular entities
  for (ety, entry) in schema.ets.toList do
    match entry with
    | .enum variants =>
      -- For enum types, generate one entity per variant
      for v in variants.toList do
        let uid : EntityUID := { ty := ety, eid := v }
        let edata ← genEntityData schema entry
        allEntities := (uid, edata) :: allEntities
    | .standard _ =>
      let ⟨numEntities, _⟩ ← Gen.choose Nat 1 3 (by omega)
      for i in List.range numEntities do
        let eid := s!"eid{i}"
        let uid : EntityUID := { ty := ety, eid }
        let edata ← genEntityData schema entry
        allEntities := (uid, edata) :: allEntities
  -- Generate action entities (required by validateEntities)
  for (actionUid, actionEntry) in schema.acts.toList do
    let actionData : EntityData := {
      attrs := Map.empty,
      ancestors := actionEntry.ancestors,
      tags := Map.empty,
    }
    allEntities := (actionUid, actionData) :: allEntities
  return Map.make allEntities

/-! ## Generating Requests conforming to a Schema -/

/-- Generate a request conforming to the schema (picks a valid action and
    matching principal/resource types) -/
def genRequest (schema : Schema) : Gen Request := do
  let actionUid ← genActionUIDFromSchema schema
  let (principalTy, resourceTy, ctxTy) ← match schema.acts.find? actionUid with
    | some entry => do
      let pList := entry.appliesToPrincipal.toList
      let rList := entry.appliesToResource.toList
      let pTy ← if h : 0 < pList.length then
        Gen.elements pList h
      else genEntityTypeFromSchema schema
      let rTy ← if h : 0 < rList.length then
        Gen.elements rList h
      else genEntityTypeFromSchema schema
      pure (pTy, rTy, entry.context)
    | none => do
      let pTy ← genEntityTypeFromSchema schema
      let rTy ← genEntityTypeFromSchema schema
      pure (pTy, rTy, Map.empty)
  let principalEid ← genValidEid schema principalTy
  let resourceEid ← genValidEid schema resourceTy
  let principal : EntityUID := { ty := principalTy, eid := principalEid }
  let resource : EntityUID := { ty := resourceTy, eid := resourceEid }
  let mut ctxPairs : List (Attr × Value) := []
  for (attr, qty) in ctxTy.toList do
    let req := qty.isRequired
    let shouldInclude ← if req then pure true else Gen.chooseAny Bool
    if shouldInclude then
      let v ← genValueForType schema qty.getType
      ctxPairs := (attr, v) :: ctxPairs
  let context := Map.make ctxPairs
  return { principal, action := actionUid, resource, context }

/-! ## Generating Policies conforming to a Schema -/

/-- Generate a scope that references entities/types from the schema -/
def genSchemaScope (schema : Schema) : Gen Scope :=
  Gen.oneOfWithDefault
    (pure .any)
    [ (do return .eq (← genEntityUIDFromSchema schema)),
      (do return .mem (← genEntityUIDFromSchema schema)),
      (do return .is (← genEntityTypeFromSchema schema)),
      (do
        let ety ← genEntityTypeFromSchema schema
        let uid ← genEntityUIDFromSchema schema
        return .isMem ety uid) ]

/-- Generate a policy whose scopes reference entities/types from the schema -/
def genPolicy (schema : Schema) : Gen Policy := do
  let ⟨n, _⟩ ← Gen.choose Nat 0 99 (by omega)
  let id := s!"policy{n}"
  let effect ← Arbitrary.arbitrary (α := Effect)
  let principalScope : PrincipalScope := .principalScope (← genSchemaScope schema)
  let actionScope ← Gen.oneOfWithDefault
    (do return ActionScope.actionScope (← genSchemaScope schema))
    [ (do
        let ⟨len, _⟩ ← Gen.choose Nat 1 3 (by omega)
        let mut uids : List EntityUID := []
        for _ in List.range len do
          uids := (← genActionUIDFromSchema schema) :: uids
        return ActionScope.actionInAny uids) ]
  let resourceScope : ResourceScope := .resourceScope (← genSchemaScope schema)
  let ⟨numConditions, _⟩ ← Gen.choose Nat 0 2 (by omega)
  let mut conditions : List Condition := []
  for _ in List.range numConditions do
    let kind ← Arbitrary.arbitrary (α := ConditionKind)
    let body ← Arbitrary.arbitrary (α := Expr)
    conditions := { kind, body } :: conditions
  return { id, effect, principalScope, actionScope, resourceScope, condition := conditions }

/-! ## Top-level generation combinators -/

/-- Generate a complete test scenario: schema + entities + request + policies -/
def genTestScenario : Gen (Schema × Entities × Request × List Policy) := do
  let schema ← arbSchema.arbitrary
  let entities ← genEntities schema
  let request ← genRequest schema
  let ⟨numPolicies, _⟩ ← Gen.choose Nat 1 5 (by omega)
  let mut policies : List Policy := []
  for _ in List.range numPolicies do
    policies := (← genPolicy schema) :: policies
  return (schema, entities, request, policies)

#eval genTestScenario.run 0

end CedarGen

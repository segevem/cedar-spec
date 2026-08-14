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

/-! # Relational specification of type instance checking

This module defines `InstanceOf` as an inductive relation, parallel to the
functional `instanceOfType` in `Cedar.Validation.RequestEntityValidator`.

The relation is stated bidirectionally: each constructor describes what
combinations of (value, type, environment) are valid, without privileging
any particular argument as "input" vs "output".

Specimen can derive generators for any mode:
- `(fun ty env => ∃ v, InstanceOf v ty env)` — generate a value of a given type
- `(fun v env => ∃ ty, InstanceOf v ty env)` — infer a type for a value
- `(fun v ty => ∃ env, InstanceOf v ty env)` — generate a schema accepting a value
-/

namespace CedarGen.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Bool subtype relation

  Relates a boolean value to the boolean types it inhabits. -/

inductive InstanceOfBool : Bool → BoolType → Prop where
  | tt : InstanceOfBool true .tt
  | ff : InstanceOfBool false .ff
  | anyTrue : InstanceOfBool true .anyBool
  | anyFalse : InstanceOfBool false .anyBool

/-! ## Extension type relation

  Relates an extension value to its extension type. -/

inductive InstanceOfExt : Ext → ExtType → Prop where
  | decimal : ∀ d, InstanceOfExt (.decimal d) .decimal
  | ipaddr : ∀ ip, InstanceOfExt (.ipaddr ip) .ipAddr
  | datetime : ∀ dt, InstanceOfExt (.datetime dt) .datetime
  | duration : ∀ dur, InstanceOfExt (.duration dur) .duration

/-! ## Entity UID validity

  Relates an entity UID to an environment where it is valid.
  An entity UID is valid if its type exists in the entity schema
  (with a matching EID for enum types) or if it's a declared action. -/

inductive ValidEntityUID : EntityUID → EntitySchema → ActionSchema → Prop where
  | standard :
    ∀ ety eid entry ets acts,
    ets.find? ety = some (.standard entry) →
    ValidEntityUID ⟨ety, eid⟩ ets acts
  | enum :
    ∀ ety eid eids ets acts,
    ets.find? ety = some (.enum eids) →
    eids.contains eid →
    ValidEntityUID ⟨ety, eid⟩ ets acts
  | action :
    ∀ uid ets acts,
    acts.contains uid →
    ValidEntityUID uid ets acts

/-! ## Core value-type instance relation (mutual inductive)

  Relates a value, a Cedar type, and a type environment.
  Mutually defined with list-level helpers for Specimen derivability. -/

mutual

inductive InstanceOf : Value → CedarType → EntitySchema → ActionSchema → Prop where
  | bool :
    ∀ b bty ets acts,
    InstanceOfBool b bty →
    InstanceOf (.prim (.bool b)) (.bool bty) ets acts
  | int :
    ∀ i ets acts,
    InstanceOf (.prim (.int i)) .int ets acts
  | string :
    ∀ s ets acts,
    InstanceOf (.prim (.string s)) .string ets acts
  | entity :
    ∀ ety eid ets acts,
    ValidEntityUID ⟨ety, eid⟩ ets acts →
    InstanceOf (.prim (.entityUID ⟨ety, eid⟩)) (.entity ety) ets acts
  | set :
    ∀ (elems : List Value) elemTy ets acts,
    AllInstanceOf elems elemTy ets acts →
    elems.isSorted →
    InstanceOf (.set (.mk elems)) (.set elemTy) ets acts
  | record :
    ∀ (fields : List (Attr × Value)) (rty : List (Attr × QualifiedType)) ets acts,
    RecordFieldsConform fields rty ets acts →
    fields.isSortedBy Prod.fst →
    rty.isSortedBy Prod.fst →
    InstanceOf (.record (.mk fields)) (.record (.mk rty)) ets acts
  | ext :
    ∀ x xty ets acts,
    InstanceOfExt x xty →
    InstanceOf (.ext x) (.ext xty) ets acts

/-- All values in a list are instances of a type -/
inductive AllInstanceOf : List Value → CedarType → EntitySchema → ActionSchema → Prop where
  | nil : ∀ ty ets acts, AllInstanceOf [] ty ets acts
  | cons : ∀ v vs ty ets acts,
    InstanceOf v ty ets acts →
    AllInstanceOf vs ty ets acts →
    AllInstanceOf (v :: vs) ty ets acts

/-- A list of (key, value) pairs where each value conforms to the declared type -/
inductive RecordFieldsConform : List (Attr × Value) → List (Attr × QualifiedType) → EntitySchema → ActionSchema → Prop where
  | nil : ∀ rty ets acts, RecordFieldsConform [] rty ets acts
  | cons : ∀ k v rest rty qty ets acts,
    (k, qty) ∈ rty →
    InstanceOf v qty.getType ets acts →
    RecordFieldsConform rest rty ets acts →
    RecordFieldsConform ((k, v) :: rest) rty ets acts

end

/-! ## Entity data conformance

  Relates entity data to an entity schema entry and environment.
  States what (uid, data, entry, env) tuples are valid. -/

inductive EntityDataConforms : EntityUID → EntityData → EntitySchemaEntry → EntitySchema → ActionSchema → Prop where
  | standard :
    ∀ uid data (entry : StandardSchemaEntry) ets acts,
    -- Attributes conform to declared types
    InstanceOf (.record data.attrs) (.record entry.attrs) ets acts →
    -- Each ancestor has a type in the declared ancestors set and is valid
    (∀ anc, anc ∈ data.ancestors →
      entry.ancestors.contains anc.ty ∧ ValidEntityUID anc ets acts) →
    -- Tags conform if declared
    (∀ tty, entry.tags = some tty →
      ∀ v, v ∈ data.tags.values → InstanceOf v tty ets acts) →
    -- No tags if not declared
    (entry.tags = none → data.tags = Map.empty) →
    EntityDataConforms uid data (.standard entry) ets acts
  | enum :
    ∀ uid eids ets acts,
    -- EID is one of the declared variants
    eids.contains uid.eid →
    -- Enum entities have empty data
    EntityDataConforms uid ⟨Map.empty, Set.empty, Map.empty⟩ (.enum eids) ets acts

/-! ## Full entity store conformance

  Relates an entity store to a type environment. -/

inductive EntitiesConform : Entities → EntitySchema → ActionSchema → Prop where
  | mk :
    ∀ entities ets acts,
    -- Every entity conforms to its schema entry
    (∀ uid data, entities.find? uid = some data →
      ∃ entry, ets.find? uid.ty = some entry ∧
        EntityDataConforms uid data entry ets acts) →
    -- Every declared action exists in the entity store
    (∀ uid, acts.contains uid → entities.contains uid) →
    EntitiesConform entities ets acts

/-! ## Request conformance

  Relates a request to a type environment where it is valid. -/

inductive RequestConforms : Request → RequestType → EntitySchema → ActionSchema → Prop where
  | mk :
    ∀ req reqty ets acts,
    -- Principal has the declared type and is valid
    req.principal.ty = reqty.principal →
    ValidEntityUID req.principal ets acts →
    -- Action matches exactly
    req.action = reqty.action →
    -- Resource has the declared type and is valid
    req.resource.ty = reqty.resource →
    ValidEntityUID req.resource ets acts →
    -- Context conforms to declared context type
    InstanceOf req.context (.record reqty.context) ets acts →
    RequestConforms req reqty ets acts

end CedarGen.Relational

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
import Cedar.Validation
import CedarGen.Relational.Schema
import CedarGen.Relational.Policy

/-! # Relational spec: well-typed request + (minimal) entities given a TypeEnv

Generates a `Request` and a *minimal* `Entities` store that conform to a
`TypeEnv`, in the Specimen-friendly structural style (no `find?`/`∈`/`∀`;
Cedar wrapper types built only in conclusions).

The relation is a **generator/sampler** only. The ground truth for
well-typedness is the *functional* Lean validator
(`Cedar.Validation.instanceOfRequestType` / `instanceOfSchema`); every value
produced here is expected to be accepted by those functions, and this is
checked separately by a property test (see `RequestEntitiesTest.lean`).

## Minimal store

Cedar slices entities before evaluation, so for testing most policy properties
the store only needs the entities the request actually references:

* the **principal** entity (type `reqty.principal`),
* the **resource** entity (type `reqty.resource`), and
* **every declared action** entity (the functional `instanceOfSchema` requires
  every action in `env.acts` to be present in the store).

Each principal/resource entity carries attributes conforming to its declared
entity-schema entry, empty ancestors, and empty tags (empty tags always
conform: the `.none` case wants an empty tag map, and the `.some` case's
`values.all` is vacuously true). Each action entity carries empty attrs/tags
and ancestors equal to its action-schema entry's ancestors, matching
`instanceOfActionSchemaEntry`.

### First-cut restrictions (extend later)

* principal/resource types are assumed to be **standard** (not enum) entity
  types, so they have an attribute record to conform to;
* attribute/context value types are primitives, entities, or extension types
  (nested records and sets are deferred — the functional record check requires
  every *required* attribute to be present, which needs a stronger value
  relation than the existing `InstanceOf`).
-/

namespace CedarGen.Relational.ReqEnt

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open CedarGen.Relational.Policy (InStringList)

/-! ## Valid entity UID *for a given type* (uid as a single output)

Given the entity schema (list) and an entity type, produce a valid `EntityUID`
of that type. Unlike `Policy.IsValidEntityUID` (which takes the full `⟨ety,eid⟩`
as one argument — mixing a bound type with a fresh eid, which Specimen cannot
schedule as either a pure input or a pure output), here the whole `uid` is a
single output the generator *builds*: `⟨ety, eid⟩` with `ety` an input and `eid`
freshly generated (any string for standard entities, an enum member otherwise).
Mirrors `EntitySchema.isValidEntityUID`. -/

inductive UIDForType :
    List (EntityType × EntitySchemaEntry) → EntityType → EntityUID → Prop where
  | standard : ∀ ety eid ancestors attrs tags rest,
      UIDForType
        ((ety, .standard (StandardSchemaEntry.mk (Set.mk ancestors) (Map.mk attrs) tags)) :: rest)
        ety ⟨ety, eid⟩
  | enum : ∀ ety eid eids rest,
      InStringList eids eid →
      UIDForType ((ety, .enum (Set.mk eids)) :: rest) ety ⟨ety, eid⟩
  | there : ∀ ety k entry rest uid,
      ety ≠ k →
      UIDForType rest ety uid →
      UIDForType ((k, entry) :: rest) ety uid

/-! ## Value conformance (structural, primitives + entity)

Mirrors `Cedar.Validation.instanceOfType` for the leaf cases. `entityEntries`
is the entity schema as a raw list. -/

inductive ValueConforms :
    List (EntityType × EntitySchemaEntry) → Value → CedarType → Prop where
  | boolTt : ∀ ents,
      ValueConforms ents (.prim (.bool true)) (.bool .tt)
  | boolFf : ∀ ents,
      ValueConforms ents (.prim (.bool false)) (.bool .ff)
  | boolAnyTrue : ∀ ents,
      ValueConforms ents (.prim (.bool true)) (.bool .anyBool)
  | boolAnyFalse : ∀ ents,
      ValueConforms ents (.prim (.bool false)) (.bool .anyBool)
  | int : ∀ ents i,
      ValueConforms ents (.prim (.int i)) .int
  | str : ∀ ents s,
      ValueConforms ents (.prim (.string s)) .string
  | entity : ∀ ents ety uid,
      UIDForType ents ety uid →
      ValueConforms ents (.prim (.entityUID uid)) (.entity ety)
  -- TODO: extension-typed values (.ext .decimal/.ipAddr/.datetime/.duration).
  -- These must be *well-formed* (valid IPs, datetimes, durations), so generation
  -- should reuse the `Valid{Decimal,Datetime,Duration}` string generators in
  -- TypeOfLean.lean (parsed to `Ext`), NOT `Arbitrary Ext.*` which yields junk.
  -- Deferred: the first-cut schemas (John Notes examples) use no ext attributes.

/-! ## Record conformance (structural over the declared attribute list)

Produces a value for *every* declared attribute, in declared order. Because the
keys come from the (unique-keyed) schema, the resulting record has unique keys,
so `Map.mk` behaves correctly under the functional validator's linear `find?`.
Producing all declared attributes (including optionals) guarantees the
functional record check's "required attribute present" side condition. -/

inductive RecordConforms :
    List (EntityType × EntitySchemaEntry) →
    List (Attr × Value) →
    List (Attr × QualifiedType) → Prop where
  | nil : ∀ ents,
      RecordConforms ents [] []
  | consRequired : ∀ ents k ty v restV restT,
      ValueConforms ents v ty →
      RecordConforms ents restV restT →
      RecordConforms ents ((k, v) :: restV) ((k, .required ty) :: restT)
  | consOptional : ∀ ents k ty v restV restT,
      ValueConforms ents v ty →
      RecordConforms ents restV restT →
      RecordConforms ents ((k, v) :: restV) ((k, .optional ty) :: restT)

/-! ## Attributes for a standard entity type (lookup + record conformance fused)

Produces an attribute record `attrsV` for the standard entity type `ety` by
walking the schema to `ety`'s `.standard` entry and generating a record
conforming to that entry's declared attribute types.

The fusion is deliberate: the declared attribute *type* list is bound by
**destructuring the input schema entry** (`Map.mk attrsTy`), so it is never a
free existential that the scheduler would otherwise fill with an arbitrary
(non-matching) value via `RecordConforms`'s multi-output mode. This keeps a
sound schedule even under `specimen_test`'s forced `multiOutput := true`.

The full schema (`fullEnts`) is threaded separately from the shrinking search
list so entity-typed attribute values are validated against the whole schema. -/

inductive EntityAttrsForType :
    List (EntityType × EntitySchemaEntry) →   -- full schema (for value validation)
    List (EntityType × EntitySchemaEntry) →   -- remaining entries to search
    EntityType → List (Attr × Value) → Prop where
  | here : ∀ fullEnts ety ancestors attrsTy tags rest attrsV,
      RecordConforms fullEnts attrsV attrsTy →
      EntityAttrsForType fullEnts
        ((ety, .standard (StandardSchemaEntry.mk (Set.mk ancestors) (Map.mk attrsTy) tags)) :: rest)
        ety attrsV
  | there : ∀ fullEnts ety k entry rest attrsV,
      ety ≠ k →
      EntityAttrsForType fullEnts rest ety attrsV →
      EntityAttrsForType fullEnts ((k, entry) :: rest) ety attrsV

/-! ## Action entities

Deterministically map each action-schema entry to its entity data:
empty attrs, empty tags, ancestors equal to the entry's ancestors. Matches
`Cedar.Validation.instanceOfSchema.instanceOfActionSchemaEntry`. -/

inductive ActionEntities :
    List (EntityUID × ActionSchemaEntry) →
    List (EntityUID × EntityData) → Prop where
  | nil : ActionEntities [] []
  | cons : ∀ uid principals resources ancestors context rest restED,
      ActionEntities rest restED →
      ActionEntities
        ((uid, ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors) (Map.mk context)) :: rest)
        ((uid, EntityData.mk Map.empty (Set.mk ancestors) Map.empty) :: restED)

/-! ## Top-level: well-typed request + minimal entities

Given `env`, generate a `Request` and minimal `Entities` conforming to it.
Principal/resource are standard entities with conforming attributes; the store
also contains every declared action entity. -/

inductive WellTypedRequestAndEntities : TypeEnv → Request → Entities → Prop where
  | mk : ∀ entityEntries actionEntries pty action rty ctxTy
           principalUID resourceUID pAttrs rAttrs ctxFields actionEds,
      -- request principal/resource: valid UIDs of the declared types
      UIDForType entityEntries pty principalUID →
      UIDForType entityEntries rty resourceUID →
      -- context conforms to the declared context record type
      RecordConforms entityEntries ctxFields ctxTy →
      -- principal/resource entity attributes conform to their schema entries
      EntityAttrsForType entityEntries entityEntries pty pAttrs →
      EntityAttrsForType entityEntries entityEntries rty rAttrs →
      -- one entity per declared action
      ActionEntities actionEntries actionEds →
      WellTypedRequestAndEntities
        (TypeEnv.mk (Map.mk entityEntries) (Map.mk actionEntries)
          (RequestType.mk pty action rty (Map.mk ctxTy)))
        (Request.mk principalUID action resourceUID (Map.mk ctxFields))
        (Map.mk
          ((principalUID, EntityData.mk (Map.mk pAttrs) Set.empty Map.empty) ::
           (resourceUID, EntityData.mk (Map.mk rAttrs) Set.empty Map.empty) ::
           actionEds))

end CedarGen.Relational.ReqEnt

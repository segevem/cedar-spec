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

module

public import Cedar.Spec
public import Cedar.Validation

@[expose] public section

/-! # A constructive description of well-formed type environments

`WfTypeEnv env` describes type environments built in a single pass, so that a derived
generator can produce them directly: entity types are declared one at a time, each standard
entity type choosing its ancestors among the standard entity types declared before it, and
attribute and tag types referring only to entity types declared so far (or to the type being
declared); actions are then built the same way. Choosing the ancestors of a type together with
their own ancestors makes the entity and action hierarchies transitively closed and acyclic
by construction. Like `Typing.lean`, the relations use only structural list patterns (no `∈`,
`find?` or field projections) and build `Map`, `Set` and `TypeEnv` values only in their
conclusions.

`WfTypeEnv` is not `TypeEnv.validateWellFormed`: it does not sort the entity and action maps or
the sets in their entries, it allows empty enumerations and an entity type named `Action`,
and it only produces actions of type `Action` with eids from a fixed pool. Every environment
it describes satisfies `EnvAssumptions` (`Schema.WfTypeEnv.envAssumptions`), and
`wfTypeEnv_validateWellFormed_iff` characterizes those that are well-formed. -/

namespace Cedar.Validation.Relational.Schema

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Entity type membership -/

/-- The entity type occurs in the list. -/
inductive DefinedEntityType : List EntityType → EntityType → Prop where
  | here : ∀ et rest, DefinedEntityType (et :: rest) et
  | there : ∀ et et' rest,
      et ≠ et' →
      DefinedEntityType rest et →
      DefinedEntityType (et' :: rest) et

/-! ## Record-key ordering bound

`KeyAbove lb a` holds when `a` strictly exceeds the lower bound `lb` (`none` is
−∞). Threaded through `WfAttrs` so each successive attribute key strictly
exceeds the previous — making every well-formed attribute list strictly sorted
by key, hence duplicate-free and already canonical (`Map.mk attrs = Map.make
attrs`). -/
inductive KeyAbove : Option Attr → Attr → Prop where
  | none : ∀ a, KeyAbove Option.none a
  | some : ∀ b a, b < a → KeyAbove (Option.some b) a

/-! ## Well-formed CedarType and attributes (mutually recursive) -/

mutual

/-- A type whose entity types occur in `ets`, whose Boolean types are `.anyBool` and whose
    record types are strictly sorted by key. -/
inductive WfCedarType : List EntityType → CedarType → Prop where
  | bool : ∀ ets, WfCedarType ets (.bool .anyBool)
  | int : ∀ ets, WfCedarType ets .int
  | string : ∀ ets, WfCedarType ets .string
  | entity : ∀ ets ety,
      DefinedEntityType ets ety →
      WfCedarType ets (.entity ety)
  | set : ∀ ets ty,
      WfCedarType ets ty →
      WfCedarType ets (.set ty)
  | record : ∀ ets attrs,
      WfAttrs Option.none ets attrs →
      WfCedarType ets (.record (Map.mk attrs))
  | extDecimal : ∀ ets, WfCedarType ets (.ext .decimal)
  | extIPAddr : ∀ ets, WfCedarType ets (.ext .ipAddr)
  | extDatetime : ∀ ets, WfCedarType ets (.ext .datetime)
  | extDuration : ∀ ets, WfCedarType ets (.ext .duration)

/-- Well-formed attribute list, threading a strict lower bound `lb` on keys so
    the generated attribute list is strictly sorted (hence duplicate-free). -/
inductive WfAttrs : Option Attr → List EntityType → List (Attr × QualifiedType) → Prop where
  | nil : ∀ lb ets, WfAttrs lb ets []
  | consRequired : ∀ lb ets attr ty rest,
      KeyAbove lb attr →
      WfCedarType ets ty →
      WfAttrs (Option.some attr) ets rest →
      WfAttrs lb ets ((attr, .required ty) :: rest)
  | consOptional : ∀ lb ets attr ty rest,
      KeyAbove lb attr →
      WfCedarType ets ty →
      WfAttrs (Option.some attr) ets rest →
      WfAttrs lb ets ((attr, .optional ty) :: rest)

end

/-! ## Structural helper relations -/

/-- `et` does not appear in the list. Used to forbid duplicate type names,
    matching Cedar construction, which rejects `DuplicateEntityTypeError`. -/
inductive NotInET : EntityType → List EntityType → Prop where
  | nil  : ∀ et, NotInET et []
  | cons : ∀ et x rest, et ≠ x → NotInET et rest → NotInET et (x :: rest)

/-- List append, as a relation. -/
inductive AppendET : List EntityType → List EntityType → List EntityType → Prop where
  | nil  : ∀ ys, AppendET [] ys ys
  | cons : ∀ x xs ys zs, AppendET xs ys zs → AppendET (x :: xs) ys (x :: zs)

/-! ## Well-formed tags -/

/-- No tags, or a tag type satisfying `WfCedarType`. -/
inductive WfTags : List EntityType → Option CedarType → Prop where
  | none : ∀ ets, WfTags ets .none
  | some : ∀ ets ty,
      WfCedarType ets ty →
      WfTags ets (.some ty)

/-! ## Transitively-closed ancestors, by construction

`built` is the list of standard entities already constructed, each paired with
its own **transitively-closed** ancestor list. A new entity chooses a subset of
them as direct parents; picking parent `p` contributes `p` *and its entire
closed ancestor set* `pset`. Because every entry in `built` already carries its
closure (invariant maintained by `WfEntitiesGo`), the union is itself
transitively closed — so `descendentOf`, which does a one-hop `contains`,
is correct for multi-hop hierarchies. The result is irreflexive and acyclic because parents are
drawn only from *earlier*-built entities (the new entity is not yet in `built`),
and enums never enter `built`, so an enum can never be an ancestor. -/
inductive PickClosedAncestors :
    List (EntityType × List EntityType) → List EntityType → Prop where
  | none : PickClosedAncestors [] []
  | skip : ∀ p pset built chosen,
      PickClosedAncestors built chosen →
      PickClosedAncestors ((p, pset) :: built) chosen
  | pick : ∀ p pset built chosen merged,
      PickClosedAncestors built chosen →
      AppendET pset chosen merged →
      PickClosedAncestors ((p, pset) :: built) (p :: merged)

/-! ## Well-formed entity schema (topological, single pass)

Builds the entity entries in one pass, threading:
* `built` — standard entries so far, each with its closed ancestor list (the
            candidate parents for `PickClosedAncestors`); enums are never added,
            enforcing enum-exclusion from the hierarchy;
* `names` — all type names declared so far (standard + enum), used for attribute
            references and, via `NotInET`, to forbid duplicate type names.

The full `names` list is an output (the first index of `WfEntitySchema`), so that
`WfActionSchema` and `RequestFromAction` see every declared type. Attribute and tag types
may refer to `et :: names`: the type being declared and the types declared before it. -/
inductive WfEntitiesGo :
    List (EntityType × List EntityType) →   -- built (closed-ancestor payload)
    List EntityType →                       -- names so far
    List EntityType →                       -- OUT: all declared names
    List (EntityType × EntitySchemaEntry) → Prop where
  | nil : ∀ built names,
      WfEntitiesGo built names names []
  | standard : ∀ built names et ancestors attrs tags allNames rest,
      NotInET et names →
      PickClosedAncestors built ancestors →
      WfAttrs Option.none (et :: names) attrs →
      WfTags (et :: names) tags →
      WfEntitiesGo ((et, ancestors) :: built) (et :: names) allNames rest →
      WfEntitiesGo built names allNames
        ((et, .standard (StandardSchemaEntry.mk (Set.mk ancestors) (Map.mk attrs) tags)) :: rest)
  | enum : ∀ built names et eids allNames rest,
      NotInET et names →
      WfEntitiesGo built (et :: names) allNames rest →
      WfEntitiesGo built names allNames ((et, .enum (Set.mk eids)) :: rest)

/-- Well-formed entity schema: run the topological construction from empty
    accumulators. The first index is the full list of declared entity-type names. -/
inductive WfEntitySchema : List EntityType → List (EntityType × EntitySchemaEntry) → Prop where
  | mk : ∀ allNames entries,
      WfEntitiesGo [] [] allNames entries →
      WfEntitySchema allNames entries

/-! ## Well-formed principal/resource type lists -/

/-- Every principal type occurs in `ets`. -/
inductive WfPrincipalTypes : List EntityType → List EntityType → Prop where
  | nil : ∀ ets, WfPrincipalTypes ets []
  | cons : ∀ ets p rest,
      DefinedEntityType ets p →
      WfPrincipalTypes ets rest →
      WfPrincipalTypes ets (p :: rest)

/-- Every resource type occurs in `ets`. -/
inductive WfResourceTypes : List EntityType → List EntityType → Prop where
  | nil : ∀ ets, WfResourceTypes ets []
  | cons : ∀ ets r rest,
      DefinedEntityType ets r →
      WfResourceTypes ets rest →
      WfResourceTypes ets (r :: rest)

/-! ## Action hierarchy: transitively-closed ancestors -/

/-- List append for action UIDs, as a relation (the `EntityUID` analogue of `AppendET`). -/
inductive AppendUID : List EntityUID → List EntityUID → List EntityUID → Prop where
  | nil  : ∀ ys, AppendUID [] ys ys
  | cons : ∀ x xs ys zs, AppendUID xs ys zs → AppendUID (x :: xs) ys (x :: zs)

/-- `SelectRemove xs y ys`: `y` is an element of `xs` and `ys` is `xs` without it. Used to draw
    distinct action eids from a fixed pool in `WfActionSchema`. -/
inductive SelectRemove {α} : List α → α → List α → Prop where
  | here  : ∀ x xs,      SelectRemove (x :: xs) x xs
  | there : ∀ x xs y ys, SelectRemove xs y ys → SelectRemove (x :: xs) y (x :: ys)

/-- Transitively-closed action ancestors, by construction — the action analogue of
    `PickClosedAncestors`. `built` is the actions already constructed, each paired with its OWN
    transitively-closed ancestor list. A new action chooses a subset as direct parents; picking
    parent `p` contributes `p` *and its entire closed ancestor set* `pset`. Because every entry in
    `built` already carries its closure (invariant maintained by `WfActionsGo`), the union is
    itself transitively closed, as `ActionSchema.validateWellFormed` requires. Irreflexive and
    acyclic because parents are drawn only from *earlier*-built actions (the new action is not
    yet in `built`). -/
inductive PickClosedActionAncestors :
    List (EntityUID × List EntityUID) → List EntityUID → Prop where
  | none : PickClosedActionAncestors [] []
  | skip : ∀ p pset built chosen,
      PickClosedActionAncestors built chosen →
      PickClosedActionAncestors ((p, pset) :: built) chosen
  | pick : ∀ p pset built chosen merged,
      PickClosedActionAncestors built chosen →
      AppendUID pset chosen merged →
      PickClosedActionAncestors ((p, pset) :: built) (p :: merged)

/-! ## Well-formed action schema entry -/

/-- The entity type of the actions `WfActionSchema` builds.

    Cedar schemas give every action the reserved type `Action` (or a namespaced
    `NS::Action`). The Lean validator does not depend on this (it checks action literals
    against the action schema, whatever their type), but the Rust implementation does, so
    environments with actions of other types are not Cedar schemas. -/
abbrev actionEntityType : EntityType := { id := "Action", path := [] }

/-! ## Well-formed action schema -/

/-- The candidate action eids. `WfActionSchema` draws them without replacement (via
    `SelectRemove`), so the actions it builds are distinct. -/
def actionEidPool : List String :=
  ["a", "b", "c", "d", "e", "foo", "bar", "baz", "id", "name", "owner"]

/-- Topological single-pass construction of the action entries, threading:
    * `built` — actions constructed so far, each paired with its transitively-closed ancestor
                list (the candidate parents for `PickClosedActionAncestors`; the closure invariant
                makes any chosen union itself closed);
    * `avail` — the remaining eid pool, drawn without replacement via `SelectRemove` so action
                UIDs are distinct.
    Each action picks its ancestors from *earlier*-built actions only, so the hierarchy is acyclic
    and transitively closed by construction. Principal, resource and context types are
    well-formed against `ets`. -/
inductive WfActionsGo :
    List EntityType →                       -- ets (principal/resource/context types)
    List (EntityUID × List EntityUID) →     -- built: actions so far, each with closed ancestors
    List String →                           -- avail: remaining eid pool
    List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ∀ ets built avail, WfActionsGo ets built avail []
  | cons : ∀ ets built avail avail' eid ancestors principals resources context rest,
      SelectRemove avail eid avail' →
      PickClosedActionAncestors built ancestors →
      WfPrincipalTypes ets principals →
      WfResourceTypes ets resources →
      WfAttrs Option.none ets context →
      WfActionsGo ets ((⟨actionEntityType, eid⟩, ancestors) :: built) avail' rest →
      WfActionsGo ets built avail
        ((⟨actionEntityType, eid⟩,
          ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors) (Map.mk context)) :: rest)

/-- Well-formed action schema: run the topological construction from empty accumulators, drawing
    distinct eids from `actionEidPool`. -/
inductive WfActionSchema : List EntityType → List (EntityUID × ActionSchemaEntry) → Prop where
  | mk : ∀ ets entries,
      WfActionsGo ets [] actionEidPool entries →
      WfActionSchema ets entries

/-! ## Well-formed request type

The request type of some action: its principal and resource types are among the action's
principal and resource types, and its context type is the action's context type. -/

/-- A request type for one of the actions of the list. -/
inductive RequestFromAction :
    List EntityType →
    List (EntityUID × ActionSchemaEntry) →
    RequestType → Prop where
  | here : ∀ ets acts uid principals resources ancestors context principal resource,
      DefinedEntityType principals principal →
      DefinedEntityType resources resource →
      RequestFromAction ets
        ((uid, ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors) (Map.mk context)) :: acts)
        (RequestType.mk principal uid resource (Map.mk context))
  | there : ∀ ets act acts reqty,
      RequestFromAction ets acts reqty →
      RequestFromAction ets (act :: acts) reqty

/-! ## Type environments -/

/-- A type environment built from an entity schema (`WfEntitySchema`), an action schema over
    its entity types (`WfActionSchema`) and the request type of one of its actions. -/
inductive WfTypeEnv : TypeEnv → Prop where
  | mk : ∀ entityTypes entityEntries actionEntries reqty,
      WfEntitySchema entityTypes entityEntries →
      WfActionSchema entityTypes actionEntries →
      RequestFromAction entityTypes actionEntries reqty →
      WfTypeEnv (TypeEnv.mk (Map.mk entityEntries) (Map.mk actionEntries) reqty)

end Cedar.Validation.Relational.Schema

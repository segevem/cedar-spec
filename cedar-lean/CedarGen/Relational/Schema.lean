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

/-! # Relational specification of well-formed Cedar schemas

Follows the Specimen Cedar example pattern: all relations use structural
list patterns (no ∈, contains, map, or record field access). Cedar wrapper
types (Set, Map, TypeEnv) are constructed only in conclusions.
-/

namespace CedarGen.Relational.Schema

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Entity type membership (structural list traversal) -/

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
attrs`). This mirrors the same threading through `HasTypeRecord` (record
literals) and matches what the schema generator produces after its
`canonicalizeAttrs` post-processing. Without it, `WfAttrs` would admit
duplicate-keyed attribute maps on which `Map.find?` (first match) disagrees
with a structural `MapContains` witness, breaking the typechecker
correspondence for `getAttr`/`hasAttr`. -/
inductive KeyAbove : Option Attr → Attr → Prop where
  | none : ∀ a, KeyAbove Option.none a
  | some : ∀ b a, b < a → KeyAbove (Option.some b) a

/-! ## Well-formed CedarType and attributes (mutually recursive) -/

mutual

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
-- __cedar is reserved name
/-! ## Structural helper relations -/

/-- `et` does not appear in the list. Used to forbid duplicate type names,
    matching Cedar construction, which rejects `DuplicateEntityTypeError`. -/
inductive NotInET : EntityType → List EntityType → Prop where
  | nil  : ∀ et, NotInET et []
  | cons : ∀ et x rest, et ≠ x → NotInET et rest → NotInET et (x :: rest)

/-- List append as a relation, so conclusions stay `::`-only (Specimen-friendly). -/
inductive AppendET : List EntityType → List EntityType → List EntityType → Prop where
  | nil  : ∀ ys, AppendET [] ys ys
  | cons : ∀ x xs ys zs, AppendET xs ys zs → AppendET (x :: xs) ys (x :: zs)

/-! ## Well-formed tags -/

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
transitively closed — so `descendentOf`, which does a one-hop `contains`
(`Types.lean`), is correct for multi-hop hierarchies without any separate
`compute_tc` pass. The result is irreflexive and acyclic because parents are
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

The full `names` list is produced as the OUTPUT (first index of `WfEntitySchema`)
so downstream (`WfActionSchema`, `RequestFromAction`) sees every declared type.
Attribute/tag types reference `et :: names` (self + types declared so far),
mirroring the original spec's reference discipline (self-reference allowed). -/
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

inductive WfPrincipalTypes : List EntityType → List EntityType → Prop where
  | nil : ∀ ets, WfPrincipalTypes ets []
  | cons : ∀ ets p rest,
      DefinedEntityType ets p →
      WfPrincipalTypes ets rest →
      WfPrincipalTypes ets (p :: rest)
-- principle type cannot be action, hopefully
inductive WfResourceTypes : List EntityType → List EntityType → Prop where
  | nil : ∀ ets, WfResourceTypes ets []
  | cons : ∀ ets r rest,
      DefinedEntityType ets r →
      WfResourceTypes ets rest →
      WfResourceTypes ets (r :: rest)
-- see above
/-! ## Action hierarchy: transitively-closed ancestors -/

/-- List append as a relation for action UIDs (the `EntityUID` analogue of `AppendET`), so
    `PickClosedActionAncestors` conclusions stay `::`-only (Specimen-friendly). -/
inductive AppendUID : List EntityUID → List EntityUID → List EntityUID → Prop where
  | nil  : ∀ ys, AppendUID [] ys ys
  | cons : ∀ x xs ys zs, AppendUID xs ys zs → AppendUID (x :: xs) ys (x :: zs)

/-- Pick one element out of a list, returning the remainder. CONSTRUCTIVE selection: given the
    pool it PRODUCES an element + leftover (unlike a `∉`/`NotIn` checker, which can only verify
    a separately-generated element and thus forces generate-and-reject). Used to draw DISTINCT
    action eids from a fixed pool in `WfActionSchema` — no duplicate UIDs, so `RequestFromAction`
    (which walks the raw list) and `Map.mk actionEntries` can't pick different entries for the
    same UID (the desync that made `reqty.context` ≠ `acts[reqty.action].context`). -/
inductive SelectRemove {α} : List α → α → List α → Prop where
  | here  : ∀ x xs,      SelectRemove (x :: xs) x xs
  | there : ∀ x xs y ys, SelectRemove xs y ys → SelectRemove (x :: xs) y (x :: ys)
-- Its MANUAL uniform generator lives in `SchemaTest.lean` (where `Specimen` is imported).

/-- Transitively-closed action ancestors, by construction — the action analogue of
    `PickClosedAncestors`. `built` is the actions already constructed, each paired with its OWN
    transitively-closed ancestor list. A new action chooses a subset as direct parents; picking
    parent `p` contributes `p` *and its entire closed ancestor set* `pset`. Because every entry in
    `built` already carries its closure (invariant maintained by `WfActionsGo`), the union is
    itself transitively closed — so the generated action hierarchy satisfies Cedar's
    well-formedness and Lean's `validateWellFormed` transitivity check (which the SymCC compiler
    runs via `CompiledPolicy.compile`; the definitional validator does not, so this was previously
    unconstrained). Irreflexive and acyclic because parents are drawn only from *earlier*-built
    actions (the new action is not yet in `built`). -/
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

/-- The reserved Cedar entity type for all action UIDs.

    Cedar mandates that every action entity has the reserved type `Action` (or a
    namespaced `NS::Action`); this is not expressible any other way through
    cedar-policy's schema APIs. The relational spec previously left the action
    UID type unconstrained, so it generated schemas whose actions had arbitrary
    types (e.g. `name::"doc1"`). Such schemas are only reachable via the
    `TypeEnv`→protobuf path and are NOT valid Cedar, so `validation-drt` aborts:
    cedar-policy rejects a policy referencing the action (`for policy `policy0`,
    unrecognized entity type `name`; did you mean `c::c`?`) while the Lean
    validator accepts it (it keys entity-literal validity on action-set
    membership, `Typechecker.lean:64`, not on the type name being `Action`).

    Pinning the type here keeps generated schemas in the well-formed Cedar space
    where cedar-policy and the Lean validator agree. -/
abbrev actionEntityType : EntityType := { id := "Action", path := [] }

/-! ## Well-formed action schema -/

/-- Fixed pool of candidate action eids, drawn WITHOUT replacement (via `SelectRemove`) so the
    generated action UIDs are automatically DISTINCT — no duplicate UID can slip in, so
    `Map.mk actionEntries` and `RequestFromAction` agree on every UID's entry. -/
def actionEidPool : List String :=
  ["a", "b", "c", "d", "e", "foo", "bar", "baz", "id", "name", "owner"]

/-- Topological single-pass construction of the action entries, threading:
    * `built` — actions constructed so far, each paired with its transitively-closed ancestor
                list (the candidate parents for `PickClosedActionAncestors`; the closure invariant
                makes any chosen union itself closed);
    * `avail` — the remaining eid pool, drawn WITHOUT replacement via `SelectRemove` so action
                UIDs are distinct (no `RequestFromAction`/`Map.mk` desync).
    Each action picks its ancestors from *earlier*-built actions only, so the hierarchy is acyclic
    and transitively closed by construction. Principal/resource/context are well-formed against
    `ets` (mirrors the old `WfActionEntry`, now inlined so `built` can be threaded). -/
inductive WfActionsGo :
    List EntityType →                       -- ets (principal/resource/context types)
    List (EntityUID × List EntityUID) →     -- built: actions so far, each with closed ancestors
    List String →                           -- avail: remaining eid pool
    List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ∀ ets built avail, WfActionsGo ets built avail []
  | cons : ∀ ets built avail avail' eid ancestors principals resources context rest,
      SelectRemove avail eid avail' →                        -- fresh eid (uniform, distinct)
      PickClosedActionAncestors built ancestors →            -- transitively-closed parents
      WfPrincipalTypes ets principals →
      WfResourceTypes ets resources →
      WfAttrs Option.none ets context →
      WfActionsGo ets ((⟨actionEntityType, eid⟩, ancestors) :: built) avail' rest →
      WfActionsGo ets built avail
        ((⟨actionEntityType, eid⟩,
          ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors) (Map.mk context)) :: rest)

/-- Well-formed action schema: run the topological construction from empty accumulators, drawing
    distinct eids from `actionEidPool`. Action ancestors are transitively closed + acyclic by
    construction, so the generated hierarchy passes Lean's `validateWellFormed` transitivity check
    (used by the SymCC compiler via `CompiledPolicy.compile`). -/
inductive WfActionSchema : List EntityType → List (EntityUID × ActionSchemaEntry) → Prop where
  | mk : ∀ ets entries,
      WfActionsGo ets [] actionEidPool entries →
      WfActionSchema ets entries

/-! ## Well-formed request type

Pick principal from the action's principal list, resource from the action's
resource list. Since WfPrincipalTypes/WfResourceTypes already guarantee those
are defined entity types, we only need DefinedEntityType on the list itself.
-/

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

/-! ## Top-level: well-formed TypeEnv -/

inductive WfTypeEnv : TypeEnv → Prop where
  | mk : ∀ entityTypes entityEntries actionEntries reqty,
      WfEntitySchema entityTypes entityEntries →
      WfActionSchema entityTypes actionEntries →
      RequestFromAction entityTypes actionEntries reqty →
      WfTypeEnv (TypeEnv.mk (Map.mk entityEntries) (Map.mk actionEntries) reqty)

end CedarGen.Relational.Schema

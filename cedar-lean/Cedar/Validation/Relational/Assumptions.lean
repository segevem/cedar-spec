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

public import Cedar.Validation.Relational.Typing

@[expose] public section

/-! # What the relational typing spec assumes of a type environment

`HasType` agrees with `typeOf` on every type environment satisfying `EnvAssumptions`
(`hasType_iff_typeOf_ok`). It asks for distinct keys where Cedar's own
`TypeEnv.WellFormed` asks for sorted ones: `Map.find?` takes the first match, so distinct
keys are what make it agree with a relational `MapContains` witness, and maps built in any
order qualify. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

mutual
/-- A `CedarType` whose every record subtype has distinct (duplicate-free) keys. -/
inductive TyWf : CedarType → Prop where
  | bool : ∀ b, TyWf (.bool b)
  | int : TyWf .int
  | string : TyWf .string
  | entity : ∀ e, TyWf (.entity e)
  | ext : ∀ x, TyWf (.ext x)
  | set : ∀ t, TyWf t → TyWf (.set t)
  | record : ∀ (m : Map Attr QualifiedType), (m.toList.map Prod.fst).Nodup →
      (∀ q ∈ m.toList.map Prod.snd, TyWfQ q) → TyWf (.record m)
inductive TyWfQ : QualifiedType → Prop where
  | required : ∀ t, TyWf t → TyWfQ (.required t)
  | optional : ∀ t, TyWf t → TyWfQ (.optional t)
end

/-- A `CedarType` is *valid* in `env` when every entity type occurring in it is
    declared (`ValidEntityType`). This is the entity-declaredness fragment of Cedar's
    `CedarType.WellFormed` — deliberately dropping the record-`Map` sortedness that Cedar
    requires, since the relational `Schema.WfTypeEnv` builds maps in generation order, not
    sorted. `typeOf` on a `WfTypeEnv` produces `TypeValid` types (`typeOf_type_valid`). -/
inductive TypeValid (env : TypeEnv) : CedarType → Prop where
  | bool : ∀ b, TypeValid env (.bool b)
  | int : TypeValid env .int
  | string : TypeValid env .string
  | ext : ∀ x, TypeValid env (.ext x)
  | entity : ∀ ety, ValidEntityType ety env.ets env.acts → TypeValid env (.entity ety)
  | set : ∀ ty, TypeValid env ty → TypeValid env (.set ty)
  | record : ∀ rts, (∀ p ∈ rts, TypeValid env p.2.getType) → TypeValid env (.record (Map.mk rts))

/-- The properties of a type environment on which `HasType` and `typeOf` agree.

* entity and action types are declared once each;
* no action is a member of an action of a different entity type, so `in` between an
  action-typed operand and an operand of another type is statically false;
* attribute, tag and context types have distinct record keys (`TyWf`) and declared entity
  types (`TypeValid`), as does the request's principal, resource and action. -/
structure EnvAssumptions (env : TypeEnv) : Prop where
  ets_keys_nodup : (env.ets.toList.map Prod.fst).Nodup
  acts_keys_nodup : (env.acts.toList.map Prod.fst).Nodup
  action_ancestry_same_type :
    ∀ {ety₁ ety₂ : EntityType}, ety₁ ≠ ety₂ → env.acts.maybeDescendentOf ety₁ ety₂ = false
  attrs_tyWf : ∀ {ety rty}, EntitySchema.attrs? env.ets ety = some rty → TyWf (.record rty)
  tags_tyWf : ∀ {ety ty}, EntitySchema.tags? env.ets ety = some (some ty) → TyWf ty
  context_tyWf : TyWf (.record env.reqty.context)
  attrs_typeValid :
    ∀ {ety rty}, EntitySchema.attrs? env.ets ety = some rty → TypeValid env (.record rty)
  tags_typeValid :
    ∀ {ety ty}, EntitySchema.tags? env.ets ety = some (some ty) → TypeValid env ty
  reqty_valid :
    ValidEntityType env.reqty.principal env.ets env.acts ∧
    ValidEntityType env.reqty.resource env.ets env.acts ∧
    ValidEntityType env.reqty.action.ty env.ets env.acts ∧
    TypeValid env (.record env.reqty.context)

/-- Every ancestor of an action has the action's own entity type. Cedar's `TypeEnv.WellFormed`
    does not require this, since an action may belong to an action of another entity type
    (one in another namespace, say); on such schemas `HasType`'s rules for `in` on
    action-typed operands disagree with `typeOf`. -/
def ActionSchema.AncestorsSameType (acts : ActionSchema) : Prop :=
  ∀ uid entry, acts.find? uid = some entry → ∀ anc ∈ entry.ancestors, anc.ty = uid.ty

end Cedar.Validation.Relational

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
import Specimen

/-! # Relational specification of the Cedar typing judgement

This module defines the Cedar expression typechecker as an inductive relation,
parallel to the functional `typeOf` in `Cedar.Validation.Typechecker`.

All relations are expressed without function calls or record accessors in
hypotheses — every structural component is an explicit variable in the
conclusion. This makes them multi-directional: Specimen can derive generators
for any input/output mode (forward typechecking, backward expression generation,
environment synthesis, etc.).
-/

namespace CedarGen.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Result type for the typing relation -/

inductive TypeResult where
  | ok
  | error (e : TypeError)
deriving Repr, DecidableEq

/-! ## Auxiliary inequality relations for small types

Expressed structurally so Specimen can generate pairs directly. -/

inductive BoolTypeNeq : BoolType → BoolType → Prop where
  | tt_ff : BoolTypeNeq .tt .ff
  | tt_any : BoolTypeNeq .tt .anyBool
  | ff_tt : BoolTypeNeq .ff .tt
  | ff_any : BoolTypeNeq .ff .anyBool
  | any_tt : BoolTypeNeq .anyBool .tt
  | any_ff : BoolTypeNeq .anyBool .ff

inductive PrimNeq : Prim → Prim → Prop where
  | bool_int : ∀ b i, PrimNeq (.bool b) (.int i)
  | bool_string : ∀ b s, PrimNeq (.bool b) (.string s)
  | bool_entity : ∀ b uid, PrimNeq (.bool b) (.entityUID uid)
  | int_bool : ∀ i b, PrimNeq (.int i) (.bool b)
  | int_string : ∀ i s, PrimNeq (.int i) (.string s)
  | int_entity : ∀ i uid, PrimNeq (.int i) (.entityUID uid)
  | string_bool : ∀ s b, PrimNeq (.string s) (.bool b)
  | string_int : ∀ s i, PrimNeq (.string s) (.int i)
  | string_entity : ∀ s uid, PrimNeq (.string s) (.entityUID uid)
  | entity_bool : ∀ uid b, PrimNeq (.entityUID uid) (.bool b)
  | entity_int : ∀ uid i, PrimNeq (.entityUID uid) (.int i)
  | entity_string : ∀ uid s, PrimNeq (.entityUID uid) (.string s)
  | bool_bool : ∀ b₁ b₂, b₁ ≠ b₂ → PrimNeq (.bool b₁) (.bool b₂)
  | int_int : ∀ i₁ i₂, i₁ ≠ i₂ → PrimNeq (.int i₁) (.int i₂)
  | string_string : ∀ s₁ s₂, s₁ ≠ s₂ → PrimNeq (.string s₁) (.string s₂)
  | entity_entity : ∀ uid₁ uid₂, uid₁ ≠ uid₂ → PrimNeq (.entityUID uid₁) (.entityUID uid₂)

/-! ## Least upper bound as a relation

Mirrors `lub?` from Subtyping.lean but expressed inductively. -/

mutual

inductive Lub : CedarType → CedarType → CedarType → Prop where
  | boolSame :
    ∀ b,
    Lub (.bool b) (.bool b) (.bool b)
  | boolDiff :
    ∀ b₁ b₂,
    BoolTypeNeq b₁ b₂ →
    Lub (.bool b₁) (.bool b₂) (.bool .anyBool)
  | int :
    Lub .int .int .int
  | string :
    Lub .string .string .string
  | entity :
    ∀ ety,
    Lub (.entity ety) (.entity ety) (.entity ety)
  | ext :
    ∀ xty,
    Lub (.ext xty) (.ext xty) (.ext xty)
  | set :
    ∀ s₁ s₂ s,
    Lub s₁ s₂ s →
    Lub (.set s₁) (.set s₂) (.set s)
  | record :
    ∀ r₁ r₂ r,
    LubRecord r₁ r₂ r →
    Lub (.record (.mk r₁)) (.record (.mk r₂)) (.record (.mk r))

inductive LubQualified : QualifiedType → QualifiedType → QualifiedType → Prop where
  | optional :
    ∀ t₁ t₂ t,
    Lub t₁ t₂ t →
    LubQualified (.optional t₁) (.optional t₂) (.optional t)
  | required :
    ∀ t₁ t₂ t,
    Lub t₁ t₂ t →
    LubQualified (.required t₁) (.required t₂) (.required t)

inductive LubRecord : List (Attr × QualifiedType) → List (Attr × QualifiedType) → List (Attr × QualifiedType) → Prop where
  | nil :
    LubRecord [] [] []
  | cons :
    ∀ k v₁ v₂ v r₁ r₂ r,
    LubQualified v₁ v₂ v →
    LubRecord r₁ r₂ r →
    LubRecord ((k, v₁) :: r₁) ((k, v₂) :: r₂) ((k, v) :: r)

end

/-! ## Map membership as a relation

Replaces `find?` / `contains` function calls with structural relations
so Specimen can generate keys from maps (backward direction). -/

inductive MapContains {α β : Type} : α → β → Map α β → Prop where
  | here :
    ∀ k v rest,
    MapContains k v (.mk ((k, v) :: rest))
  | there :
    ∀ k v k' v' rest,
    MapContains k v (.mk rest) →
    MapContains k v (.mk ((k', v') :: rest))

inductive SetContains {α : Type} : α → Set α → Prop where
  | here :
    ∀ x rest,
    SetContains x (.mk (x :: rest))
  | there :
    ∀ x y rest,
    SetContains x (.mk rest) →
    SetContains x (.mk (y :: rest))


inductive SameEntityType : EntityType → EntityType → Prop where
 | mk : SameEntityType a a

inductive SameString : String → String → Prop where
 | mk : SameString a a

inductive MapContainsPairKey {v} : EntityType → String → v → Map EntityUID v → Prop where
  | here : MapContainsPairKey a b va (Map.mk ((⟨a,b⟩, va) :: m))
  | nextA : Not (SameEntityType a a') → MapContainsPairKey a b va (Map.mk m) → MapContainsPairKey a b va (Map.mk ((⟨a',b'⟩, v') :: m))
  | nextB : Not (SameString b b') → MapContainsPairKey a b va (Map.mk m) → MapContainsPairKey a b va (Map.mk ((⟨a',b'⟩, v') :: m))


/-! ## Entity UID validity as a relation -/

inductive ValidEntityUID : EntityType → String → EntitySchema → ActionSchema → Prop where
  | standard :
    ∀ ety eid entry ets acts,
    MapContains ety (EntitySchemaEntry.standard entry) ets →
    ValidEntityUID ety eid ets acts
  | enum :
    ∀ ety eid eids ets acts,
    MapContains ety (EntitySchemaEntry.enum eids) ets →
    SetContains eid eids →
    ValidEntityUID ety eid ets acts
  | action :
    ∀ ety eid ets acts entry,
    MapContainsPairKey ety eid entry acts →
    ValidEntityUID ety eid ets acts

/-! ## Literal typing -/

inductive HasTypeLit : Prim → EntitySchema → ActionSchema → TypedExpr → CedarType → Prop where
  | boolTrue :
    ∀ ets acts,
    HasTypeLit (.bool true) ets acts
      (.lit (.bool true) (.bool .tt))
      (.bool .tt)
  | boolFalse :
    ∀ ets acts,
    HasTypeLit (.bool false) ets acts
      (.lit (.bool false) (.bool .ff))
      (.bool .ff)
  | int :
    ∀ i ets acts,
    HasTypeLit (.int i) ets acts
      (.lit (.int i) .int)
      .int
  | string :
    ∀ s ets acts,
    HasTypeLit (.string s) ets acts
      (.lit (.string s) .string)
      .string
  | entity :
    ∀ ety eid ets acts,
    ValidEntityUID ety eid ets acts →
    HasTypeLit (.entityUID ⟨ety, eid⟩) ets acts
      (.lit (.entityUID ⟨ety, eid⟩) (.entity ety))
      (.entity ety)

/-! ## Variable typing -/

inductive HasTypeVar : Var → EntitySchema → ActionSchema → RequestType → TypedExpr → CedarType → Prop where
  | principal :
    ∀ ets acts princ action resource ctx,
    HasTypeVar .principal ets acts ⟨princ, action, resource, ctx⟩
      (.var .principal (.entity princ))
      (.entity princ)
  | action :
    ∀ ets acts princ actionTy actionEid resource ctx,
    HasTypeVar .action ets acts ⟨princ, ⟨actionTy, actionEid⟩, resource, ctx⟩
      (.var .action (.entity actionTy))
      (.entity actionTy)
  | resource :
    ∀ ets acts princ action resource ctx,
    HasTypeVar .resource ets acts ⟨princ, action, resource, ctx⟩
      (.var .resource (.entity resource))
      (.entity resource)
  | context :
    ∀ ets acts princ action resource ctx,
    HasTypeVar .context ets acts ⟨princ, action, resource, ctx⟩
      (.var .context (.record ctx))
      (.record ctx)

/-! ## Unary operation typing

Only relates (op, inputType, outputType). The TypedExpr is assembled by the caller. -/

inductive HasTypeUnaryApp : UnaryOp → CedarType → CedarType → Prop where
  | notTt :      HasTypeUnaryApp .not      (.bool .tt)      (.bool .ff)
  | notFf :      HasTypeUnaryApp .not      (.bool .ff)      (.bool .tt)
  | notAny :     HasTypeUnaryApp .not      (.bool .anyBool) (.bool .anyBool)
  | neg :        HasTypeUnaryApp .neg      .int             .int
  | isEmpty :  ∀ elemTy,
               HasTypeUnaryApp .isEmpty  (.set elemTy)    (.bool .anyBool)
  | like :     ∀ pat,
               HasTypeUnaryApp (.like pat) .string        (.bool .anyBool)
  | isTrue :   ∀ ety,
               HasTypeUnaryApp (.is ety) (.entity ety)   (.bool .tt)
  | isFalse :  ∀ ety₁ ety₂,
               ety₁ ≠ ety₂ →
               HasTypeUnaryApp (.is ety₁) (.entity ety₂) (.bool .ff)

/-! ## Arithmetic and comparison binary ops

Only relates (op, inputType1, inputType2, outputType). The TypedExpr values
are assembled by the caller — this relation just determines what type
combinations are valid. -/

inductive HasTypeArith : BinaryOp → CedarType → CedarType → CedarType → Prop where
  | lessInt :       HasTypeArith .less   .int            .int            (.bool .anyBool)
  | lessDatetime :  HasTypeArith .less   (.ext .datetime) (.ext .datetime) (.bool .anyBool)
  | lessDuration :  HasTypeArith .less   (.ext .duration) (.ext .duration) (.bool .anyBool)
  | lessEqInt :     HasTypeArith .lessEq .int            .int            (.bool .anyBool)
  | lessEqDatetime: HasTypeArith .lessEq (.ext .datetime) (.ext .datetime) (.bool .anyBool)
  | lessEqDuration: HasTypeArith .lessEq (.ext .duration) (.ext .duration) (.bool .anyBool)
  | add :           HasTypeArith .add    .int            .int            .int
  | sub :           HasTypeArith .sub    .int            .int            .int
  | mul :           HasTypeArith .mul    .int            .int            .int

/-! ## Equality typing

Split into two pure relations (no Expr/Capabilities/TypeEnv) so Specimen
can generate each case independently. The literal case operates on Prim values;
the non-literal case operates on CedarTypes already produced by sub-expression typing. -/

inductive HasTypeEqLit : Prim → Prim → CedarType → Prop where
  | same : ∀ p, HasTypeEqLit p p (.bool .tt)
  | diff : ∀ p₁ p₂, PrimNeq p₁ p₂ → HasTypeEqLit p₁ p₂ (.bool .ff)

inductive HasTypeEqNonLit : CedarType → CedarType → CedarType → Prop where
  | lubOk :
    ∀ t₁ t₂ lubTy,
    Lub t₁ t₂ lubTy →
    HasTypeEqNonLit t₁ t₂ (.bool .anyBool)
  | entityEntityDiff :
    ∀ ety₁ ety₂,
    ety₁ ≠ ety₂ →
    HasTypeEqNonLit (.entity ety₁) (.entity ety₂) (.bool .ff)

/-! ## Set operations typing -/

/-! ## Set operations typing

Only relates (op, inputType1, inputType2, outputType). -/

inductive HasTypeSetOp : BinaryOp → CedarType → CedarType → CedarType → Prop where
  | contains :
    ∀ t₂ elemTy lubTy,
    Lub t₂ elemTy lubTy →
    HasTypeSetOp .contains (.set elemTy) t₂ (.bool .anyBool)
  | containsAll :
    ∀ elemTy₁ elemTy₂ lubTy,
    Lub elemTy₁ elemTy₂ lubTy →
    HasTypeSetOp .containsAll (.set elemTy₁) (.set elemTy₂) (.bool .anyBool)
  | containsAny :
    ∀ elemTy₁ elemTy₂ lubTy,
    Lub elemTy₁ elemTy₂ lubTy →
    HasTypeSetOp .containsAny (.set elemTy₁) (.set elemTy₂) (.bool .anyBool)

/-! ## Set literal element typing (as a fold-like relation)

Instead of calling `foldlM lub?`, we express the constraint that
all element types are compatible via iterated Lub. -/

inductive AllLub : CedarType → List CedarType → CedarType → Prop where
  | nil :
    ∀ ty,
    AllLub ty [] ty
  | cons :
    ∀ acc hd tl lubTy result,
    Lub acc hd lubTy →
    AllLub lubTy tl result →
    AllLub acc (hd :: tl) result

/-! ## Capability relations

Structural relations for capability list operations.
These allow Specimen to generate capability combinations bidirectionally. -/

/-- Structural membership in a capabilities list -/
inductive CapMem : Expr → Key → Capabilities → Prop where
  | here :
    ∀ x k rest,
    CapMem x k ((x, k) :: rest)
  | there :
    ∀ x k x' k' rest,
    CapMem x k rest →
    CapMem x k ((x', k') :: rest)

/-- Structural merge of two capability lists.
`CapMerge c₁ c₂ c` means every element of `c` came from `c₁`, `c₂`, or both,
and every element of `c₁` and `c₂` appears in `c`.

Running forwards: given c₁ and c₂, produce their union (interleaving/deduplicating).
Running backwards ("un-unioning"): given c, non-deterministically assign
each element to the left source, right source, or both. -/
inductive CapMerge : Capabilities → Capabilities → Capabilities → Prop where
  | nil :
    CapMerge [] [] []
  | left :
    ∀ x k c₁ c₂ c,
    CapMerge c₁ c₂ c →
    CapMerge ((x, k) :: c₁) c₂ ((x, k) :: c)
  | right :
    ∀ x k c₁ c₂ c,
    CapMerge c₁ c₂ c →
    CapMerge c₁ ((x, k) :: c₂) ((x, k) :: c)
  | both :
    ∀ x k c₁ c₂ c,
    CapMerge c₁ c₂ c →
    CapMerge ((x, k) :: c₁) ((x, k) :: c₂) ((x, k) :: c)

/-- Every element in the first list also appears in the second.
Used to express "subset" constraints on capability intersections. -/
inductive CapSubset : Capabilities → Capabilities → Prop where
  | nil :
    CapSubset [] c
  | cons :
    ∀ x k rest c,
    CapMem x k c →
    CapSubset rest c →
    CapSubset ((x, k) :: rest) c

/-! ## If-then-else typing as a relation

Mirrors `typeOfIf` from Typechecker.lean. Split by the BoolType of the condition.
Capability combination is expressed structurally via `CapMerge`/`CapSubset`. -/
inductive HasTypeIf : BoolType → Capabilities → CedarType → CedarType → Capabilities → Capabilities → CedarType → Capabilities → Prop where
  | tt :
    ∀ c₁ t₂ t₃ c₂ c₃ cout,
    CapMerge c₁ c₂ cout →
    HasTypeIf .tt c₁ t₂ t₃ c₂ c₃ t₂ cout
  | ff :
    ∀ c₁ t₂ t₃ c₂ c₃,
    HasTypeIf .ff c₁ t₂ t₃ c₂ c₃ t₃ c₃
  | anyBool :
    ∀ c₁ t₂ t₃ c₂ c₃ lubTy c₁₂ cout,
    Lub t₂ t₃ lubTy →
    CapMerge c₁ c₂ c₁₂ →
    CapSubset cout c₁₂ →
    CapSubset cout c₃ →
    HasTypeIf .anyBool c₁ t₂ t₃ c₂ c₃ lubTy cout

/-! ## And typing as a relation

Mirrors `typeOfAnd`. -/

inductive HasTypeAnd : BoolType → BoolType → Capabilities → Capabilities → CedarType → Capabilities → Prop where
  | ttThenFf :
    ∀ c₁ c₂,
    HasTypeAnd .tt .ff c₁ c₂ (.bool .ff) []
  | ttThenTt :
    ∀ c₁ c₂ cout,
    CapMerge c₁ c₂ cout →
    HasTypeAnd .tt .tt c₁ c₂ (.bool .tt) cout
  | ttThenAny :
    ∀ c₁ c₂ cout,
    CapMerge c₁ c₂ cout →
    HasTypeAnd .tt .anyBool c₁ c₂ (.bool .anyBool) cout
  | anyThenFf :
    ∀ b₁ c₁ c₂,
    HasTypeAnd b₁ .ff c₁ c₂ (.bool .ff) []
  | anyThenTt :
    ∀ b₁ c₁ c₂ cout,
    CapMerge c₁ c₂ cout →
    HasTypeAnd b₁ .tt c₁ c₂ (.bool b₁) cout
  | anyThenAny :
    ∀ b₁ c₁ c₂ cout,
    CapMerge c₁ c₂ cout →
    HasTypeAnd b₁ .anyBool c₁ c₂ (.bool .anyBool) cout

/-! ## Or typing as a relation

Mirrors `typeOfOr`. -/

inductive HasTypeOr : BoolType → Capabilities → BoolType → Capabilities → CedarType → Capabilities → Prop where
  | ffThenBool :
    ∀ c₁ b₂ c₂,
    HasTypeOr .ff c₁ b₂ c₂ (.bool b₂) c₂
  | anyThenTt :
    ∀ b₁ c₁ c₂,
    HasTypeOr b₁ c₁ .tt c₂ (.bool .tt) []
  | anyThenFf :
    ∀ b₁ c₁ c₂,
    HasTypeOr b₁ c₁ .ff c₂ (.bool .anyBool) c₁
  | anyThenAny :
    ∀ b₁ c₁ c₂ cout,
    CapSubset cout c₁ →
    CapSubset cout c₂ →
    HasTypeOr b₁ c₁ .anyBool c₂ (.bool .anyBool) cout

/-! ## Membership (in) operator typing as a relation

Mirrors `typeOfInₑ` and `typeOfInₛ`. We abstract the ancestry checks
as opaque BoolType results since the detailed action/entity ancestry
logic is schema-dependent. -/

/-! ### Entity ancestry as a relation

`DescendentOf ets acts ety₁ ety₂` holds when `ety₁` is a descendent of
(or equal to) `ety₂` according to the entity schema or action schema. -/

inductive DescendentOf : EntitySchema → ActionSchema → EntityType → EntityType → Prop where
  | refl :
    ∀ ets acts ety,
    DescendentOf ets acts ety ety
  | ancestor :
    ∀ ets acts ety₁ ety₂ ancs attrs tags,
    MapContains ety₁ (.standard ⟨ancs, attrs, tags⟩) ets →
    SetContains ety₂ ancs →
    DescendentOf ets acts ety₁ ety₂

inductive HasTypeMem : CedarType → CedarType → Expr → Expr → TypeEnv → CedarType → Prop where
  | entityEntityDescendent :
    ∀ ety₁ ety₂ x₁ x₂ ets acts reqty,
    DescendentOf ets acts ety₁ ety₂ →
    HasTypeMem (.entity ety₁) (.entity ety₂) x₁ x₂ ⟨ets, acts, reqty⟩ (.bool .anyBool)
  | entityEntitySame :
    ∀ ety x₁ x₂ ets acts reqty,
    HasTypeMem (.entity ety) (.entity ety) x₁ x₂ ⟨ets, acts, reqty⟩ (.bool .anyBool)
  | entitySetDescendent :
    ∀ ety₁ ety₂ x₁ x₂ ets acts reqty,
    DescendentOf ets acts ety₁ ety₂ →
    HasTypeMem (.entity ety₁) (.set (.entity ety₂)) x₁ x₂ ⟨ets, acts, reqty⟩ (.bool .anyBool)
  | entitySetSame :
    ∀ ety x₁ x₂ ets acts reqty,
    HasTypeMem (.entity ety) (.set (.entity ety)) x₁ x₂ ⟨ets, acts, reqty⟩ (.bool .anyBool)

/-! ## Has-attribute typing as a relation

Mirrors `typeOfHasAttr`. -/

inductive HasAttrInRecord : RecordType → Expr → Attr → Capabilities → Bool → CedarType → Capabilities → Prop where
  | found_in_caps :
    ∀ rty x a c knownToExist qty,
    MapContains a qty rty →
    CapMem x (.attr a) c →
    HasAttrInRecord rty x a c knownToExist (.bool .tt) []
  | found_required_known :
    ∀ rty x a c ty,
    MapContains a (.required ty) rty →
    HasAttrInRecord rty x a c true (.bool .tt) []
  | found_not_known :
    ∀ rty x a c qty,
    MapContains a qty rty →
    HasAttrInRecord rty x a c false (.bool .anyBool) [(x, .attr a)]
  | found_optional_known :
    ∀ rty x a c ty,
    MapContains a (.optional ty) rty →
    HasAttrInRecord rty x a c true (.bool .anyBool) [(x, .attr a)]

inductive HasTypeHasAttr : CedarType → Expr → Attr → Capabilities → TypeEnv → CedarType → Capabilities → Prop where
  | record :
    ∀ rty x a c env ty caps,
    HasAttrInRecord rty x a c true ty caps →
    HasTypeHasAttr (.record rty) x a c env ty caps
  | entity :
    ∀ ety x a c ets acts reqty ty caps ancs rty tags,
    MapContains ety (.standard ⟨ancs, rty, tags⟩) ets →
    HasAttrInRecord rty x a c false ty caps →
    HasTypeHasAttr (.entity ety) x a c ⟨ets, acts, reqty⟩ ty caps

/-! ## Get-attribute typing as a relation

Mirrors `typeOfGetAttr`. -/

inductive GetAttrInRecord : CedarType → RecordType → Expr → Attr → Capabilities → CedarType → Prop where
  | required :
    ∀ ty rty x a c aty,
    MapContains a (.required aty) rty →
    GetAttrInRecord ty rty x a c aty
  | optional :
    ∀ ty rty x a c aty,
    MapContains a (.optional aty) rty →
    CapMem x (.attr a) c →
    GetAttrInRecord ty rty x a c aty

inductive HasTypeGetAttr : CedarType → Expr → Attr → Capabilities → TypeEnv → CedarType → Prop where
  | record :
    ∀ rty x a c env ty,
    GetAttrInRecord (.record rty) rty x a c ty →
    HasTypeGetAttr (.record rty) x a c env ty
  | entity :
    ∀ ety x a c ets acts reqty ty ancs rty tags,
    MapContains ety (.standard ⟨ancs, rty, tags⟩) ets →
    GetAttrInRecord (.entity ety) rty x a c ty →
    HasTypeGetAttr (.entity ety) x a c ⟨ets, acts, reqty⟩ ty

/-! ## Extension function call typing as a relation

Mirrors `typeOfCall`. -/

/-! ### Valid extension constructor string (structural witness)

Instead of calling the parse function and checking `.isSome`, we
witness validity by providing the parsed value. -/

inductive ValidDecimal : String → Prop where
  | mk : ∀ s d, Cedar.Spec.Ext.Decimal.decimal s = some d → ValidDecimal s

inductive ValidIP : String → Prop where
  | mk : ∀ s ip, Cedar.Spec.Ext.IPAddr.ip s = some ip → ValidIP s

inductive ValidDatetime : String → Prop where
  | mk : ∀ s dt, Cedar.Spec.Ext.Datetime.parse s = some dt → ValidDatetime s

inductive ValidDuration : String → Prop where
  | mk : ∀ s dur, Cedar.Spec.Ext.Datetime.Duration.parse s = some dur → ValidDuration s

inductive HasTypeCall : ExtFun → List CedarType → List Expr → CedarType → Prop where
  | decimal :
    ∀ s,
    ValidDecimal s →
    HasTypeCall .decimal [.string] [.lit (.string s)] (.ext .decimal)
  | ip :
    ∀ s,
    ValidIP s →
    HasTypeCall .ip [.string] [.lit (.string s)] (.ext .ipAddr)
  | datetime :
    ∀ s,
    ValidDatetime s →
    HasTypeCall .datetime [.string] [.lit (.string s)] (.ext .datetime)
  | duration :
    ∀ s,
    ValidDuration s →
    HasTypeCall .duration [.string] [.lit (.string s)] (.ext .duration)
  | lessThan :
    ∀ xs,
    HasTypeCall .lessThan [.ext .decimal, .ext .decimal] xs (.bool .anyBool)
  | lessThanOrEqual :
    ∀ xs,
    HasTypeCall .lessThanOrEqual [.ext .decimal, .ext .decimal] xs (.bool .anyBool)
  | greaterThan :
    ∀ xs,
    HasTypeCall .greaterThan [.ext .decimal, .ext .decimal] xs (.bool .anyBool)
  | greaterThanOrEqual :
    ∀ xs,
    HasTypeCall .greaterThanOrEqual [.ext .decimal, .ext .decimal] xs (.bool .anyBool)
  | isIpv4 :
    ∀ xs,
    HasTypeCall .isIpv4 [.ext .ipAddr] xs (.bool .anyBool)
  | isIpv6 :
    ∀ xs,
    HasTypeCall .isIpv6 [.ext .ipAddr] xs (.bool .anyBool)
  | isLoopback :
    ∀ xs,
    HasTypeCall .isLoopback [.ext .ipAddr] xs (.bool .anyBool)
  | isMulticast :
    ∀ xs,
    HasTypeCall .isMulticast [.ext .ipAddr] xs (.bool .anyBool)
  | isInRange :
    ∀ xs,
    HasTypeCall .isInRange [.ext .ipAddr, .ext .ipAddr] xs (.bool .anyBool)
  | offset :
    ∀ xs,
    HasTypeCall .offset [.ext .datetime, .ext .duration] xs (.ext .datetime)
  | durationSince :
    ∀ xs,
    HasTypeCall .durationSince [.ext .datetime, .ext .datetime] xs (.ext .duration)
  | toDate :
    ∀ xs,
    HasTypeCall .toDate [.ext .datetime] xs (.ext .datetime)
  | toTime :
    ∀ xs,
    HasTypeCall .toTime [.ext .datetime] xs (.ext .duration)
  | toMilliseconds :
    ∀ xs,
    HasTypeCall .toMilliseconds [.ext .duration] xs .int
  | toSeconds :
    ∀ xs,
    HasTypeCall .toSeconds [.ext .duration] xs .int
  | toMinutes :
    ∀ xs,
    HasTypeCall .toMinutes [.ext .duration] xs .int
  | toHours :
    ∀ xs,
    HasTypeCall .toHours [.ext .duration] xs .int
  | toDays :
    ∀ xs,
    HasTypeCall .toDays [.ext .duration] xs .int

/-! ## Simple predicates with DecOpt (used as negative checks) -/

inductive BothLit : Expr → Expr → Prop where
  | mk : ∀ p₁ p₂, BothLit (.lit p₁) (.lit p₂)

instance : DecOpt (BothLit x₁ x₂) where
  decOpt _ := .ok (match x₁, x₂ with | .lit _, .lit _ => true | _, _ => false)

inductive BothEntity : CedarType → CedarType → Prop where
  | mk : ∀ ety₁ ety₂, BothEntity (.entity ety₁) (.entity ety₂)

instance : DecOpt (BothEntity t₁ t₂) where
  decOpt _ := .ok (match t₁, t₂ with | .entity _, .entity _ => true | _, _ => false)

inductive UnaryAppCompat : UnaryOp → CedarType → Prop where
  | not : ∀ b, UnaryAppCompat .not (.bool b)
  | neg : UnaryAppCompat .neg .int
  | isEmpty : ∀ ty, UnaryAppCompat .isEmpty (.set ty)
  | like : ∀ pat, UnaryAppCompat (.like pat) .string
  | is : ∀ ety₁ ety₂, UnaryAppCompat (.is ety₁) (.entity ety₂)

instance : DecOpt (UnaryAppCompat op t) where
  decOpt _ := .ok (match op, t with
    | .not, .bool _ => true
    | .neg, .int => true
    | .isEmpty, .set _ => true
    | .like _, .string => true
    | .is _, .entity _ => true
    | _, _ => false)

inductive LubExists : CedarType → CedarType → Prop where
  | boolBool : ∀ b₁ b₂, LubExists (.bool b₁) (.bool b₂)
  | int : LubExists .int .int
  | string : LubExists .string .string
  | entity : ∀ ety, LubExists (.entity ety) (.entity ety)
  | ext : ∀ xty, LubExists (.ext xty) (.ext xty)
  | set : ∀ s₁ s₂, LubExists (.set s₁) (.set s₂)
  | record : ∀ r₁ r₂, LubExists (.record r₁) (.record r₂)

instance : DecOpt (LubExists t₁ t₂) where
  decOpt _ := .ok (match t₁, t₂ with
    | .bool _, .bool _ => true
    | .int, .int => true
    | .string, .string => true
    | .entity e₁, .entity e₂ => e₁ == e₂
    | .ext x₁, .ext x₂ => x₁ == x₂
    | .set _, .set _ => true
    | .record _, .record _ => true
    | _, _ => false)

/-! ## Main typing relation -/

mutual

inductive HasType : Expr → Capabilities → TypeEnv → Option TypedExpr → Option CedarType → Option Capabilities → TypeResult → Prop where
  | lit :
    ∀ p c ets acts reqty tx ty,
    HasTypeLit p ets acts tx ty →
    HasType (.lit p) c ⟨ets, acts, reqty⟩ (some tx) (some ty) (some []) .ok
  | var :
    ∀ v c ets acts reqty tx ty,
    HasTypeVar v ets acts reqty tx ty →
    HasType (.var v) c ⟨ets, acts, reqty⟩ (some tx) (some ty) (some []) .ok
  | unaryApp :
    ∀ op x₁ c ets acts reqty tx₁ t₁ ty,
    HasTypeUnaryApp op t₁ ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
    HasType (.unaryApp op x₁) c ⟨ets, acts, reqty⟩
      (some (.unaryApp op tx₁ ty)) (some ty) (some []) .ok
  | binaryAppEqLit :
    ∀ p₁ p₂ c ets acts reqty tx₁ t₁ tx₂ t₂ ty,
    HasTypeLit p₁ ets acts tx₁ t₁ →
    HasTypeLit p₂ ets acts tx₂ t₂ →
    HasTypeEqLit p₁ p₂ ty →
    HasType (.binaryApp .eq (.lit p₁) (.lit p₂)) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .eq tx₁ tx₂ ty)) (some ty) (some []) .ok
  | binaryAppEqNonLit :

    ∀ x₁ x₂ c ets acts reqty tx₁ t₁ tx₂ t₂ ty,
        HasTypeEqNonLit t₁ t₂ ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some []) .ok →
    ¬ BothLit x₁ x₂ →

    HasType (.binaryApp .eq x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .eq tx₁ tx₂ ty)) (some ty) (some []) .ok
  | binaryAppArith :
    ∀ op x₁ x₂ c ets acts reqty tx₁ t₁ tx₂ t₂ ty,
    HasTypeArith op t₁ t₂ ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some []) .ok →
    HasType (.binaryApp op x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp op tx₁ tx₂ ty)) (some ty) (some []) .ok
  | binaryAppSetOp :
    ∀ op x₁ x₂ c ets acts reqty tx₁ t₁ tx₂ t₂ ty,
    HasTypeSetOp op t₁ t₂ ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some []) .ok →
    HasType (.binaryApp op x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp op tx₁ tx₂ ty)) (some ty) (some []) .ok
  | set :
    ∀ x xs c ets acts reqty tx ty tys tyList lubTy,
    HasType x c ⟨ets, acts, reqty⟩ (some tx) (some ty) (some []) .ok →
    HasTypeList xs c ⟨ets, acts, reqty⟩ tys tyList →
    AllLub ty tyList lubTy →
    HasType (.set (x :: xs)) c ⟨ets, acts, reqty⟩
      (some (.set (tx :: tys) (.set lubTy))) (some (.set lubTy)) (some []) .ok
  | record :
    ∀ axs c ets acts reqty atys atyList,
    HasTypeRecord axs c ⟨ets, acts, reqty⟩ atys atyList →
    HasType (.record axs) c ⟨ets, acts, reqty⟩
      (some (.record atys (.record (.mk atyList))))
      (some (.record (.mk atyList)))
      (some []) .ok
  | ite :
    ∀ x₁ x₂ x₃ c ets acts reqty tx₁ b₁ c₁ c_c₁ tx₂ t₂ c₂ tx₃ t₃ c₃ ty cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool b₁)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some c₂) .ok →
    HasType x₃ c ⟨ets, acts, reqty⟩ (some tx₃) (some t₃) (some c₃) .ok →
    HasTypeIf b₁ c₁ t₂ t₃ c₂ c₃ ty cout →
    HasType (.ite x₁ x₂ x₃) c ⟨ets, acts, reqty⟩
      (some (.ite tx₁ tx₂ tx₃ ty)) (some ty) (some cout) .ok
  | and :
    ∀ x₁ x₂ c ets acts reqty tx₁ b₁ c₁ c_c₁ tx₂ b₂ c₂ ty cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool b₁)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool b₂)) (some c₂) .ok →
    HasTypeAnd b₁ b₂ c₁ c₂ ty cout →
    HasType (.and x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.and tx₁ tx₂ ty)) (some ty) (some cout) .ok
  | andShort :
    ∀ x₁ x₂ c ets acts reqty tx₁ c₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .ff)) (some c₁) .ok →
    HasType (.and x₁ x₂) c ⟨ets, acts, reqty⟩
      (some tx₁) (some (.bool .ff)) (some []) .ok
  | or :
    ∀ x₁ x₂ c ets acts reqty tx₁ b₁ c₁ tx₂ b₂ c₂ ty cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool b₁)) (some c₁) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool b₂)) (some c₂) .ok →
    HasTypeOr b₁ c₁ b₂ c₂ ty cout →
    HasType (.or x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.or tx₁ tx₂ ty)) (some ty) (some cout) .ok
  | orShort :
    ∀ x₁ x₂ c ets acts reqty tx₁ c₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .tt)) (some c₁) .ok →
    HasType (.or x₁ x₂) c ⟨ets, acts, reqty⟩
      (some tx₁) (some (.bool .tt)) (some []) .ok
  | binaryAppMem :
    ∀ x₁ x₂ c ets acts reqty tx₁ t₁ tx₂ t₂ ty,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some []) .ok →
    HasTypeMem t₁ t₂ x₁ x₂ ⟨ets, acts, reqty⟩ ty →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .mem tx₁ tx₂ ty)) (some ty) (some []) .ok
  | hasAttr :
    ∀ x₁ a c ets acts reqty tx₁ t₁ ty caps,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
    HasTypeHasAttr t₁ x₁ a c ⟨ets, acts, reqty⟩ ty caps →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩
      (some (.hasAttr tx₁ a ty)) (some ty) (some caps) .ok
  | getAttr :
    ∀ x₁ a c ets acts reqty tx₁ t₁ ty,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
    HasTypeGetAttr t₁ x₁ a c ⟨ets, acts, reqty⟩ ty →
    HasType (.getAttr x₁ a) c ⟨ets, acts, reqty⟩
      (some (.getAttr tx₁ a ty)) (some ty) (some []) .ok
  | call :
    ∀ xfn xs c ets acts reqty txs tys ty,
    HasTypeList xs c ⟨ets, acts, reqty⟩ txs tys →
    HasTypeCall xfn tys xs ty →
    HasType (.call xfn xs) c ⟨ets, acts, reqty⟩
      (some (.call xfn txs ty)) (some ty) (some []) .ok
  -- | emptySetErr :
  --   ∀ c ets acts reqty,
  --   HasType (.set []) c ⟨ets, acts, reqty⟩ none none none (.error .emptySetErr)
  -- | unaryAppUnexpectedType :
  --   ∀ op x₁ c ets acts reqty tx₁ t₁,
  --   HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
  --   ¬ UnaryAppCompat op t₁ →
  --   HasType (.unaryApp op x₁) c ⟨ets, acts, reqty⟩
  --     none none none (.error (.unexpectedType t₁))
  -- | eqLubErr :
  --   ∀ x₁ x₂ c ets acts reqty tx₁ t₁ tx₂ t₂,
  --   HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
  --   HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some []) .ok →
  --   ¬ BothLit x₁ x₂ →
  --   ¬ LubExists t₁ t₂ →
  --   ¬ BothEntity t₁ t₂ →
  --   HasType (.binaryApp .eq x₁ x₂) c ⟨ets, acts, reqty⟩
  --     none none none (.error (.lubErr t₁ t₂))

/-- Typing a list of expressions (success path only). -/
inductive HasTypeList : List Expr → Capabilities → TypeEnv → List TypedExpr → List CedarType → Prop where
  | nil :
    ∀ c env,
    HasTypeList [] c env [] []
  | cons :
    ∀ x xs c env tx ty txs tys,
    HasType x c env (some tx) (some ty) (some []) .ok →
    HasTypeList xs c env txs tys →
    HasTypeList (x :: xs) c env (tx :: txs) (ty :: tys)

/-- Typing a record (success path only). -/
inductive HasTypeRecord : List (Attr × Expr) → Capabilities → TypeEnv → List (Attr × TypedExpr) → List (Attr × QualifiedType) → Prop where
  | nil :
    ∀ c env,
    HasTypeRecord [] c env [] []
  | cons :
    ∀ a x axs c env tx ty atys atyList,
    HasType x c env (some tx) (some ty) (some []) .ok →
    HasTypeRecord axs c env atys atyList →
    HasTypeRecord ((a, x) :: axs) c env ((a, tx) :: atys) ((a, .required ty) :: atyList)

end

end CedarGen.Relational

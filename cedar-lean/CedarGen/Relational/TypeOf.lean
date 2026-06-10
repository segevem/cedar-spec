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


/-! ## Entity UID validity as a relation -/

inductive ValidEntityUID : EntityUID → EntitySchema → ActionSchema → Prop where
  | standard :
    ∀ ety eid entry ets acts,
    MapContains ety (EntitySchemaEntry.standard entry) ets →
    ValidEntityUID ⟨ety, eid⟩ ets acts
  | enum :
    ∀ ety eid eids ets acts,
    MapContains ety (EntitySchemaEntry.enum eids) ets →
    SetContains eid eids →
    ValidEntityUID ⟨ety, eid⟩ ets acts
  | action :
    ∀ uid ets acts entry,
    MapContains uid entry acts →
    ValidEntityUID uid ets acts

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
    ValidEntityUID ⟨ety, eid⟩ ets acts →
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
    ∀ ets acts princ action resource ctx,
    HasTypeVar .action ets acts ⟨princ, action, resource, ctx⟩
      (.var .action (.entity action.ty))
      (.entity action.ty)
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

/-! ## Equality typing — moved into the mutual block below -/

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

/-! ## Both-literal predicate (used as a negative check) -/

inductive BothLit : Expr → Expr → Prop where
  | mk : ∀ p₁ p₂, BothLit (.lit p₁) (.lit p₂)

instance : DecOpt (BothLit x₁ x₂) where
  decOpt _ := .ok (match x₁, x₂ with | .lit _, .lit _ => true | _, _ => false)

/-! ## Main typing relation -/

mutual

/-- Equality typing: mutual with HasType so sub-expressions are constrained.
    `entityEntityDiff` also requires `NotBothLit` since the functional spec
    only reaches this path after failing the literal check AND failing lub.
    Outputs both TypedExprs so the caller can assemble the result. -/
inductive HasTypeEq : Expr → Expr → Capabilities → TypeEnv → TypedExpr → CedarType → TypedExpr → CedarType → CedarType → Prop where
  | litSame :
    ∀ p c env tx₁ t₁ c₁ tx₂ t₂ c₂,
    HasType (.lit p) c env tx₁ t₁ c₁ →
    HasType (.lit p) c env tx₂ t₂ c₂ →
    HasTypeEq (.lit p) (.lit p) c env tx₁ t₁ tx₂ t₂ (.bool .tt)
  | litDiff :
    ∀ p₁ p₂ c env tx₁ t₁ c₁ tx₂ t₂ c₂,
    PrimNeq p₁ p₂ →
    HasType (.lit p₁) c env tx₁ t₁ c₁ →
    HasType (.lit p₂) c env tx₂ t₂ c₂ →
    HasTypeEq (.lit p₁) (.lit p₂) c env tx₁ t₁ tx₂ t₂ (.bool .ff)
  | lubOk :
    ∀ x₁ x₂ c env tx₁ t₁ c₁ tx₂ t₂ c₂ lubTy,
    HasType x₁ c env tx₁ t₁ c₁ →
    HasType x₂ c env tx₂ t₂ c₂ →
    ¬ BothLit x₁ x₂ →
    Lub t₁ t₂ lubTy →
    HasTypeEq x₁ x₂ c env tx₁ t₁ tx₂ t₂ (.bool .anyBool)
  | entityEntityDiff :
    ∀ x₁ x₂ c env tx₁ ety₁ c₁ tx₂ ety₂ c₂,
    HasType x₁ c env tx₁ (.entity ety₁) c₁ →
    HasType x₂ c env tx₂ (.entity ety₂) c₂ →
    ¬ BothLit x₁ x₂ →
    ety₁ ≠ ety₂ →
    HasTypeEq x₁ x₂ c env tx₁ (.entity ety₁) tx₂ (.entity ety₂) (.bool .ff)

inductive HasType : Expr → Capabilities → TypeEnv → TypedExpr → CedarType → Capabilities → Prop where
  | lit :
    ∀ p c ets acts reqty tx ty,
    HasTypeLit p ets acts tx ty →
    HasType (.lit p) c ⟨ets, acts, reqty⟩ tx ty ∅
  | var :
    ∀ v c ets acts reqty tx ty,
    HasTypeVar v ets acts reqty tx ty →
    HasType (.var v) c ⟨ets, acts, reqty⟩ tx ty ∅
  | unaryApp :
    ∀ op x₁ c ets acts reqty tx₁ t₁ c₁ ty,
    HasTypeUnaryApp op t₁ ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ tx₁ t₁ c₁ →
    HasType (.unaryApp op x₁) c ⟨ets, acts, reqty⟩
      (.unaryApp op tx₁ ty) ty ∅
  | binaryAppEq :
    ∀ x₁ x₂ c ets acts reqty tx₁ t₁ tx₂ t₂ ty,
    HasTypeEq x₁ x₂ c ⟨ets, acts, reqty⟩ tx₁ t₁ tx₂ t₂ ty →
    HasType (.binaryApp .eq x₁ x₂) c ⟨ets, acts, reqty⟩
      (.binaryApp .eq tx₁ tx₂ ty) ty ∅
  | binaryAppArith :
    ∀ op x₁ x₂ c ets acts reqty (tx₁ : TypedExpr) t₁ c₁ (tx₂ : TypedExpr) t₂ c₂ ty,
    HasTypeArith op t₁ t₂ ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ tx₁ t₁ c₁ →
    HasType x₂ c ⟨ets, acts, reqty⟩ tx₂ t₂ c₂ →
    HasType (.binaryApp op x₁ x₂) c ⟨ets, acts, reqty⟩
      (.binaryApp op tx₁ tx₂ ty) ty ∅
  | binaryAppSetOp :
    ∀ op x₁ x₂ c ets acts reqty (tx₁ : TypedExpr) t₁ c₁ (tx₂ : TypedExpr) t₂ c₂ ty,
    HasTypeSetOp op t₁ t₂ ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ tx₁ t₁ c₁ →
    HasType x₂ c ⟨ets, acts, reqty⟩ tx₂ t₂ c₂ →
    HasType (.binaryApp op x₁ x₂) c ⟨ets, acts, reqty⟩
      (.binaryApp op tx₁ tx₂ ty) ty ∅
  | set :
    ∀ xs c ets acts reqty tys tyList hdTy lubTy,
    HasTypeList xs c ⟨ets, acts, reqty⟩ tys tyList →
    AllLub hdTy tyList lubTy →
    HasType (.set xs) c ⟨ets, acts, reqty⟩
      (.set tys (.set lubTy)) (.set lubTy) ∅
  | record :
    ∀ axs c ets acts reqty atys atyList,
    HasTypeRecord axs c ⟨ets, acts, reqty⟩ atys atyList →
    HasType (.record axs) c ⟨ets, acts, reqty⟩
      (.record atys (.record (.mk atyList)))
      (.record (.mk atyList))
      ∅

/-- Typing a list of expressions. Produces both the TypedExpr list and the
    CedarType list (so Specimen can use the type list for AllLub). -/
inductive HasTypeList : List Expr → Capabilities → TypeEnv → List TypedExpr → List CedarType → Prop where
  | nil :
    ∀ c env,
    HasTypeList [] c env [] []
  | cons :
    ∀ x xs c env tx ty txs tys,
    HasType x c env tx ty ∅ →
    HasTypeList xs c env txs tys →
    HasTypeList (x :: xs) c env (tx :: txs) (ty :: tys)

/-- Typing a record. Produces both (Attr × TypedExpr) list and the
    (Attr × QualifiedType) list for the record type. -/
inductive HasTypeRecord : List (Attr × Expr) → Capabilities → TypeEnv → List (Attr × TypedExpr) → List (Attr × QualifiedType) → Prop where
  | nil :
    ∀ c env,
    HasTypeRecord [] c env [] []
  | cons :
    ∀ a x axs c env tx ty atys atyList,
    HasType x c env tx ty ∅ →
    HasTypeRecord axs c env atys atyList →
    HasTypeRecord ((a, x) :: axs) c env ((a, tx) :: atys) ((a, .required ty) :: atyList)

end

end CedarGen.Relational

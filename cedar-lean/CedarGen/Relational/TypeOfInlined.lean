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

/- # Inlined relational specification of the Cedar typing judgement

This module is a variant of `TypeOf.lean` that inlines all dispatch-table
auxiliary relations (HasTypeArith, HasTypeIf, HasTypeAnd, HasTypeOr,
HasTypeEqNonLit, HasTypeSetOp, HasTypeMem, HasTypeUnaryApp, HasTypeHasAttr,
HasTypeGetAttr) directly into `HasType` constructors.

The goal: each constructor hardcodes the exact sub-expression types, so the
derived generator can route directly to a constructor with zero intermediate
auxiliary generation.  Structural helpers that are recursive or schema-dependent
(Lub, CapMerge, MapContains, etc.) are kept as separate relations.
-/

namespace CedarGen.Relational.Inlined

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/- ## Re-exported structural helpers (same as TypeOf.lean) -/

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

mutual

inductive Lub : CedarType → CedarType → CedarType → Prop where
  | boolSame : ∀ b, Lub (.bool b) (.bool b) (.bool b)
  | boolDiff : ∀ b₁ b₂, BoolTypeNeq b₁ b₂ → Lub (.bool b₁) (.bool b₂) (.bool .anyBool)
  | int : Lub .int .int .int
  | string : Lub .string .string .string
  | entity : ∀ ety, Lub (.entity ety) (.entity ety) (.entity ety)
  | ext : ∀ xty, Lub (.ext xty) (.ext xty) (.ext xty)
  | set : ∀ s₁ s₂ s, Lub s₁ s₂ s → Lub (.set s₁) (.set s₂) (.set s)
  | record : ∀ r₁ r₂ r, LubRecord r₁ r₂ r → Lub (.record (.mk r₁)) (.record (.mk r₂)) (.record (.mk r))

inductive LubQualified : QualifiedType → QualifiedType → QualifiedType → Prop where
  | optional : ∀ t₁ t₂ t, Lub t₁ t₂ t → LubQualified (.optional t₁) (.optional t₂) (.optional t)
  | required : ∀ t₁ t₂ t, Lub t₁ t₂ t → LubQualified (.required t₁) (.required t₂) (.required t)

inductive LubRecord : List (Attr × QualifiedType) → List (Attr × QualifiedType) → List (Attr × QualifiedType) → Prop where
  | nil : LubRecord [] [] []
  | cons : ∀ k v₁ v₂ v r₁ r₂ r, LubQualified v₁ v₂ v → LubRecord r₁ r₂ r → LubRecord ((k, v₁) :: r₁) ((k, v₂) :: r₂) ((k, v) :: r)

end

/- ## Map/Set membership -/

inductive MapContains {α β : Type} : α → β → Map α β → Prop where
  | here : ∀ k v rest, MapContains k v (.mk ((k, v) :: rest))
  | there : ∀ k v k' v' rest, MapContains k v (.mk rest) → MapContains k v (.mk ((k', v') :: rest))

inductive SetContains {α : Type} : α → Set α → Prop where
  | here : ∀ x rest, SetContains x (.mk (x :: rest))
  | there : ∀ x y rest, SetContains x (.mk rest) → SetContains x (.mk (y :: rest))

inductive SameEntityType : EntityType → EntityType → Prop where
 | mk : SameEntityType a a

inductive SameString : String → String → Prop where
 | mk : SameString a a

inductive MapContainsPairKey {v} : EntityType → String → v → Map EntityUID v → Prop where
  | here : MapContainsPairKey a b va (Map.mk ((⟨a,b⟩, va) :: m))
  | nextA : Not (SameEntityType a a') → MapContainsPairKey a b va (Map.mk m) → MapContainsPairKey a b va (Map.mk ((⟨a',b'⟩, v') :: m))
  | nextB : Not (SameString b b') → MapContainsPairKey a b va (Map.mk m) → MapContainsPairKey a b va (Map.mk ((⟨a',b'⟩, v') :: m))

/- ## Entity UID validity -/

inductive ValidEntityUID : EntityType → String → EntitySchema → ActionSchema → Prop where
  | standard : ∀ ety eid entry ets acts, MapContains ety (EntitySchemaEntry.standard entry) ets → ValidEntityUID ety eid ets acts
  | enum : ∀ ety eid eids ets acts, MapContains ety (EntitySchemaEntry.enum eids) ets → SetContains eid eids → ValidEntityUID ety eid ets acts
  | action : ∀ ety eid ets acts entry, MapContainsPairKey ety eid entry acts → ValidEntityUID ety eid ets acts

/- ## Literal typing -/

inductive HasTypeLit : Prim → EntitySchema → ActionSchema → TypedExpr → CedarType → Prop where
  | boolTrue : ∀ ets acts, HasTypeLit (.bool true) ets acts (.lit (.bool true) (.bool .tt)) (.bool .tt)
  | boolFalse : ∀ ets acts, HasTypeLit (.bool false) ets acts (.lit (.bool false) (.bool .ff)) (.bool .ff)
  | int : ∀ i ets acts, HasTypeLit (.int i) ets acts (.lit (.int i) .int) .int
  | string : ∀ s ets acts, HasTypeLit (.string s) ets acts (.lit (.string s) .string) .string
  | entity : ∀ ety eid ets acts, ValidEntityUID ety eid ets acts → HasTypeLit (.entityUID ⟨ety, eid⟩) ets acts (.lit (.entityUID ⟨ety, eid⟩) (.entity ety)) (.entity ety)

/- ## Variable typing -/

inductive HasTypeVar : Var → EntitySchema → ActionSchema → RequestType → TypedExpr → CedarType → Prop where
  | principal : ∀ ets acts princ action resource ctx, HasTypeVar .principal ets acts ⟨princ, action, resource, ctx⟩ (.var .principal (.entity princ)) (.entity princ)
  | action : ∀ ets acts princ actionTy actionEid resource ctx, HasTypeVar .action ets acts ⟨princ, ⟨actionTy, actionEid⟩, resource, ctx⟩ (.var .action (.entity actionTy)) (.entity actionTy)
  | resource : ∀ ets acts princ action resource ctx, HasTypeVar .resource ets acts ⟨princ, action, resource, ctx⟩ (.var .resource (.entity resource)) (.entity resource)
  | context : ∀ ets acts princ action resource ctx, HasTypeVar .context ets acts ⟨princ, action, resource, ctx⟩ (.var .context (.record ctx)) (.record ctx)

/- ## Equality on literals -/

inductive HasTypeEqLit : Prim → Prim → CedarType → Prop where
  | same : ∀ p, HasTypeEqLit p p (.bool .tt)
  | diff : ∀ p₁ p₂, PrimNeq p₁ p₂ → HasTypeEqLit p₁ p₂ (.bool .ff)

/- ## Extension function call typing -/

inductive ValidDecimal : String → Prop where
  | mk : ∀ s d, Cedar.Spec.Ext.Decimal.decimal s = some d → ValidDecimal s

inductive ValidIP : String → Prop where
  | mk : ∀ s ip, Cedar.Spec.Ext.IPAddr.ip s = some ip → ValidIP s

inductive ValidDatetime : String → Prop where
  | mk : ∀ s dt, Cedar.Spec.Ext.Datetime.parse s = some dt → ValidDatetime s

inductive ValidDuration : String → Prop where
  | mk : ∀ s dur, Cedar.Spec.Ext.Datetime.Duration.parse s = some dur → ValidDuration s

inductive HasTypeCall : ExtFun → List CedarType → List Expr → CedarType → Prop where
  | decimal : ∀ s, ValidDecimal s → HasTypeCall .decimal [.string] [.lit (.string s)] (.ext .decimal)
  | ip : ∀ s, ValidIP s → HasTypeCall .ip [.string] [.lit (.string s)] (.ext .ipAddr)
  | datetime : ∀ s, ValidDatetime s → HasTypeCall .datetime [.string] [.lit (.string s)] (.ext .datetime)
  | duration : ∀ s, ValidDuration s → HasTypeCall .duration [.string] [.lit (.string s)] (.ext .duration)
  | lessThan : ∀ xs, HasTypeCall .lessThan [.ext .decimal, .ext .decimal] xs (.bool .anyBool)
  | lessThanOrEqual : ∀ xs, HasTypeCall .lessThanOrEqual [.ext .decimal, .ext .decimal] xs (.bool .anyBool)
  | greaterThan : ∀ xs, HasTypeCall .greaterThan [.ext .decimal, .ext .decimal] xs (.bool .anyBool)
  | greaterThanOrEqual : ∀ xs, HasTypeCall .greaterThanOrEqual [.ext .decimal, .ext .decimal] xs (.bool .anyBool)
  | isIpv4 : ∀ xs, HasTypeCall .isIpv4 [.ext .ipAddr] xs (.bool .anyBool)
  | isIpv6 : ∀ xs, HasTypeCall .isIpv6 [.ext .ipAddr] xs (.bool .anyBool)
  | isLoopback : ∀ xs, HasTypeCall .isLoopback [.ext .ipAddr] xs (.bool .anyBool)
  | isMulticast : ∀ xs, HasTypeCall .isMulticast [.ext .ipAddr] xs (.bool .anyBool)
  | isInRange : ∀ xs, HasTypeCall .isInRange [.ext .ipAddr, .ext .ipAddr] xs (.bool .anyBool)
  | offset : ∀ xs, HasTypeCall .offset [.ext .datetime, .ext .duration] xs (.ext .datetime)
  | durationSince : ∀ xs, HasTypeCall .durationSince [.ext .datetime, .ext .datetime] xs (.ext .duration)
  | toDate : ∀ xs, HasTypeCall .toDate [.ext .datetime] xs (.ext .datetime)
  | toTime : ∀ xs, HasTypeCall .toTime [.ext .datetime] xs (.ext .duration)
  | toMilliseconds : ∀ xs, HasTypeCall .toMilliseconds [.ext .duration] xs .int
  | toSeconds : ∀ xs, HasTypeCall .toSeconds [.ext .duration] xs .int
  | toMinutes : ∀ xs, HasTypeCall .toMinutes [.ext .duration] xs .int
  | toHours : ∀ xs, HasTypeCall .toHours [.ext .duration] xs .int
  | toDays : ∀ xs, HasTypeCall .toDays [.ext .duration] xs .int

/- ## Set literal element typing -/

inductive AllLub : CedarType → List CedarType → CedarType → Prop where
  | nil : ∀ ty, AllLub ty [] ty
  | cons : ∀ acc hd tl lubTy result, Lub acc hd lubTy → AllLub lubTy tl result → AllLub acc (hd :: tl) result

/- ## Capability relations -/

inductive CapMem : Expr → Key → Capabilities → Prop where
  | here : ∀ x k rest, CapMem x k ((x, k) :: rest)
  | there : ∀ x k x' k' rest, CapMem x k rest → CapMem x k ((x', k') :: rest)

inductive CapMerge : Capabilities → Capabilities → Capabilities → Prop where
  | nil : CapMerge [] [] []
  | left : ∀ x k c₁ c₂ c, CapMerge c₁ c₂ c → CapMerge ((x, k) :: c₁) c₂ ((x, k) :: c)
  | right : ∀ x k c₁ c₂ c, CapMerge c₁ c₂ c → CapMerge c₁ ((x, k) :: c₂) ((x, k) :: c)
  | both : ∀ x k c₁ c₂ c, CapMerge c₁ c₂ c → CapMerge ((x, k) :: c₁) ((x, k) :: c₂) ((x, k) :: c)

inductive CapSubset : Capabilities → Capabilities → Prop where
  | nil : CapSubset [] c
  | cons : ∀ x k rest c, CapMem x k c → CapSubset rest c → CapSubset ((x, k) :: rest) c

/- ## Attribute access helpers -/

inductive HasAttrInRecord : RecordType → Expr → Attr → Capabilities → Bool → CedarType → Capabilities → Prop where
  | found_in_caps : ∀ rty x a c knownToExist qty, MapContains a qty rty → CapMem x (.attr a) c → HasAttrInRecord rty x a c knownToExist (.bool .tt) []
  | found_required_known : ∀ rty x a c ty, MapContains a (.required ty) rty → HasAttrInRecord rty x a c true (.bool .tt) []
  | found_not_known : ∀ rty x a c qty, MapContains a qty rty → HasAttrInRecord rty x a c false (.bool .anyBool) [(x, .attr a)]
  | found_optional_known : ∀ rty x a c ty, MapContains a (.optional ty) rty → HasAttrInRecord rty x a c true (.bool .anyBool) [(x, .attr a)]

inductive GetAttrInRecord : CedarType → RecordType → Expr → Attr → Capabilities → CedarType → Prop where
  | required : ∀ ty rty x a c aty, MapContains a (.required aty) rty → GetAttrInRecord ty rty x a c aty
  | optional : ∀ ty rty x a c aty, MapContains a (.optional aty) rty → CapMem x (.attr a) c → GetAttrInRecord ty rty x a c aty

/- ## Entity ancestry -/

inductive DescendentOf : EntitySchema → ActionSchema → EntityType → EntityType → Prop where
  | refl : ∀ ets acts ety, DescendentOf ets acts ety ety
  | ancestor : ∀ ets acts ety₁ ety₂ ancs attrs tags, MapContains ety₁ (.standard ⟨ancs, attrs, tags⟩) ets → SetContains ety₂ ancs → DescendentOf ets acts ety₁ ety₂

/- ## Predicates with DecOpt -/

inductive BothLit : Expr → Expr → Prop where
  | mk : ∀ p₁ p₂, BothLit (.lit p₁) (.lit p₂)

instance : DecOpt (BothLit x₁ x₂) where
  decOpt _ := .ok (match x₁, x₂ with | .lit _, .lit _ => true | _, _ => false)

/- ## Result type -/

inductive TypeResult where
  | ok
  | error (e : TypeError)
deriving Repr, DecidableEq

/- ## Main typing relation (INLINED)

All dispatch-table auxiliaries are expanded into individual constructors.
Each constructor hardcodes the exact types, so the generator can route
directly without intermediate auxiliary generation. -/

mutual

inductive HasType : Expr → Capabilities → TypeEnv → Option TypedExpr → Option CedarType → Option Capabilities → TypeResult → Prop where
  /- ### Literals -/
  | lit :
    ∀ p c ets acts reqty tx ty,
    HasTypeLit p ets acts tx ty →
    HasType (.lit p) c ⟨ets, acts, reqty⟩ (some tx) (some ty) (some []) TypeResult.ok

  /- ### Variables -/
  | var :
    ∀ v c ets acts reqty tx ty,
    HasTypeVar v ets acts reqty tx ty →
    HasType (.var v) c ⟨ets, acts, reqty⟩ (some tx) (some ty) (some []) .ok

  /- ### Unary: not -/
  | unaryAppNotTt :
    ∀ x₁ c ets acts reqty tx₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .tt)) (some []) .ok →
    HasType (.unaryApp .not x₁) c ⟨ets, acts, reqty⟩
      (some (.unaryApp .not tx₁ (.bool .ff))) (some (.bool .ff)) (some []) .ok
  | unaryAppNotFf :
    ∀ x₁ c ets acts reqty tx₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .ff)) (some []) .ok →
    HasType (.unaryApp .not x₁) c ⟨ets, acts, reqty⟩
      (some (.unaryApp .not tx₁ (.bool .tt))) (some (.bool .tt)) (some []) .ok
  | unaryAppNotAny :
    ∀ x₁ c ets acts reqty tx₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .anyBool)) (some []) .ok →
    HasType (.unaryApp .not x₁) c ⟨ets, acts, reqty⟩
      (some (.unaryApp .not tx₁ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok

  /- ### Unary: neg -/
  | unaryAppNeg :
    ∀ x₁ c ets acts reqty tx₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some .int) (some []) .ok →
    HasType (.unaryApp .neg x₁) c ⟨ets, acts, reqty⟩
      (some (.unaryApp .neg tx₁ .int)) (some .int) (some []) .ok

  /- ### Unary: isEmpty -/
  | unaryAppIsEmpty :
    ∀ x₁ c ets acts reqty tx₁ elemTy,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.set elemTy)) (some []) .ok →
    HasType (.unaryApp .isEmpty x₁) c ⟨ets, acts, reqty⟩
      (some (.unaryApp .isEmpty tx₁ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok

  /- ### Unary: like -/
  | unaryAppLike :
    ∀ pat x₁ c ets acts reqty tx₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some .string) (some []) .ok →
    HasType (.unaryApp (.like pat) x₁) c ⟨ets, acts, reqty⟩
      (some (.unaryApp (.like pat) tx₁ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok

  /- ### Unary: is (true — same entity type) -/
  | unaryAppIsTrue :
    ∀ ety x₁ c ets acts reqty tx₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.entity ety)) (some []) .ok →
    HasType (.unaryApp (.is ety) x₁) c ⟨ets, acts, reqty⟩
      (some (.unaryApp (.is ety) tx₁ (.bool .tt))) (some (.bool .tt)) (some []) .ok

  /- ### Unary: is (false — different entity type) -/
  | unaryAppIsFalse :
    ∀ ety₁ ety₂ x₁ c ets acts reqty tx₁,
    ety₁ ≠ ety₂ →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.entity ety₂)) (some []) .ok →
    HasType (.unaryApp (.is ety₁) x₁) c ⟨ets, acts, reqty⟩
      (some (.unaryApp (.is ety₁) tx₁ (.bool .ff))) (some (.bool .ff)) (some []) .ok

  /- ### Binary: eq on literals -/
  | binaryAppEqLit :
    ∀ p₁ p₂ c ets acts reqty tx₁ t₁ tx₂ t₂ ty,
    HasTypeLit p₁ ets acts tx₁ t₁ →
    HasTypeLit p₂ ets acts tx₂ t₂ →
    HasTypeEqLit p₁ p₂ ty →
    HasType (.binaryApp .eq (.lit p₁) (.lit p₂)) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .eq tx₁ tx₂ ty)) (some ty) (some []) .ok

  /- ### Binary: eq non-literal (lub exists) -/
  | binaryAppEqNonLitLub :
    ∀ x₁ x₂ c ets acts reqty tx₁ t₁ tx₂ t₂ lubTy,
    Lub t₁ t₂ lubTy →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some t₁) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some []) .ok →
    ¬ BothLit x₁ x₂ →
    HasType (.binaryApp .eq x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .eq tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok

  /- ### Binary: eq non-literal (entity-entity different) -/
  | binaryAppEqEntityDiff :
    ∀ x₁ x₂ c ets acts reqty tx₁ ety₁ tx₂ ety₂,
    ety₁ ≠ ety₂ →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.entity ety₁)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.entity ety₂)) (some []) .ok →
    ¬ BothLit x₁ x₂ →
    HasType (.binaryApp .eq x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .eq tx₁ tx₂ (.bool .ff))) (some (.bool .ff)) (some []) .ok

  /- ### Binary: arithmetic — less int -/
  | binaryAppLessInt :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some .int) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some .int) (some []) .ok →
    HasType (.binaryApp .less x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .less tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok
  | binaryAppLessDatetime :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.ext .datetime)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.ext .datetime)) (some []) .ok →
    HasType (.binaryApp .less x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .less tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok
  | binaryAppLessDuration :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.ext .duration)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.ext .duration)) (some []) .ok →
    HasType (.binaryApp .less x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .less tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok

  /- ### Binary: arithmetic — lessEq -/
  | binaryAppLessEqInt :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some .int) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some .int) (some []) .ok →
    HasType (.binaryApp .lessEq x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .lessEq tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok
  | binaryAppLessEqDatetime :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.ext .datetime)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.ext .datetime)) (some []) .ok →
    HasType (.binaryApp .lessEq x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .lessEq tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok
  | binaryAppLessEqDuration :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.ext .duration)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.ext .duration)) (some []) .ok →
    HasType (.binaryApp .lessEq x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .lessEq tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok

  /- ### Binary: arithmetic — add/sub/mul -/
  | binaryAppAdd :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some .int) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some .int) (some []) .ok →
    HasType (.binaryApp .add x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .add tx₁ tx₂ .int)) (some .int) (some []) .ok
  | binaryAppSub :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some .int) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some .int) (some []) .ok →
    HasType (.binaryApp .sub x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .sub tx₁ tx₂ .int)) (some .int) (some []) .ok
  | binaryAppMul :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some .int) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some .int) (some []) .ok →
    HasType (.binaryApp .mul x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .mul tx₁ tx₂ .int)) (some .int) (some []) .ok

  /- ### Binary: set operations — contains -/
  | binaryAppContains :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂ t₂ elemTy lubTy,
    Lub t₂ elemTy lubTy →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.set elemTy)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some []) .ok →
    HasType (.binaryApp .contains x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .contains tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok
  | binaryAppContainsAll :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂ elemTy₁ elemTy₂ lubTy,
    Lub elemTy₁ elemTy₂ lubTy →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.set elemTy₁)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.set elemTy₂)) (some []) .ok →
    HasType (.binaryApp .containsAll x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .containsAll tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok
  | binaryAppContainsAny :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂ elemTy₁ elemTy₂ lubTy,
    Lub elemTy₁ elemTy₂ lubTy →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.set elemTy₁)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.set elemTy₂)) (some []) .ok →
    HasType (.binaryApp .containsAny x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .containsAny tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok

  /- ### Binary: mem — entity in entity (descendent) -/
  | binaryAppMemEntityEntity :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂ ety₁ ety₂,
    DescendentOf ets acts ety₁ ety₂ →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.entity ety₁)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.entity ety₂)) (some []) .ok →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .mem tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok
  | binaryAppMemEntitySame :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂ ety,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.entity ety)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.entity ety)) (some []) .ok →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .mem tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok
  | binaryAppMemEntitySet :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂ ety₁ ety₂,
    DescendentOf ets acts ety₁ ety₂ →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.entity ety₁)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.set (.entity ety₂))) (some []) .ok →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .mem tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok
  | binaryAppMemEntitySetSame :
    ∀ x₁ x₂ c ets acts reqty tx₁ tx₂ ety,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.entity ety)) (some []) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.set (.entity ety))) (some []) .ok →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.binaryApp .mem tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some []) .ok

  /- ### hasAttr — record -/
  | hasAttrRecord :
    ∀ x₁ a c ets acts reqty tx₁ rty ty caps,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.record rty)) (some []) .ok →
    HasAttrInRecord rty x₁ a c true ty caps →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩
      (some (.hasAttr tx₁ a ty)) (some ty) (some caps) .ok

  /- ### hasAttr — entity -/
  | hasAttrEntity :
    ∀ x₁ a c ets acts reqty tx₁ ety ty caps ancs rty tags,
    MapContains ety (.standard ⟨ancs, rty, tags⟩) ets →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.entity ety)) (some []) .ok →
    HasAttrInRecord rty x₁ a c false ty caps →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩
      (some (.hasAttr tx₁ a ty)) (some ty) (some caps) .ok

  /- ### getAttr — record -/
  | getAttrRecord :
    ∀ x₁ a c ets acts reqty tx₁ rty ty,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.record rty)) (some []) .ok →
    GetAttrInRecord (.record rty) rty x₁ a c ty →
    HasType (.getAttr x₁ a) c ⟨ets, acts, reqty⟩
      (some (.getAttr tx₁ a ty)) (some ty) (some []) .ok

  /- ### getAttr — entity -/
  | getAttrEntity :
    ∀ x₁ a c ets acts reqty tx₁ ety ty ancs rty tags,
    MapContains ety (.standard ⟨ancs, rty, tags⟩) ets →
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.entity ety)) (some []) .ok →
    GetAttrInRecord (.entity ety) rty x₁ a c ty →
    HasType (.getAttr x₁ a) c ⟨ets, acts, reqty⟩
      (some (.getAttr tx₁ a ty)) (some ty) (some []) .ok

  /- ### ite — condition true -/
  | iteTt :
    ∀ x₁ x₂ x₃ c ets acts reqty tx₁ c₁ c_c₁ tx₂ t₂ c₂ tx₃ t₃ c₃ cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .tt)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some c₂) .ok →
    HasType x₃ c ⟨ets, acts, reqty⟩ (some tx₃) (some t₃) (some c₃) .ok →
    CapMerge c₁ c₂ cout →
    HasType (.ite x₁ x₂ x₃) c ⟨ets, acts, reqty⟩
      (some (.ite tx₁ tx₂ tx₃ t₂)) (some t₂) (some cout) .ok

  /- ### ite — condition false -/
  | iteFf :
    ∀ x₁ x₂ x₃ c ets acts reqty tx₁ c₁ c_c₁ tx₂ t₂ c₂ tx₃ t₃ c₃,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .ff)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some c₂) .ok →
    HasType x₃ c ⟨ets, acts, reqty⟩ (some tx₃) (some t₃) (some c₃) .ok →
    HasType (.ite x₁ x₂ x₃) c ⟨ets, acts, reqty⟩
      (some (.ite tx₁ tx₂ tx₃ t₃)) (some t₃) (some c₃) .ok

  /- ### ite — condition anyBool -/
  | iteAnyBool :
    ∀ x₁ x₂ x₃ c ets acts reqty tx₁ c₁ c_c₁ tx₂ t₂ c₂ tx₃ t₃ c₃ lubTy c₁₂ cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .anyBool)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some t₂) (some c₂) .ok →
    HasType x₃ c ⟨ets, acts, reqty⟩ (some tx₃) (some t₃) (some c₃) .ok →
    Lub t₂ t₃ lubTy →
    CapMerge c₁ c₂ c₁₂ →
    CapSubset cout c₁₂ →
    CapSubset cout c₃ →
    HasType (.ite x₁ x₂ x₃) c ⟨ets, acts, reqty⟩
      (some (.ite tx₁ tx₂ tx₃ lubTy)) (some lubTy) (some cout) .ok

  /- ### and — short-circuit (condition false) -/
  | andShort :
    ∀ x₁ x₂ c ets acts reqty tx₁ c₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .ff)) (some c₁) .ok →
    HasType (.and x₁ x₂) c ⟨ets, acts, reqty⟩
      (some tx₁) (some (.bool .ff)) (some []) .ok

  /- ### and — tt then ff -/
  | andTtFf :
    ∀ x₁ x₂ c ets acts reqty tx₁ c₁ c_c₁ tx₂ c₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .tt)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool .ff)) (some c₂) .ok →
    HasType (.and x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.and tx₁ tx₂ (.bool .ff))) (some (.bool .ff)) (some []) .ok

  /- ### and — tt then tt -/
  | andTtTt :
    ∀ x₁ x₂ c ets acts reqty tx₁ c₁ c_c₁ tx₂ c₂ cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .tt)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool .tt)) (some c₂) .ok →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.and tx₁ tx₂ (.bool .tt))) (some (.bool .tt)) (some cout) .ok

  /- ### and — tt then anyBool -/
  | andTtAny :
    ∀ x₁ x₂ c ets acts reqty tx₁ c₁ c_c₁ tx₂ c₂ cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .tt)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool .anyBool)) (some c₂) .ok →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.and tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some cout) .ok

  /- ### and — anyBool then ff -/
  | andAnyFf :
    ∀ x₁ x₂ c ets acts reqty tx₁ b₁ c₁ c_c₁ tx₂ c₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool b₁)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool .ff)) (some c₂) .ok →
    HasType (.and x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.and tx₁ tx₂ (.bool .ff))) (some (.bool .ff)) (some []) .ok

  /- ### and — anyBool then tt -/
  | andAnyTt :
    ∀ x₁ x₂ c ets acts reqty tx₁ b₁ c₁ c_c₁ tx₂ c₂ cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool b₁)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool .tt)) (some c₂) .ok →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.and tx₁ tx₂ (.bool b₁))) (some (.bool b₁)) (some cout) .ok

  /- ### and — anyBool then anyBool -/
  | andAnyAny :
    ∀ x₁ x₂ c ets acts reqty tx₁ b₁ c₁ c_c₁ tx₂ c₂ cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool b₁)) (some c₁) .ok →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool .anyBool)) (some c₂) .ok →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.and tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some cout) .ok

  /- ### or — short-circuit (condition true) -/
  | orShort :
    ∀ x₁ x₂ c ets acts reqty tx₁ c₁,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .tt)) (some c₁) .ok →
    HasType (.or x₁ x₂) c ⟨ets, acts, reqty⟩
      (some tx₁) (some (.bool .tt)) (some []) .ok

  /- ### or — ff then b₂ -/
  | orFfThen :
    ∀ x₁ x₂ c ets acts reqty tx₁ c₁ tx₂ b₂ c₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool .ff)) (some c₁) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool b₂)) (some c₂) .ok →
    HasType (.or x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.or tx₁ tx₂ (.bool b₂))) (some (.bool b₂)) (some c₂) .ok

  /- ### or — any then tt -/
  | orAnyTt :
    ∀ x₁ x₂ c ets acts reqty tx₁ b₁ c₁ tx₂ c₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool b₁)) (some c₁) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool .tt)) (some c₂) .ok →
    HasType (.or x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.or tx₁ tx₂ (.bool .tt))) (some (.bool .tt)) (some []) .ok

  /- ### or — any then ff -/
  | orAnyFf :
    ∀ x₁ x₂ c ets acts reqty tx₁ b₁ c₁ tx₂ c₂,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool b₁)) (some c₁) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool .ff)) (some c₂) .ok →
    HasType (.or x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.or tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some c₁) .ok

  /- ### or — any then anyBool -/
  | orAnyAny :
    ∀ x₁ x₂ c ets acts reqty tx₁ b₁ c₁ tx₂ c₂ cout,
    HasType x₁ c ⟨ets, acts, reqty⟩ (some tx₁) (some (.bool b₁)) (some c₁) .ok →
    HasType x₂ c ⟨ets, acts, reqty⟩ (some tx₂) (some (.bool .anyBool)) (some c₂) .ok →
    CapSubset cout c₁ →
    CapSubset cout c₂ →
    HasType (.or x₁ x₂) c ⟨ets, acts, reqty⟩
      (some (.or tx₁ tx₂ (.bool .anyBool))) (some (.bool .anyBool)) (some cout) .ok

  /- ### Set literal -/
  | set :
    ∀ x xs c ets acts reqty tx ty tys tyList lubTy,
    HasType x c ⟨ets, acts, reqty⟩ (some tx) (some ty) (some []) .ok →
    HasTypeList xs c ⟨ets, acts, reqty⟩ tys tyList →
    AllLub ty tyList lubTy →
    HasType (.set (x :: xs)) c ⟨ets, acts, reqty⟩
      (some (.set (tx :: tys) (.set lubTy))) (some (.set lubTy)) (some []) .ok

  /- ### Record literal -/
  | record :
    ∀ axs c ets acts reqty atys atyList,
    HasTypeRecord axs c ⟨ets, acts, reqty⟩ atys atyList →
    HasType (.record axs) c ⟨ets, acts, reqty⟩
      (some (.record atys (.record (.mk atyList))))
      (some (.record (.mk atyList)))
      (some []) .ok

  /- ### Extension function call -/
  | call :
    ∀ xfn xs c ets acts reqty txs tys ty,
    HasTypeList xs c ⟨ets, acts, reqty⟩ txs tys →
    HasTypeCall xfn tys xs ty →
    HasType (.call xfn xs) c ⟨ets, acts, reqty⟩
      (some (.call xfn txs ty)) (some ty) (some []) .ok

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

end CedarGen.Relational.Inlined

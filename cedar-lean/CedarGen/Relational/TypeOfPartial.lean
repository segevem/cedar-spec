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

/- # Partial-type-directed relational specification of the Cedar typing judgement

This variant extends the minimal `TypeOfLean` spec with a `PartialCedarType`
*demand* threaded as an **input** to `HasType`. The `CedarType` output is NOT the
expression's complete type — it is the **filler** of the hole in the partial demand.
The complete type is recovered by plugging the filler back into the demand:

    complete type = plug pt filler

    HasType : Expr → Capabilities → TypeEnv → PartialCedarType → CedarType → Capabilities → Prop
                                             ^^^^^^^^^^^^^^^ input demand   ^^^^^^^^^ hole filler

Examples:
- demand `.hole`,      filler `t`            ⇒ complete `t`               (hole = whole type)
- demand `.entity`,    filler `.entity User` ⇒ complete `.entity User`    (leaf; filler = type)
- demand `.set .hole`, filler `elemTy`       ⇒ complete `.set elemTy`     (filler = element type)
- demand `.set .entity`, filler `.entity U`  ⇒ complete `.set (.entity U)`

Motivation. In `TypeOfLean`, rules for structured operands (getAttr/getTag/mem/…)
first *produce* an entity/element type from the schema and then recurse into the
sub-expression demanding that concrete type — "generate a type and pattern-match".
Here we recurse into the sub-expression with a *partial* demand (e.g. `.entity`),
let the filler (hence the concrete type) flow **out** of that derivation, and only
then look it up in the schema. Order flips from lookup-then-recurse to recurse-then-lookup.

`PartialCedarType` only carries the shapes with inner structure worth demanding
(`entity`, `ext`, `set`) plus a `hole` that matches any type. `bool`/`int`/`string`
have no inner element to extract, so operands of those types are recursed into with
the `.hole` demand (filler = the whole base type). `record` is omitted (a record
demand would need a list of fills, not a single one).
-/

namespace CedarGen.Relational.Partial

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/- ## Partial types and the plug (composition) relation -/

/-- A Cedar type with a hole. Only the shapes worth demanding top-down are kept:
`entity`/`ext` (leaves; the filler is the whole entity/ext type) and `set` (the
element demand nested). `hole` matches any concrete type. -/
inductive PartialCedarType where
  | hole
  | entity
  | ext
  | set (ty : PartialCedarType)
deriving Repr, DecidableEq, Inhabited

/-- Reconstruct the complete `CedarType` by plugging `filler` into the hole of `pt`.
`set` is structural and is rebuilt; the leaf demands take the filler directly (the
`entity`/`ext` *shape* constraint is enforced separately by the `Plug` relation). -/
def plug : PartialCedarType → CedarType → CedarType
  | .hole,   f => f
  | .entity, f => f
  | .ext,    f => f
  | .set p,  f => .set (plug p f)

/-- `Plug pt filler complete`: `complete` is the result of plugging `filler` into
the hole of the partial demand `pt` (`complete = plug pt filler`), and — at
`.entity`/`.ext` leaves — `filler` has the demanded shape. This is the "composition"
tying the `PartialCedarType` input and the `CedarType` filler output of `HasType`
to the expression's actual type. -/
inductive Plug : PartialCedarType → CedarType → CedarType → Prop where
  | hole   : ∀ ty, Plug .hole ty ty
  | entity : ∀ ety, Plug .entity (.entity ety) (.entity ety)
  | ext    : ∀ xty, Plug .ext (.ext xty) (.ext xty)
  | set    : ∀ p f c, Plug p f c → Plug (.set p) f (.set c)

def plugB : PartialCedarType → CedarType → CedarType → Bool
  | .hole,   f, c => f == c
  | .entity, f, c => (f == c) && (match c with | .entity _ => true | _ => false)
  | .ext,    f, c => (f == c) && (match c with | .ext _ => true | _ => false)
  | .set p,  f, c => (match c with | .set c' => plugB p f c' | _ => false)

instance : DecOpt (Plug pt filler complete) where
  decOpt _ := .ok (plugB pt filler complete)

open Plausible in
/- Producer for the filler given the demand `pt` and the complete type `complete`
(the mode used in every rule conclusion). Deterministic: strip the `set` wrappers of
`pt` off `complete`; the remaining subterm is the filler (checking the leaf shape). -/
instance : ArbitrarySizedSuchThat CedarType (fun filler => Plug pt filler complete) where
  arbitrarySizedST _ := do
    let rec go (p : PartialCedarType) (c : CedarType) : Option CedarType :=
      match p, c with
      | .hole,   c          => some c
      | .entity, c@(.entity _) => some c
      | .ext,    c@(.ext _)    => some c
      | .set p', .set c'    => go p' c'
      | _,       _          => none
    match go pt complete with
    | some f => return f
    | none   => throw Gen.genericFailure

/- ## Structural helpers (identical to TypeOfLean) -/

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

mutual
/-- Two types are lub-compatible (a lub exists). Only produces the pair, not the result. -/

inductive LubCompat : CedarType → CedarType → Prop where
  | bool : ∀ b₁ b₂, LubCompat (.bool b₁) (.bool b₂)
  | int : LubCompat .int .int
  | string : LubCompat .string .string
  | entity : ∀ ety, LubCompat (.entity ety) (.entity ety)
  | ext : ∀ xty, LubCompat (.ext xty) (.ext xty)
  | set : ∀ s₁ s₂, LubCompat s₁ s₂ → LubCompat (.set s₁) (.set s₂)
  | record : ∀ r₁ r₂, LubCompatRecord r₁ r₂ → LubCompat (.record (.mk r₁)) (.record (.mk r₂))

inductive LubCompatRecord : List (Attr × QualifiedType) → List (Attr × QualifiedType) → Prop where
  | nil : LubCompatRecord [] []
  | consReq : ∀ k t₁ t₂ r₁ r₂, LubCompat t₁ t₂ → LubCompatRecord r₁ r₂ →
      LubCompatRecord ((k, .required t₁) :: r₁) ((k, .required t₂) :: r₂)
  | consOpt : ∀ k t₁ t₂ r₁ r₂, LubCompat t₁ t₂ → LubCompatRecord r₁ r₂ →
      LubCompatRecord ((k, .optional t₁) :: r₁) ((k, .optional t₂) :: r₂)
end

/- ## Map/Set membership -/

inductive MapContains {α β : Type} : α → β → Map α β → Prop where
  | here : ∀ k v rest, MapContains k v (.mk ((k, v) :: rest))
  | there : ∀ k v k' v' rest, MapContains k v (.mk rest) → MapContains k v (.mk ((k', v') :: rest))

inductive MapNotContainsKey {α β : Type} [DecidableEq α] : α → Map α β → Prop where
  | empty : ∀ k, MapNotContainsKey k (.mk [])
  | skip : ∀ k k' v' rest, k ≠ k' → MapNotContainsKey k (.mk rest) → MapNotContainsKey k (.mk ((k', v') :: rest))

inductive SetContains {α : Type} : α → Set α → Prop where
  | here : ∀ x rest, SetContains x (.mk (x :: rest))
  | there : ∀ x y rest, SetContains x (.mk rest) → SetContains x (.mk (y :: rest))

inductive MapContainsPairKey {v} : EntityType → String → v → Map EntityUID v → Prop where
  | here : MapContainsPairKey a b va (Map.mk ((⟨a,b⟩, va) :: m))
  | nextA : a ≠ a' → MapContainsPairKey a b va (Map.mk m) → MapContainsPairKey a b va (Map.mk ((⟨a',b'⟩, v') :: m))
  | nextB : b ≠ b' → MapContainsPairKey a b va (Map.mk m) → MapContainsPairKey a b va (Map.mk ((⟨a',b'⟩, v') :: m))

/- ## Entity UID validity -/

inductive ValidEntityUID : EntityType → String → EntitySchema → ActionSchema → Prop where
  | standard : ∀ ety eid entry ets acts, MapContains ety (EntitySchemaEntry.standard entry) ets → ValidEntityUID ety eid ets acts
  | enum : ∀ ety eid eids ets acts, MapContains ety (EntitySchemaEntry.enum eids) ets → SetContains eid eids → ValidEntityUID ety eid ets acts
  | action : ∀ ety eid ets acts entry, MapContainsPairKey ety eid entry acts → ValidEntityUID ety eid ets acts

/-- `ety` is a *declared* entity type. Retained for entity *literal* and *variable*
rules; structured-operand rules (getAttr/mem/…) no longer need it — the entity type
now flows out of the operand's own derivation. -/
inductive ValidEntityType : EntityType → EntitySchema → ActionSchema → Prop where
  | inSchema : ∀ ety entry ets acts, MapContains ety entry ets → ValidEntityType ety ets acts
  | isAction : ∀ ety eid entry ets acts, MapContainsPairKey ety eid entry acts → ValidEntityType ety ets acts

/- ## Capability relations -/

inductive CapMem : Expr → Key → Capabilities → Prop where
  | here : ∀ x k rest, CapMem x k ((x, k) :: rest)
  | there : ∀ x k x' k' rest, CapMem x k rest → CapMem x k ((x', k') :: rest)

inductive CapTagMem : Expr → Expr → Capabilities → Prop where
  | here : ∀ x e rest, CapTagMem x e ((x, .tag e) :: rest)
  | there : ∀ x e x' k' rest, CapTagMem x e rest → CapTagMem x e ((x', k') :: rest)

inductive CapAttrMem : Expr → Attr → Capabilities → Prop where
  | here : ∀ x a rest, CapAttrMem x a ((x, .attr a) :: rest)
  | there : ∀ x a x' k' rest, CapAttrMem x a rest → CapAttrMem x a ((x', k') :: rest)

inductive CapMerge : Capabilities → Capabilities → Capabilities → Prop where
  | nil : CapMerge [] [] []
  | left : ∀ x k c₁ c₂ c, CapMerge c₁ c₂ c → CapMerge ((x, k) :: c₁) c₂ ((x, k) :: c)
  | right : ∀ x k c₁ c₂ c, CapMerge c₁ c₂ c → CapMerge c₁ ((x, k) :: c₂) ((x, k) :: c)
  | both : ∀ x k c₁ c₂ c, CapMerge c₁ c₂ c → CapMerge ((x, k) :: c₁) ((x, k) :: c₂) ((x, k) :: c)

inductive CapSubset : Capabilities → Capabilities → Prop where
  | nil : CapSubset [] c
  | cons : ∀ x k rest c, CapMem x k c → CapSubset rest c → CapSubset ((x, k) :: rest) c

instance : DecOpt (CapMem x k c) where
  decOpt _ := .ok (c.any (fun (x', k') => x' == x && k' == k))

instance : DecOpt (CapTagMem x e c) where
  decOpt _ := .ok (c.any (fun (x', k') => x' == x && k' == .tag e))

instance : DecOpt (CapAttrMem x a c) where
  decOpt _ := .ok (c.any (fun (x', k') => x' == x && k' == .attr a))

instance [BEq α] [BEq β] : DecOpt (MapContains k v (m : Map α β)) where
  decOpt _ := .ok (match m with | .mk l => l.any (fun (k', v') => k' == k && v' == v))

instance [DecidableEq α] [BEq α] : DecOpt (MapNotContainsKey (α := α) (β := β) k (m : Map α β)) where
  decOpt _ := .ok (match m with | .mk l => l.all (fun (k', _) => k' != k))

instance [BEq α] : DecOpt (SetContains x (s : Set α)) where
  decOpt _ := .ok (match s with | .mk l => l.any (· == x))

def capIntersect (c₁ c₂ : Capabilities) : Capabilities :=
  c₁.filter (fun (x, k) => c₂.any (fun (x', k') => x' == x && k' == k))

/- ## Attribute access helpers -/

inductive HasAttrInRecord : RecordType → Expr → Attr → Capabilities → Bool → CedarType → Capabilities → Prop where
  | found_in_caps : ∀ rty x a c knownToExist qty, CapAttrMem x a c → MapContains (id a) qty rty → HasAttrInRecord rty x a c knownToExist (.bool .tt) []
  | found_required_known : ∀ rty x a c ty, MapContains a (.required ty) rty → HasAttrInRecord rty x a c true (.bool .tt) []
  | found_not_known : ∀ rty x a c qty, MapContains a qty rty → ¬ CapAttrMem x a c → HasAttrInRecord rty x a c false (.bool .anyBool) [(x, .attr a)]
  | found_optional_known : ∀ rty x a c ty, MapContains a (.optional ty) rty → ¬ CapAttrMem x a c → HasAttrInRecord rty x a c true (.bool .anyBool) [(x, .attr a)]

inductive GetAttrInRecord : CedarType → RecordType → Expr → Attr → Capabilities → CedarType → Prop where
  | required : ∀ ty rty x a c aty, MapContains a (.required aty) rty → GetAttrInRecord ty rty x a c aty
  | optional : ∀ ty rty x a c aty, CapAttrMem x a c → MapContains (id a) (.optional aty) rty → GetAttrInRecord ty rty x a c aty

/- ## Specialized map lookups for standard schema entries -/

inductive MapContainsAncestors : EntityType → Set EntityType → EntitySchema → Prop where
  | here : ∀ ety ancs attrs tags rest,
    MapContainsAncestors ety ancs (.mk ((ety, .standard ⟨ancs, attrs, tags⟩) :: rest))
  | there : ∀ ety ancs k' v' rest,
    MapContainsAncestors ety ancs (.mk rest) →
    MapContainsAncestors ety ancs (.mk ((k', v') :: rest))

inductive MapContainsAttrs : EntityType → RecordType → EntitySchema → Prop where
  | here : ∀ ety ancs attrs tags rest,
    MapContainsAttrs ety attrs (.mk ((ety, .standard ⟨ancs, attrs, tags⟩) :: rest))
  | there : ∀ ety attrs k' v' rest,
    MapContainsAttrs ety attrs (.mk rest) →
    MapContainsAttrs ety attrs (.mk ((k', v') :: rest))

inductive MapContainsTagType : EntityType → CedarType → EntitySchema → Prop where
  | here : ∀ ety ty ancs attrs rest,
    MapContainsTagType ety ty (.mk ((ety, .standard ⟨ancs, attrs, .some ty⟩) :: rest))
  | there : ∀ ety ty k' v' rest,
    MapContainsTagType ety ty (.mk rest) →
    MapContainsTagType ety ty (.mk ((k', v') :: rest))

inductive MapContainsNoTags : EntityType → EntitySchema → Prop where
  | here : ∀ ety ancs attrs rest,
    MapContainsNoTags ety (.mk ((ety, .standard ⟨ancs, attrs, .none⟩) :: rest))
  | there : ∀ ety k' v' rest,
    MapContainsNoTags ety (.mk rest) →
    MapContainsNoTags ety (.mk ((k', v') :: rest))

instance [BEq v] : DecOpt (MapContainsPairKey (v := v) a b va m) where
  decOpt _ := .ok (match m with | .mk l => l.any (fun (uid, val) => uid.ty == a && uid.eid == b && val == va))

instance : DecOpt (MapContainsAncestors ety ancs (ets : EntitySchema)) where
  decOpt _ := .ok (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
    match v with | .standard ⟨a, _, _⟩ => a == ancs | _ => false))

instance : DecOpt (MapContainsAttrs ety attrs (ets : EntitySchema)) where
  decOpt _ := .ok (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
    match v with | .standard ⟨_, a, _⟩ => a == attrs | _ => false))

instance : DecOpt (MapContainsTagType ety ty (ets : EntitySchema)) where
  decOpt _ := .ok (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
    match v with | .standard ⟨_, _, .some t⟩ => t == ty | _ => false))

instance : DecOpt (MapContainsNoTags ety (ets : EntitySchema)) where
  decOpt _ := .ok (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
    match v with | .standard ⟨_, _, .none⟩ => true | _ => false))

/- ## Entity ancestry -/

inductive DescendentOf : EntitySchema → ActionSchema → EntityType → EntityType → Prop where
  | refl : ∀ ets acts ety, DescendentOf ets acts ety ety
  | ancestor : ∀ ets acts ety₁ ety₂ ancs,
    MapContainsAncestors ety₁ ancs ets →
    SetContains ety₂ ancs →
    DescendentOf ets acts ety₁ ety₂

inductive NotDescendentOf : EntitySchema → ActionSchema → EntityType → EntityType → Prop where
  | diff : ∀ ets acts ety₁ ety₂ ancs,
    ety₁ ≠ ety₂ →
    MapContainsAncestors ety₁ ancs ets →
    Not (SetContains ety₂ ancs) →
    NotDescendentOf ets acts ety₁ ety₂

/- ## Action hierarchy (for precise mem typing) -/

inductive ActionDescendentOf : ActionSchema → EntityUID → EntityUID → Prop where
  | refl : ∀ acts uid entry, MapContains uid entry acts → ActionDescendentOf acts uid uid
  | ancestor : ∀ acts uid₁ uid₂ entry,
    MapContains uid₁ entry acts →
    SetContains uid₂ entry.ancestors →
    ActionDescendentOf acts uid₁ uid₂

inductive ActionInSet : ActionSchema → EntityUID → List Expr → Prop where
  | here : ∀ acts uid₁ uid₂ rest,
      ActionDescendentOf acts uid₁ uid₂ →
      ActionInSet acts uid₁ (.lit (.entityUID uid₂) :: rest)
  | there : ∀ acts uid₁ x rest,
      ActionInSet acts uid₁ rest →
      ActionInSet acts uid₁ (x :: rest)

instance : DecOpt (ActionInSet acts uid₁ xs) where
  decOpt _ := .ok (xs.any (fun x => match x with
    | .lit (.entityUID uid₂) => acts.descendentOf uid₁ uid₂
    | _ => false))

inductive NotActionDescendentOf : ActionSchema → EntityUID → EntityUID → Prop where
  | diff : ∀ acts uid₁ uid₂ entry,
    uid₁ ≠ uid₂ →
    MapContains uid₁ entry acts →
    Not (SetContains uid₂ entry.ancestors) →
    NotActionDescendentOf acts uid₁ uid₂

/- ## Tag schema access -/

inductive HasTagSchema : EntitySchema → EntityType → CedarType → Prop where
  | mk : ∀ ets ety ty,
    MapContainsTagType ety ty ets →
    HasTagSchema ets ety ty

inductive NoTags : EntitySchema → EntityType → Prop where
  | none : ∀ ets ety,
    MapContainsNoTags ety ets →
    NoTags ets ety

/- ## Set element type accumulation -/

inductive AllLub : CedarType → List CedarType → CedarType → Prop where
  | nil : ∀ ty, AllLub ty [] ty
  | cons : ∀ acc hd tl lubTy result, Lub acc hd lubTy → AllLub lubTy tl result → AllLub acc (hd :: tl) result

/- ## Extension function call typing -/

inductive ValidDecimal : String → Prop where
  | mk : ∀ s d, Cedar.Spec.Ext.Decimal.decimal s = some d → ValidDecimal s

inductive ValidIP : String → Prop where
  | mk : ∀ s ip, Cedar.Spec.Ext.IPAddr.ip s = some ip → ValidIP s

inductive ValidDatetime : String → Prop where
  | mk : ∀ s dt, Cedar.Spec.Ext.Datetime.parse s = some dt → ValidDatetime s

inductive ValidDuration : String → Prop where
  | mk : ∀ s dur, Cedar.Spec.Ext.Datetime.Duration.parse s = some dur → ValidDuration s

instance : DecOpt (ValidDecimal s) where
  decOpt _ := .ok (Cedar.Spec.Ext.Decimal.decimal s).isSome

instance : DecOpt (ValidIP s) where
  decOpt _ := .ok (Cedar.Spec.Ext.IPAddr.ip s).isSome

instance : DecOpt (ValidDatetime s) where
  decOpt _ := .ok (Cedar.Spec.Ext.Datetime.parse s).isSome

instance : DecOpt (ValidDuration s) where
  decOpt _ := .ok (Cedar.Spec.Ext.Datetime.Duration.parse s).isSome

open Plausible in
instance : ArbitrarySizedSuchThat String ValidDecimal where
  arbitrarySizedST _ := do
    let ⟨intPart, _⟩ ← Gen.choose Int (-9223) 9223 (by omega)
    let ⟨fracDigits, _⟩ ← Gen.choose Nat 1 4 (by omega)
    let ⟨fracVal, _⟩ ← Gen.choose Nat 0 (Nat.pow 10 fracDigits - 1) (by omega)
    let fracStr := s!"{fracVal}"
    let pad := String.mk (List.replicate (fracDigits - fracStr.length) '0')
    let s := s!"{intPart}.{pad}{fracStr}"
    match Cedar.Spec.Ext.Decimal.decimal s with
    | some _ => return s
    | none => throw Gen.genericFailure

open Plausible in
instance : ArbitrarySizedSuchThat String ValidIP where
  arbitrarySizedST _ := do
    let ⟨a, _⟩ ← Gen.choose Nat 0 255 (by omega)
    let ⟨b, _⟩ ← Gen.choose Nat 0 255 (by omega)
    let ⟨c, _⟩ ← Gen.choose Nat 0 255 (by omega)
    let ⟨d, _⟩ ← Gen.choose Nat 0 255 (by omega)
    let s := s!"{a}.{b}.{c}.{d}"
    match Cedar.Spec.Ext.IPAddr.ip s with
    | some _ => return s
    | none => throw Gen.genericFailure

open Plausible in
instance : ArbitrarySizedSuchThat String ValidDatetime where
  arbitrarySizedST _ := do
    let ⟨year, _⟩ ← Gen.choose Nat 1970 2100 (by omega)
    let ⟨month, _⟩ ← Gen.choose Nat 1 12 (by omega)
    let ⟨day, _⟩ ← Gen.choose Nat 1 28 (by omega)
    let mStr := if month < 10 then s!"0{month}" else s!"{month}"
    let dStr := if day < 10 then s!"0{day}" else s!"{day}"
    let s := s!"{year}-{mStr}-{dStr}T00:00:00Z"
    match Cedar.Spec.Ext.Datetime.parse s with
    | some _ => return s
    | none => throw Gen.genericFailure

open Plausible in
instance : ArbitrarySizedSuchThat String ValidDuration where
  arbitrarySizedST _ := do
    let ⟨days, _⟩ ← Gen.choose Nat 0 365 (by omega)
    let ⟨hours, _⟩ ← Gen.choose Nat 0 23 (by omega)
    let ⟨mins, _⟩ ← Gen.choose Nat 0 59 (by omega)
    let ⟨secs, _⟩ ← Gen.choose Nat 0 59 (by omega)
    let s := s!"{days}d{hours}h{mins}m{secs}s"
    match Cedar.Spec.Ext.Datetime.Duration.parse s with
    | some _ => return s
    | none => throw Gen.genericFailure

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

/- ## Predicates -/

inductive BothLit : Expr → Expr → Prop where
  | mk : ∀ p₁ p₂, BothLit (.lit p₁) (.lit p₂)

instance : DecOpt (BothLit x₁ x₂) where
  decOpt _ := .ok (match x₁, x₂ with | .lit _, .lit _ => true | _, _ => false)

inductive IsActionLitMem : Expr → Expr → ActionSchema → Prop where
  | mk : ∀ uid₁ uid₂ acts entry,
    MapContains uid₁ entry acts →
    IsActionLitMem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂)) acts

instance : DecOpt (IsActionLitMem x₁ x₂ acts) where
  decOpt _ := .ok (match x₁, x₂ with
    | .lit (.entityUID uid₁), .lit (.entityUID _) => acts.contains uid₁
    | _, _ => false)

inductive IsActionLitMemSet : Expr → Expr → ActionSchema → Prop where
  | mk : ∀ uid₁ xs acts entry,
    MapContains uid₁ entry acts →
    (∀ x, x ∈ xs → ∃ uid, x = .lit (.entityUID uid)) →
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts

instance : DecOpt (IsActionLitMemSet x₁ x₂ acts) where
  decOpt _ := .ok (match x₁, x₂ with
    | .lit (.entityUID uid₁), .set xs =>
      acts.contains uid₁ && xs.all (match · with | .lit (.entityUID _) => true | _ => false)
    | _, _ => false)

/- ## Main typing relation

Signature: `HasType x c env pt filler cout`
- x     : Expr             (output — the generated expression)
- c     : Capabilities     (input  — available capabilities)
- env   : TypeEnv          (input  — the typing environment)
- pt    : PartialCedarType (input  — the demanded partial type; holes match anything)
- filler: CedarType        (output — the hole filler; complete type = `plug pt filler`)
- cout  : Capabilities     (output — capabilities produced)

Idioms below:
- Base operand of fixed type T (int/string/bool): recurse with demand `.hole`; the
  filler is `T` (whole base type).
- Entity/ext operand: recurse with demand `.entity`/`.ext`; the filler is the whole
  `.entity ety` / `.ext xty` (leaf) — the concrete type flows out.
- Set operand: recurse with demand `.set …`; the filler is the *element* filler,
  e.g. `.set .hole` yields the element type directly.
- Every conclusion computes the complete type `ty` internally and exposes the filler
  via `Plug pt filler ty` (except ite/or, where the filler is taken directly from a
  branch already recursed with `pt`).
-/

mutual

inductive HasType : Expr → Capabilities → TypeEnv → PartialCedarType → CedarType → Capabilities → Prop where
  /- ### Literals -/
  | litBoolTrue :
    ∀ c ets acts reqty pt f,
    Plug pt f (.bool .tt) →
    HasType (.lit (.bool true)) c ⟨ets, acts, reqty⟩ pt f []
  | litBoolFalse :
    ∀ c ets acts reqty pt f,
    Plug pt f (.bool .ff) →
    HasType (.lit (.bool false)) c ⟨ets, acts, reqty⟩ pt f []
  | litInt :
    ∀ i c ets acts reqty pt f,
    Plug pt f .int →
    HasType (.lit (.int i)) c ⟨ets, acts, reqty⟩ pt f []
  | litString :
    ∀ s c ets acts reqty pt f,
    Plug pt f .string →
    HasType (.lit (.string s)) c ⟨ets, acts, reqty⟩ pt f []
  | litEntity :
    ∀ ety eid c ets acts reqty pt f,
    ValidEntityUID ety eid ets acts →
    Plug pt f (.entity ety) →
    HasType (.lit (.entityUID ⟨ety, eid⟩)) c ⟨ets, acts, reqty⟩ pt f []

  /- ### Variables -/
  | varPrincipal :
    ∀ c ets acts princ action resource ctx pt f,
    Plug pt f (.entity princ) →
    HasType (.var .principal) c ⟨ets, acts, ⟨princ, action, resource, ctx⟩⟩ pt f []
  | varAction :
    ∀ c ets acts princ actionTy actionEid resource ctx pt f,
    Plug pt f (.entity actionTy) →
    HasType (.var .action) c ⟨ets, acts, ⟨princ, ⟨actionTy, actionEid⟩, resource, ctx⟩⟩ pt f []
  | varResource :
    ∀ c ets acts princ action resource ctx pt f,
    Plug pt f (.entity resource) →
    HasType (.var .resource) c ⟨ets, acts, ⟨princ, action, resource, ctx⟩⟩ pt f []
  | varContext :
    ∀ c ets acts princ action resource ctx pt f,
    Plug pt f (.record ctx) →
    HasType (.var .context) c ⟨ets, acts, ⟨princ, action, resource, ctx⟩⟩ pt f []

  /- ### Unary: not -/
  | unaryAppNotTt :
    ∀ x₁ c env pt f,
    Plug pt f (.bool .ff) →
    HasType x₁ c env .hole (.bool .tt) [] →
    HasType (.unaryApp .not x₁) c env pt f []
  | unaryAppNotFf :
    ∀ x₁ c env pt f,
    Plug pt f (.bool .tt) →
    HasType x₁ c env .hole (.bool .ff) [] →
    HasType (.unaryApp .not x₁) c env pt f []
  | unaryAppNotAny :
    ∀ x₁ c env pt f,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .hole (.bool .anyBool) [] →
    HasType (.unaryApp .not x₁) c env pt f []

  /- ### Unary: neg -/
  | unaryAppNeg :
    ∀ x₁ c env pt f,
    Plug pt f .int →
    HasType x₁ c env .hole .int [] →
    HasType (.unaryApp .neg x₁) c env pt f []

  /- ### Unary: isEmpty (operand is any set — demand `.set .hole`, filler = element type) -/
  | unaryAppIsEmpty :
    ∀ x₁ c env pt f elemTy,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env (.set .hole) elemTy [] →
    HasType (.unaryApp .isEmpty x₁) c env pt f []

  /- ### Unary: like -/
  | unaryAppLike :
    ∀ pat x₁ c env pt f,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .hole .string [] →
    HasType (.unaryApp (.like pat) x₁) c env pt f []

  /- ### Unary: is (true) — recurse demanding `.entity`; filler = `.entity ety` flows out -/
  | unaryAppIsTrue :
    ∀ ety x₁ c env pt f,
    Plug pt f (.bool .tt) →
    HasType x₁ c env .entity (.entity ety) [] →
    HasType (.unaryApp (.is ety) x₁) c env pt f []

  /- ### Unary: is (false) — operand type `ety₂` flows out; tested type `ety₁` free -/
  | unaryAppIsFalse :
    ∀ ety₁ ety₂ x₁ c env pt f,
    Plug pt f (.bool .ff) →
    ety₁ ≠ ety₂ →
    HasType x₁ c env .entity (.entity ety₂) [] →
    HasType (.unaryApp (.is ety₁) x₁) c env pt f []

  /- ### Binary: eq on literals -/
  | binaryAppEqLitSame :
    ∀ p c env pt f ty,
    Plug pt f (.bool .tt) →
    HasType (.lit p) c env .hole ty [] →
    HasType (.binaryApp .eq (.lit p) (.lit p)) c env pt f []
  | binaryAppEqLitDiff :
    ∀ p₁ p₂ c env pt f ty₁ ty₂,
    Plug pt f (.bool .ff) →
    PrimNeq p₁ p₂ →
    HasType (.lit p₁) c env .hole ty₁ [] →
    HasType (.lit p₂) c env .hole ty₂ [] →
    HasType (.binaryApp .eq (.lit p₁) (.lit p₂)) c env pt f []

  /- ### Binary: eq non-literal (lub exists) -/
  | binaryAppEqNonLitLub :
    ∀ x₁ x₂ c env pt f t₁ t₂ lubTy,
    Plug pt f (.bool .anyBool) →
    Lub t₁ t₂ lubTy →
    HasType x₁ c env .hole t₁ [] →
    HasType x₂ c env .hole t₂ [] →
    ¬ BothLit x₁ x₂ →
    HasType (.binaryApp .eq x₁ x₂) c env pt f []

  /- ### Binary: eq entity-entity different — both operand types flow out -/
  | binaryAppEqEntityDiff :
    ∀ x₁ x₂ c env pt f ety₁ ety₂,
    Plug pt f (.bool .ff) →
    ety₁ ≠ ety₂ →
    HasType x₁ c env .entity (.entity ety₁) [] →
    HasType x₂ c env .entity (.entity ety₂) [] →
    ¬ BothLit x₁ x₂ →
    HasType (.binaryApp .eq x₁ x₂) c env pt f []

  /- ### Binary: arithmetic -/
  | binaryAppLessInt :
    ∀ x₁ x₂ c env pt f,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .hole .int [] →
    HasType x₂ c env .hole .int [] →
    HasType (.binaryApp .less x₁ x₂) c env pt f []
  | binaryAppLessDatetime :
    ∀ x₁ x₂ c env pt f,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .ext (.ext .datetime) [] →
    HasType x₂ c env .ext (.ext .datetime) [] →
    HasType (.binaryApp .less x₁ x₂) c env pt f []
  | binaryAppLessDuration :
    ∀ x₁ x₂ c env pt f,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .ext (.ext .duration) [] →
    HasType x₂ c env .ext (.ext .duration) [] →
    HasType (.binaryApp .less x₁ x₂) c env pt f []
  | binaryAppLessEqInt :
    ∀ x₁ x₂ c env pt f,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .hole .int [] →
    HasType x₂ c env .hole .int [] →
    HasType (.binaryApp .lessEq x₁ x₂) c env pt f []
  | binaryAppLessEqDatetime :
    ∀ x₁ x₂ c env pt f,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .ext (.ext .datetime) [] →
    HasType x₂ c env .ext (.ext .datetime) [] →
    HasType (.binaryApp .lessEq x₁ x₂) c env pt f []
  | binaryAppLessEqDuration :
    ∀ x₁ x₂ c env pt f,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .ext (.ext .duration) [] →
    HasType x₂ c env .ext (.ext .duration) [] →
    HasType (.binaryApp .lessEq x₁ x₂) c env pt f []
  | binaryAppAdd :
    ∀ x₁ x₂ c env pt f,
    Plug pt f .int →
    HasType x₁ c env .hole .int [] →
    HasType x₂ c env .hole .int [] →
    HasType (.binaryApp .add x₁ x₂) c env pt f []
  | binaryAppSub :
    ∀ x₁ x₂ c env pt f,
    Plug pt f .int →
    HasType x₁ c env .hole .int [] →
    HasType x₂ c env .hole .int [] →
    HasType (.binaryApp .sub x₁ x₂) c env pt f []
  | binaryAppMul :
    ∀ x₁ x₂ c env pt f,
    Plug pt f .int →
    HasType x₁ c env .hole .int [] →
    HasType x₂ c env .hole .int [] →
    HasType (.binaryApp .mul x₁ x₂) c env pt f []

  /- ### Binary: set operations (set operands demand `.set .hole`, filler = element type) -/
  | binaryAppContains :
    ∀ x₁ x₂ c env pt f t₂ elemTy,
    Plug pt f (.bool .anyBool) →
    LubCompat t₂ elemTy →
    HasType x₁ c env (.set .hole) elemTy [] →
    HasType x₂ c env .hole t₂ [] →
    HasType (.binaryApp .contains x₁ x₂) c env pt f []
  | binaryAppContainsAll :
    ∀ x₁ x₂ c env pt f elemTy₁ elemTy₂,
    Plug pt f (.bool .anyBool) →
    LubCompat elemTy₁ elemTy₂ →
    HasType x₁ c env (.set .hole) elemTy₁ [] →
    HasType x₂ c env (.set .hole) elemTy₂ [] →
    HasType (.binaryApp .containsAll x₁ x₂) c env pt f []
  | binaryAppContainsAny :
    ∀ x₁ x₂ c env pt f elemTy₁ elemTy₂,
    Plug pt f (.bool .anyBool) →
    LubCompat elemTy₁ elemTy₂ →
    HasType x₁ c env (.set .hole) elemTy₁ [] →
    HasType x₂ c env (.set .hole) elemTy₂ [] →
    HasType (.binaryApp .containsAny x₁ x₂) c env pt f []

  /- ### Binary: mem (generic — excludes action-literal cases)
  Operand entity types flow out of the recursive derivations. For the set operand,
  demand `.set .entity` so the filler is the element entity type `.entity ety₂`. -/
  | binaryAppMemEntityEntity :
    ∀ x₁ x₂ c ets acts reqty pt f ety₁ ety₂,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety₁) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ .entity (.entity ety₂) [] →
    DescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ pt f []
  | binaryAppMemEntitySame :
    ∀ x₁ x₂ c ets acts reqty pt f ety,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ pt f []
  | binaryAppMemEntitySet :
    ∀ x₁ x₂ c ets acts reqty pt f ety₁ ety₂,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety₁) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set .entity) (.entity ety₂) [] →
    DescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ pt f []
  | binaryAppMemEntitySetSame :
    ∀ x₁ x₂ c ets acts reqty pt f ety,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set .entity) (.entity ety) [] →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ pt f []

  /- ### Binary: mem — false (not descendent, excludes action-literal cases) -/
  | binaryAppMemEntityEntityFf :
    ∀ x₁ x₂ c ets acts reqty pt f ety₁ ety₂,
    Plug pt f (.bool .ff) →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety₁) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ .entity (.entity ety₂) [] →
    NotDescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ pt f []
  | binaryAppMemEntitySetFf :
    ∀ x₁ x₂ c ets acts reqty pt f ety₁ ety₂,
    Plug pt f (.bool .ff) →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety₁) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set .entity) (.entity ety₂) [] →
    NotDescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ pt f []

  /- ### Binary: mem — true (known action literal hierarchy) -/
  | binaryAppMemActionLitTt :
    ∀ uid₁ uid₂ c ets acts reqty pt f,
    Plug pt f (.bool .tt) →
    ActionDescendentOf acts uid₁ uid₂ →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ .entity (.entity uid₁.ty) [] →
    HasType (.lit (.entityUID uid₂)) c ⟨ets, acts, reqty⟩ .entity (.entity uid₂.ty) [] →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂))) c ⟨ets, acts, reqty⟩ pt f []
  | binaryAppMemActionLitFf :
    ∀ uid₁ uid₂ c ets acts reqty pt f,
    Plug pt f (.bool .ff) →
    NotActionDescendentOf acts uid₁ uid₂ →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ .entity (.entity uid₁.ty) [] →
    HasType (.lit (.entityUID uid₂)) c ⟨ets, acts, reqty⟩ .entity (.entity uid₂.ty) [] →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂))) c ⟨ets, acts, reqty⟩ pt f []

  /- ### Binary: mem — action literal in set of entity literals -/
  | binaryAppMemActionLitSetTt :
    ∀ uid₁ xs c ets acts reqty pt f ety₂,
    Plug pt f (.bool .tt) →
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts →
    ActionInSet acts uid₁ xs →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ .entity (.entity uid₁.ty) [] →
    HasType (.set xs) c ⟨ets, acts, reqty⟩ (.set .entity) (.entity ety₂) [] →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.set xs)) c ⟨ets, acts, reqty⟩ pt f []
  | binaryAppMemActionLitSetFf :
    ∀ uid₁ xs c ets acts reqty pt f ety₂,
    Plug pt f (.bool .ff) →
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts →
    ¬ ActionInSet acts uid₁ xs →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ .entity (.entity uid₁.ty) [] →
    HasType (.set xs) c ⟨ets, acts, reqty⟩ (.set .entity) (.entity ety₂) [] →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.set xs)) c ⟨ets, acts, reqty⟩ pt f []

  /- ### hasAttr — record (attribute found) -/
  | hasAttrRecord :
    ∀ x₁ a c env pt f rty ty caps,
    Plug pt f ty →
    HasType x₁ c env .hole (.record rty) [] →
    HasAttrInRecord rty x₁ a c true ty caps →
    HasType (.hasAttr x₁ a) c env pt f caps

  /- ### hasAttr — record (attribute not found) -/
  | hasAttrRecordNotFound :
    ∀ x₁ a c env pt f rty,
    Plug pt f (.bool .ff) →
    HasType x₁ c env .hole (.record (.mk rty)) [] →
    MapNotContainsKey a (.mk rty) →
    HasType (.hasAttr x₁ a) c env pt f []

  /- ### hasAttr — entity (attribute found); entity type flows out, then look up attrs -/
  | hasAttrEntity :
    ∀ x₁ a c ets acts reqty pt f ety ty caps rty,
    Plug pt f ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    MapContainsAttrs ety rty ets →
    HasAttrInRecord rty x₁ a c false ty caps →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ pt f caps

  /- ### hasAttr — entity (attribute not found) -/
  | hasAttrEntityNotFound :
    ∀ x₁ a c ets acts reqty pt f ety rty,
    Plug pt f (.bool .ff) →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    MapContainsAttrs ety rty ets →
    MapNotContainsKey a rty →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ pt f []

  /- ### getAttr — record -/
  | getAttrRecord :
    ∀ x₁ a c env pt f rty ty,
    Plug pt f ty →
    HasType x₁ c env .hole (.record rty) [] →
    GetAttrInRecord (.record rty) rty x₁ a c ty →
    HasType (.getAttr x₁ a) c env pt f []

  /- ### getAttr — entity; entity type flows out, then look up attrs -/
  | getAttrEntity :
    ∀ x₁ a c ets acts reqty pt f ety ty rty,
    Plug pt f ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    MapContainsAttrs ety rty ets →
    GetAttrInRecord (.entity ety) rty x₁ a c ty →
    HasType (.getAttr x₁ a) c ⟨ets, acts, reqty⟩ pt f []

  /- ### hasTag — entity has tags, not in capabilities -/
  | hasTagAnyBool :
    ∀ x₁ x₂ c ets acts reqty pt f ety ty,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    HasTagSchema ets ety ty →
    HasType x₂ c ⟨ets, acts, reqty⟩ .hole .string [] →
    HasType (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ pt f [(x₁, .tag x₂)]

  /- ### hasTag — entity has tags, already in capabilities.
  Both operands are produced from `c` via `CapTagMem` (the `id` wrappers keep the
  operand typechecks in check-mode), so `ety` is produced by `HasTagSchema` from the
  schema — the recurse-then-lookup flip does not apply. -/
  | hasTagTt :
    ∀ x₁ x₂ c ets acts reqty pt f ety ty,
    Plug pt f (.bool .tt) →
    CapTagMem x₁ x₂ c →
    HasTagSchema ets ety ty →
    HasType (id x₁) c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    HasType (id x₂) c ⟨ets, acts, reqty⟩ .hole .string [] →
    HasType (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ pt f []

  /- ### hasTag — entity has no tags -/
  | hasTagFf :
    ∀ x₁ x₂ c ets acts reqty pt f ety,
    Plug pt f (.bool .ff) →
    HasType x₁ c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    NoTags ets ety →
    HasType x₂ c ⟨ets, acts, reqty⟩ .hole .string [] →
    HasType (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ pt f []

  /- ### getTag — entity with tags, capability present -/
  | getTag :
    ∀ x₁ x₂ c ets acts reqty pt f ety ty,
    Plug pt f ty →
    CapTagMem x₁ x₂ c →
    HasTagSchema ets ety ty →
    HasType (id x₁) c ⟨ets, acts, reqty⟩ .entity (.entity ety) [] →
    HasType (id x₂) c ⟨ets, acts, reqty⟩ .hole .string [] →
    HasType (.binaryApp .getTag x₁ x₂) c ⟨ets, acts, reqty⟩ pt f []

  /- ### ite — condition true (filler taken directly from the then-branch, recursed with `pt`) -/
  | iteTt :
    ∀ x₁ x₂ x₃ c env pt f₂ c₁ c_c₁ c₂ t₃ cout,
    HasType x₁ c env .hole (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env pt f₂ c₂ →
    HasType x₃ c env .hole t₃ [] →
    CapMerge c₁ c₂ cout →
    HasType (.ite x₁ x₂ x₃) c env pt f₂ cout

  /- ### ite — condition false (filler from the else-branch, recursed with `pt`) -/
  | iteFf :
    ∀ x₁ x₂ x₃ c env pt f₃ c₁ c_c₁ t₂ c₂ c₃,
    HasType x₁ c env .hole (.bool .ff) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env .hole t₂ c₂ →
    HasType x₃ c env pt f₃ c₃ →
    HasType (.ite x₁ x₂ x₃) c env pt f₃ c₃

  /- ### ite — condition anyBool (complete type is the lub; expose its filler) -/
  | iteAnyBool :
    ∀ x₁ x₂ x₃ c env pt f c₁ c_c₁ t₂ c₂ t₃ c₃ lubTy c₁₂,
    Plug pt f lubTy →
    HasType x₁ c env .hole (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env .hole t₂ c₂ →
    HasType x₃ c env .hole t₃ c₃ →
    Lub t₂ t₃ lubTy →
    CapMerge c₁ c₂ c₁₂ →
    HasType (.ite x₁ x₂ x₃) c env pt f (capIntersect c₁₂ c₃)

  /- ### and — short-circuit -/
  | andShort :
    ∀ x₁ x₂ c env pt f c₁,
    Plug pt f (.bool .ff) →
    HasType x₁ c env .hole (.bool .ff) c₁ →
    HasType (.and x₁ x₂) c env pt f []

  /- ### and — tt then ff -/
  | andTtFf :
    ∀ x₁ x₂ c env pt f c₁ c_c₁ c₂,
    Plug pt f (.bool .ff) →
    HasType x₁ c env .hole (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env .hole (.bool .ff) c₂ →
    HasType (.and x₁ x₂) c env pt f []

  /- ### and — tt then tt -/
  | andTtTt :
    ∀ x₁ x₂ c env pt f c₁ c_c₁ c₂ cout,
    Plug pt f (.bool .tt) →
    HasType x₁ c env .hole (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env .hole (.bool .tt) c₂ →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c env pt f cout

  /- ### and — tt then anyBool -/
  | andTtAny :
    ∀ x₁ x₂ c env pt f c₁ c_c₁ c₂ cout,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .hole (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env .hole (.bool .anyBool) c₂ →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c env pt f cout

  /- ### and — anyBool then ff -/
  | andAnyFf :
    ∀ x₁ x₂ c env pt f c₁ c_c₁ c₂,
    Plug pt f (.bool .ff) →
    HasType x₁ c env .hole (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env .hole (.bool .ff) c₂ →
    HasType (.and x₁ x₂) c env pt f []

  /- ### and — anyBool then tt -/
  | andAnyTt :
    ∀ x₁ x₂ c env pt f c₁ c_c₁ c₂ cout,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .hole (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env .hole (.bool .tt) c₂ →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c env pt f cout

  /- ### and — anyBool then anyBool -/
  | andAnyAny :
    ∀ x₁ x₂ c env pt f c₁ c_c₁ c₂ cout,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .hole (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env .hole (.bool .anyBool) c₂ →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c env pt f cout

  /- ### or — short-circuit -/
  | orShort :
    ∀ x₁ x₂ c env pt f c₁,
    Plug pt f (.bool .tt) →
    HasType x₁ c env .hole (.bool .tt) c₁ →
    HasType (.or x₁ x₂) c env pt f []

  /- ### or — ff then b₂ -/
  | orFfThen :
    ∀ x₁ x₂ c env pt f c₁ b₂ c₂,
    Plug pt f (.bool b₂) →
    HasType x₁ c env .hole (.bool .ff) c₁ →
    HasType x₂ c env .hole (.bool b₂) c₂ →
    HasType (.or x₁ x₂) c env pt f c₂

  /- ### or — anyBool then tt -/
  | orAnyTt :
    ∀ x₁ x₂ c env pt f c₁ c₂,
    Plug pt f (.bool .tt) →
    HasType x₁ c env .hole (.bool .anyBool) c₁ →
    HasType x₂ c env .hole (.bool .tt) c₂ →
    HasType (.or x₁ x₂) c env pt f []

  /- ### or — anyBool then ff -/
  | orAnyFf :
    ∀ x₁ x₂ c env pt f c₁ c₂,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .hole (.bool .anyBool) c₁ →
    HasType x₂ c env .hole (.bool .ff) c₂ →
    HasType (.or x₁ x₂) c env pt f c₁

  /- ### or — anyBool then anyBool -/
  | orAnyAny :
    ∀ x₁ x₂ c env pt f c₁ c₂,
    Plug pt f (.bool .anyBool) →
    HasType x₁ c env .hole (.bool .anyBool) c₁ →
    HasType x₂ c env .hole (.bool .anyBool) c₂ →
    HasType (.or x₁ x₂) c env pt f (capIntersect c₁ c₂)

  /- ### Set literal (elements demand `.hole`; complete type `.set lubTy`, expose its filler) -/
  | set :
    ∀ x xs c env pt f ty tyList lubTy,
    Plug pt f (.set lubTy) →
    HasType x c env .hole ty [] →
    HasTypeList xs c env tyList →
    AllLub ty tyList lubTy →
    HasType (.set (x :: xs)) c env pt f []

  /- ### Record literal -/
  | record :
    ∀ axs c env pt f atyList,
    Plug pt f (.record (.mk atyList)) →
    HasTypeRecord axs c env atyList →
    HasType (.record axs) c env pt f []

  /- ### Extension function call -/
  | call :
    ∀ xfn xs c env pt f tys ty,
    Plug pt f ty →
    HasTypeList xs c env tys →
    HasTypeCall xfn tys xs ty →
    HasType (.call xfn xs) c env pt f []

/-- Typing a list of expressions. Each element is recursed into with the `.hole`
demand, so the produced type is the element's *complete* type (used by `AllLub` for
set literals and by `HasTypeCall` for extension-function arguments). -/
inductive HasTypeList : List Expr → Capabilities → TypeEnv → List CedarType → Prop where
  | nil :
    ∀ c env,
    HasTypeList [] c env []
  | cons :
    ∀ x xs c env ty tys,
    HasType x c env .hole ty [] →
    HasTypeList xs c env tys →
    HasTypeList (x :: xs) c env (ty :: tys)

/-- Typing a record. Each field expression is recursed into with the `.hole` demand. -/
inductive HasTypeRecord : List (Attr × Expr) → Capabilities → TypeEnv → List (Attr × QualifiedType) → Prop where
  | nil :
    ∀ c env,
    HasTypeRecord [] c env []
  | cons :
    ∀ a x axs c env ty atyList,
    HasType x c env .hole ty [] →
    HasTypeRecord axs c env atyList →
    HasTypeRecord ((a, x) :: axs) c env ((a, .required ty) :: atyList)

end

end CedarGen.Relational.Partial

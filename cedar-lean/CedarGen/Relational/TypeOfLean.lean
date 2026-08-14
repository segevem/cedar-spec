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

/- # Lean (minimal) relational specification of the Cedar typing judgement

This variant strips out TypedExpr, Option wrappers, and TypeResult.
The signature is just: `HasType : Expr → Capabilities → TypeEnv → CedarType → Capabilities → Prop`

- No TypedExpr output (generator produces only Expr)
- No Option wrapping (all outputs are concrete)
- No TypeResult (only models the success path)
- Inlined dispatch tables (no intermediate auxiliary generation)
- Capabilities still relational (CapMerge/CapSubset)

This should be the closest to what makes Specimen's monolithic HasType fast:
minimal output parameters, hardcoded types per constructor.
-/

namespace CedarGen.Relational.Lean

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/- ## Structural helpers -/

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

/-- `ety` is a *declared* entity type: a key of the entity schema `ets` (standard
or enum — no inhabitant required) or the type of some action in `acts`. This is
exactly the notion of "valid entity type" `typeOf` uses (`typeOfLit`'s
`ets.isValidEntityUID uid || acts.contains uid`, and the `.none → unknownEntity`
branches of hasAttr/getAttr/tag typing). Unlike `ValidEntityUID` it does *not*
require the type to be inhabited, so empty enum types are included — matching
`typeOf`, which never requires an entity type to have members.

In a well-formed environment, every operand of entity type necessarily has a
declared type (by soundness of `HasType` wrt `typeOf`: the only producers of
`.entity ety` are entity literals — guarded by `ValidEntityUID` — variables whose
request types are declared, and attribute accesses whose types come from the
schema). So adding this as a premise to entity-operand rules rejects nothing that
`typeOf` accepts; it only gives Specimen a *finite* producer for the operand's
entity type instead of enumerating `EntityType = Name` unboundedly. -/
inductive ValidEntityType : EntityType → EntitySchema → ActionSchema → Prop where
  | inSchema : ∀ ety entry ets acts, MapContains ety entry ets → ValidEntityType ety ets acts
  | isAction : ∀ ety eid entry ets acts, MapContainsPairKey ety eid entry acts → ValidEntityType ety ets acts

/-- Constructively produce a *valid* entity type (declared in `ets`, or an action type in
    `acts`) that is DISTINCT from a given `other`. `checkEntities` requires the tested type
    of `x is ety` to be declared, and the `.ff` case of `is` additionally requires it to
    differ from the operand's type. Folding both requirements into one relation lets Specimen
    PRODUCE the tested type by walking the schema (binding `ety` via `MapContains`, then
    discarding only the lone `= other` candidate) instead of drawing a type from the unbounded
    `EntityType` space and rejecting when it is undeclared or equal to `other`. The producer
    (`MapContains`/`MapContainsPairKey`) comes first so `ety` is bound before the `≠` guard. -/
inductive ValidDifferentEntityType : EntityType → EntityType → EntitySchema → ActionSchema → Prop where
  | inSchema : ∀ other ety entry ets acts,
      MapContains ety entry ets → ety ≠ other →
      ValidDifferentEntityType other ety ets acts
  | isAction : ∀ other ety eid entry ets acts,
      MapContainsPairKey ety eid entry acts → ety ≠ other →
      ValidDifferentEntityType other ety ets acts

/- ## Capability relations -/

inductive CapMem : Expr → Key → Capabilities → Prop where
  | here : ∀ x k rest, CapMem x k ((x, k) :: rest)
  | there : ∀ x k x' k' rest, CapMem x k rest → CapMem x k ((x', k') :: rest)

/-- Specialized membership for tag capabilities: lifts the tag-key expression to
a top-level argument so Specimen can *produce* `(x, e)` by walking `c` rather than
inverting `.tag e` inside a `Key`. See pitfall #7 (compound constructor args). -/
inductive CapTagMem : Expr → Expr → Capabilities → Prop where
  | here : ∀ x e rest, CapTagMem x e ((x, .tag e) :: rest)
  | there : ∀ x e x' k' rest, CapTagMem x e rest → CapTagMem x e ((x', k') :: rest)

/-- Specialized membership for attribute capabilities: lifts the attr name to a
top-level argument so Specimen can *produce* `a` by walking `c` (given the base
`x`) rather than checking `(x, .attr a) ∈ c` after `a` was drawn from the record
type. Attribute analogue of `CapTagMem`. -/
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
  -- `CapAttrMem` produces `a` from `c` (given `x`); `id a` forces `MapContains`
  -- to check-only so it can't re-produce `a` from `rty`. See getTag/CapTagMem.
  | found_in_caps : ∀ rty x a c knownToExist qty, CapAttrMem x a c → MapContains (id a) qty rty → HasAttrInRecord rty x a c knownToExist (.bool .tt) []
  | found_required_known : ∀ rty x a c ty, MapContains a (.required ty) rty → HasAttrInRecord rty x a c true (.bool .tt) []
  -- `¬ CapAttrMem`: the functional checker returns `.tt` when `(x, .attr a) ∈ c`
  -- (see `hasAttrInRecord`), so the anyBool branch fires only when the cap is
  -- *absent*. Without this guard these overlap with `found_in_caps` and the
  -- generator types `hasAttr` as anyBool where the functional checker says tt.
  | found_not_known : ∀ rty x a c qty, MapContains a qty rty → ¬ CapAttrMem x a c → HasAttrInRecord rty x a c false (.bool .anyBool) [(x, .attr a)]
  | found_optional_known : ∀ rty x a c ty, MapContains a (.optional ty) rty → ¬ CapAttrMem x a c → HasAttrInRecord rty x a c true (.bool .anyBool) [(x, .attr a)]

-- The receiver type is intentionally omitted: the functional `getAttrInRecord`
-- carries it only to build the `.attrNotFound ty a` error message, which this
-- relation (having no error case) never uses. Keeping it as a phantom first
-- argument made the derived checker enumerate it over *all* of `CedarType` (an
-- infinite recursive domain) before discarding it — the source of a divergent
-- generation. Dropping it removes that enumeration at the root.
inductive GetAttrInRecord : RecordType → Expr → Attr → Capabilities → CedarType → Prop where
  | required : ∀ rty x a c aty, MapContains a (.required aty) rty → GetAttrInRecord rty x a c aty
  | optional : ∀ rty x a c aty, CapAttrMem x a c → MapContains (id a) (.optional aty) rty → GetAttrInRecord rty x a c aty

/- ## Specialized map lookups for standard schema entries

These avoid mixing bound/fresh variables inside a compound constructor argument
to MapContains, which Specimen cannot schedule. Each extracts one field as a
top-level output while hiding the others as universally quantified wildcards. -/

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
  -- `refl` must require `uid` to be an *action* (a key in `acts`). Functional
  -- `typeOfInₑ` only takes the action-hierarchy path (→ `.tt`) when `actionUID? x₁`
  -- succeeds; a reflexive `e in e` for a non-action entity is generic → `.anyBool`.
  -- Without this guard, `binaryAppMemActionLitTt` types e.g. `foo::bob in foo::bob`
  -- (foo a normal entity) as `.tt`, which the functional validator rejects.
  | refl : ∀ acts uid entry, MapContains uid entry acts → ActionDescendentOf acts uid uid
  | ancestor : ∀ acts uid₁ uid₂ entry,
    MapContains uid₁ entry acts →
    SetContains uid₂ entry.ancestors →
    ActionDescendentOf acts uid₁ uid₂

/-- Some literal entity in the set `xs` is an action-descendent target of `uid₁`.
Mirrors the functional `uids.any (acts.descendentOf uid₁ ·)` used by `typeOfInₛ`:
`x in [set]` is `tt` iff the set actually *contains* an ancestor of `x`. -/
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

/-! ### Full-coverage generators for extension-function literal strings.
Each builds a value from independently-generated components that span the full
valid space (per the parsers in `Cedar/Spec/Ext/`), formats it to the string the
parser expects, and keeps the parser check as a safety net so out-of-range /
overflow combinations simply retry. -/

/-- Left-pad `n` with `'0'` to at least `width` characters. -/
private def zeroPad (n width : Nat) : String :=
  let s := toString n
  if s.length < width then String.ofList (List.replicate (width - s.length) '0') ++ s else s

/-- Lowercase hexadecimal string of `n` (no padding), for IPv6 groups. -/
private partial def toHexLower (n : Nat) : String :=
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + (d - 10))
  if n < 16 then String.singleton (digit n)
  else toHexLower (n / 16) ++ String.singleton (digit (n % 16))

/-- A string of `n` `'0'` characters, for value-preserving leading-zero forms. -/
private def leadZeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- Draw 0..2 leading zeros — a distinct, parser-accepted spelling of the same
    quantity (`String.toNat?` accepts "007"). Exercised on ~2/3 of quantities. -/
private def genLeadZeros : Plausible.Gen String := do
  let ⟨lz, _⟩ ← Plausible.Gen.choose Nat 0 2 (by omega); pure (leadZeros lz)

/-- One duration unit: with prob. 1/2 present with an arbitrary quantity in
    `0..hi` (optionally leading-zero padded), else omitted (units may be dropped,
    but the whole string must be ordered largest→smallest, enforced at the call
    site). -/
private def genDurUnit (suffix : String) (hi : Nat) : Plausible.Gen String := do
  let ⟨incl, _⟩ ← Plausible.Gen.choose Nat 0 1 (by omega)
  if incl == 0 then pure ""
  else do
    let ⟨q, _⟩ ← Plausible.Gen.choose Nat 0 hi (by omega)
    let lz ← genLeadZeros
    pure s!"{lz}{q}{suffix}"

open Plausible in
instance : ArbitrarySizedSuchThat String ValidDecimal where
  arbitrarySizedST _ := do
    -- integer part spans the full `Int64 / 10^4` range; sign is explicit so
    -- negative values with a zero integer part (e.g. `-0.5`) are reachable.
    let ⟨neg, _⟩ ← Gen.choose Nat 0 1 (by omega)
    let ⟨mag, _⟩ ← Gen.choose Nat 0 922337203685477 (by omega)
    let ⟨fracDigits, _⟩ ← Gen.choose Nat 1 4 (by omega)
    -- `fracVal` left-padded to `fracDigits` covers both `.05` and `.50` spellings.
    let ⟨fracVal, _⟩ ← Gen.choose Nat 0 (Nat.pow 10 fracDigits - 1) (by omega)
    -- leading zeros on the integer part are value-preserving but a distinct
    -- parser input (`String.toInt?` accepts "007" / "-007"); exercise them often.
    let ⟨intLeadZeros, _⟩ ← Gen.choose Nat 0 3 (by omega)
    let magStr := leadZeros intLeadZeros ++ toString mag
    -- sign is unconditional (allows negative zero "-0.0", which parses to 0; only
    -- the bare "-" left part is rejected, and `magStr` is never empty).
    let signStr := if neg == 1 then "-" else ""
    let s := s!"{signStr}{magStr}.{zeroPad fracVal fracDigits}"
    match Cedar.Spec.Ext.Decimal.decimal s with
    | some _ => return s
    | none => throw Gen.genericFailure

open Plausible in
instance : ArbitrarySizedSuchThat String ValidIP where
  arbitrarySizedST _ := do
    -- one IPv6 group: value as lowercase hex, then left-padded with zeros to a
    -- random width in 1..4 (never truncating). Leading-zero groups like `00ff` /
    -- `0001` are a distinct, parser-accepted spelling. Since ~94% of full-range
    -- 16-bit values are already 4 hex digits (no room to pad), half the groups
    -- are drawn from a small range (0..0xff) so leading zeros are non-rare while
    -- the full 0..0xffff range stays covered by the other half.
    let genGroup : Gen String := do
      let ⟨big, _⟩ ← Gen.choose Nat 0 1 (by omega)
      let ⟨g, _⟩ ← Gen.choose Nat 0 (if big == 1 then 65535 else 255) (by omega)
      let hx := toHexLower g
      let ⟨w, _⟩ ← Gen.choose Nat 1 4 (by omega)
      pure (if hx.length < w then leadZeros (w - hx.length) ++ hx else hx)
    -- variant 0/1: IPv4 (plain / CIDR); 2/3: IPv6 full 8-group (plain / CIDR);
    -- 4/5: IPv6 `::`-compressed (plain / CIDR), exercising the parser's
    -- `splitOn "::"` fill branch that the full form never reaches.
    let ⟨variant, _⟩ ← Gen.choose Nat 0 5 (by omega)
    let s ← match variant with
      | 0 | 1 => do
        let ⟨a, _⟩ ← Gen.choose Nat 0 255 (by omega)
        let ⟨b, _⟩ ← Gen.choose Nat 0 255 (by omega)
        let ⟨c, _⟩ ← Gen.choose Nat 0 255 (by omega)
        let ⟨d, _⟩ ← Gen.choose Nat 0 255 (by omega)
        let base := s!"{a}.{b}.{c}.{d}"
        if variant == 0 then pure base
        else do let ⟨p, _⟩ ← Gen.choose Nat 0 32 (by omega); pure s!"{base}/{p}"
      | 2 | 3 => do
        let mut groups : List String := []
        for _ in List.range 8 do groups := groups ++ [← genGroup]
        let base := String.intercalate ":" groups
        if variant == 2 then pure base
        else do let ⟨p, _⟩ ← Gen.choose Nat 0 128 (by omega); pure s!"{base}/{p}"
      | _ => do
        -- `::` stands in for one-or-more zero groups, so the explicit groups
        -- must number strictly fewer than 8 (parser requires `len < 8`).
        let ⟨k, _⟩ ← Gen.choose Nat 0 7 (by omega)      -- explicit group count
        let ⟨nl, _⟩ ← Gen.choose Nat 0 k (by omega)     -- groups left of `::`
        let mut ls : List String := []
        for _ in List.range nl do ls := ls ++ [← genGroup]
        let mut rs : List String := []
        for _ in List.range (k - nl) do rs := rs ++ [← genGroup]
        let base := String.intercalate ":" ls ++ "::" ++ String.intercalate ":" rs
        if variant == 4 then pure base
        else do let ⟨p, _⟩ ← Gen.choose Nat 0 128 (by omega); pure s!"{base}/{p}"
    match Cedar.Spec.Ext.IPAddr.ip s with
    | some _ => return s
    | none => throw Gen.genericFailure

open Plausible in
instance : ArbitrarySizedSuchThat String ValidDatetime where
  arbitrarySizedST _ := do
    let ⟨year, _⟩ ← Gen.choose Nat 1 9999 (by omega)
    let ⟨month, _⟩ ← Gen.choose Nat 1 12 (by omega)
    -- day 1..31; invalid day/month combinations (e.g. Feb 30) are rejected below.
    let ⟨day, _⟩ ← Gen.choose Nat 1 31 (by omega)
    let datePart := s!"{zeroPad year 4}-{zeroPad month 2}-{zeroPad day 2}"
    -- fmt 0: date only, 1: UTC, 2: UTC+ms, 3: offset, 4: offset+ms.
    let ⟨fmt, _⟩ ← Gen.choose Nat 0 4 (by omega)
    let s ← match fmt with
      | 0 => pure datePart
      | f => do
        let ⟨hh, _⟩ ← Gen.choose Nat 0 23 (by omega)
        let ⟨mm, _⟩ ← Gen.choose Nat 0 59 (by omega)
        let ⟨ss, _⟩ ← Gen.choose Nat 0 59 (by omega)
        let time := s!"{zeroPad hh 2}:{zeroPad mm 2}:{zeroPad ss 2}"
        let msPart ← if f == 2 || f == 4 then do
            let ⟨ms, _⟩ ← Gen.choose Nat 0 999 (by omega); pure s!".{zeroPad ms 3}"
          else pure ""
        let tz ← if f == 1 || f == 2 then pure "Z"
          else do
            let ⟨sign, _⟩ ← Gen.choose Nat 0 1 (by omega)
            let ⟨oh, _⟩ ← Gen.choose Nat 0 23 (by omega)
            let ⟨om, _⟩ ← Gen.choose Nat 0 59 (by omega)
            pure s!"{if sign == 0 then "+" else "-"}{zeroPad oh 2}{zeroPad om 2}"
        pure s!"{datePart}T{time}{msPart}{tz}"
    match Cedar.Spec.Ext.Datetime.parse s with
    | some _ => return s
    | none => throw Gen.genericFailure

open Plausible in
instance : ArbitrarySizedSuchThat String ValidDuration where
  arbitrarySizedST _ := do
    let ⟨neg, _⟩ ← Gen.choose Nat 0 1 (by omega)
    let signStr := if neg == 1 then "-" else ""
    -- mode 0: a single unit whose quantity spans that unit's full Int64 range
    --   (reaches high-magnitude durations; the cap is `⌊Int64.max / mult⌋`, so
    --   the summed value always fits — no overflow retries).
    -- mode 1: several units, each with a modest quantity, exercising the ordered
    --   multi-pair form. A rare summed-value overflow simply retries.
    let ⟨mode, _⟩ ← Gen.choose Nat 0 1 (by omega)
    let body ← if mode == 0 then do
        let ⟨u, _⟩ ← Gen.choose Nat 0 4 (by omega)
        let (suffix, hi) := match u with
          | 0 => ("d",  106751991167)
          | 1 => ("h",  2562047788015)
          | 2 => ("m",  153722867280912)
          | 3 => ("s",  9223372036854775)
          | _ => ("ms", 9223372036854775807)
        let ⟨q, _⟩ ← Gen.choose Nat 0 hi (by omega)
        let lz ← genLeadZeros
        pure s!"{lz}{q}{suffix}"
      else do
        -- units ordered largest→smallest, each optionally present with a quantity.
        let d  ← genDurUnit "d"  10000
        let h  ← genDurUnit "h"  100000
        let m  ← genDurUnit "m"  1000000
        let sc ← genDurUnit "s"  1000000
        let ms ← genDurUnit "ms" 100000000
        let b := d ++ h ++ m ++ sc ++ ms
        pure (if b.isEmpty then "0ms" else b)
    let s := signStr ++ body
    match Cedar.Spec.Ext.Datetime.Duration.parse s with
    | some _ => return s
    | none => throw Gen.genericFailure

-- Extension-function typing is inlined directly into `HasType` (see the
-- `call*` constructors): each function's argument types are constants, so the
-- rules state them as direct `HasType` premises rather than routing a `tys`
-- signature list through an auxiliary relation + `HasTypeList`.

/- ## Predicates -/

inductive BothLit : Expr → Expr → Prop where
  | mk : ∀ p₁ p₂, BothLit (.lit p₁) (.lit p₂)

instance : DecOpt (BothLit x₁ x₂) where
  decOpt _ := .ok (match x₁, x₂ with | .lit _, .lit _ => true | _, _ => false)

/-- x₁ is an action-schema literal AND x₂ is an entity literal.
    When both hold, the functional uses action-hierarchy logic for `mem`. -/
inductive IsActionLitMem : Expr → Expr → ActionSchema → Prop where
  | mk : ∀ uid₁ uid₂ acts entry,
    MapContains uid₁ entry acts →
    IsActionLitMem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂)) acts

instance : DecOpt (IsActionLitMem x₁ x₂ acts) where
  decOpt _ := .ok (match x₁, x₂ with
    | .lit (.entityUID uid₁), .lit (.entityUID _) => acts.contains uid₁
    | _, _ => false)

/-- x₁ is an action-schema literal AND x₂ is a set of entity-UID literals.
    When both hold, the functional uses action-hierarchy logic for set `mem`. -/
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

Signature: `HasType x c env ty cout`
- x : Expr (output — the generated expression)
- c : Capabilities (input — available capabilities)
- env : TypeEnv (input — the typing environment)
- ty : CedarType (input — the target type)
- cout : Capabilities (output — capabilities produced)
-/

mutual

inductive HasType : Expr → Capabilities → TypeEnv → CedarType → Capabilities → Prop where
  /- ### Literals -/
  | litBoolTrue :
    ∀ c ets acts reqty,
    HasType (.lit (.bool true)) c ⟨ets, acts, reqty⟩ (.bool .tt) []
  | litBoolFalse :
    ∀ c ets acts reqty,
    HasType (.lit (.bool false)) c ⟨ets, acts, reqty⟩ (.bool .ff) []
  | litInt :
    ∀ i c ets acts reqty,
    HasType (.lit (.int i)) c ⟨ets, acts, reqty⟩ .int []
  | litString :
    ∀ s c ets acts reqty,
    HasType (.lit (.string s)) c ⟨ets, acts, reqty⟩ .string []
  | litEntity :
    ∀ ety eid c ets acts reqty,
    ValidEntityUID ety eid ets acts →
    HasType (.lit (.entityUID ⟨ety, eid⟩)) c ⟨ets, acts, reqty⟩ (.entity ety) []

  /- ### Variables -/
  | varPrincipal :
    ∀ c ets acts princ action resource ctx,
    HasType (.var .principal) c ⟨ets, acts, ⟨princ, action, resource, ctx⟩⟩ (.entity princ) []
  | varAction :
    ∀ c ets acts princ actionTy actionEid resource ctx,
    HasType (.var .action) c ⟨ets, acts, ⟨princ, ⟨actionTy, actionEid⟩, resource, ctx⟩⟩ (.entity actionTy) []
  | varResource :
    ∀ c ets acts princ action resource ctx,
    HasType (.var .resource) c ⟨ets, acts, ⟨princ, action, resource, ctx⟩⟩ (.entity resource) []
  | varContext :
    ∀ c ets acts princ action resource ctx,
    HasType (.var .context) c ⟨ets, acts, ⟨princ, action, resource, ctx⟩⟩ (.record ctx) []

  /- ### Unary: not -/
  | unaryAppNotTt :
    ∀ x₁ c env,
    HasType x₁ c env (.bool .tt) [] →
    HasType (.unaryApp .not x₁) c env (.bool .ff) []
  | unaryAppNotFf :
    ∀ x₁ c env,
    HasType x₁ c env (.bool .ff) [] →
    HasType (.unaryApp .not x₁) c env (.bool .tt) []
  | unaryAppNotAny :
    ∀ x₁ c env,
    HasType x₁ c env (.bool .anyBool) [] →
    HasType (.unaryApp .not x₁) c env (.bool .anyBool) []

  /- ### Unary: neg -/
  | unaryAppNeg :
    ∀ x₁ c env,
    HasType x₁ c env .int [] →
    HasType (.unaryApp .neg x₁) c env .int []

  /- ### Unary: isEmpty -/
  | unaryAppIsEmpty :
    ∀ x₁ c env elemTy,
    HasType x₁ c env (.set elemTy) [] →
    HasType (.unaryApp .isEmpty x₁) c env (.bool .anyBool) []

  /- ### Unary: like -/
  | unaryAppLike :
    ∀ pat x₁ c env,
    HasType x₁ c env .string [] →
    HasType (.unaryApp (.like pat) x₁) c env (.bool .anyBool) []

  /- ### Unary: is (true) -/
  | unaryAppIsTrue :
    ∀ ety x₁ c env,
    ValidEntityType ety env.ets env.acts →
    HasType x₁ c env (.entity ety) [] →
    HasType (.unaryApp (.is ety) x₁) c env (.bool .tt) []

  /- ### Unary: is (false) -/
  -- Both the *tested* type `ety₁` and the *operand* type `ety₂` must be declared:
  -- although `typeOf` alone never requires `ety₁` to be in the schema, the real
  -- `validate` runs `checkEntities` first, which rejects `x is ety₁` for an
  -- undeclared `ety₁` (`unrecognized entity type`). `ValidDifferentEntityType`
  -- produces `ety₁` declared *and* `≠ ety₂` (the `.ff` case needs the mismatch),
  -- so we never emit `is <undeclared>`. `ety₂` is pinned by `ValidEntityType`.
  | unaryAppIsFalse :
    ∀ ety₁ ety₂ x₁ c env,
    ValidEntityType ety₂ env.ets env.acts →
    ValidDifferentEntityType ety₂ ety₁ env.ets env.acts →
    HasType x₁ c env (.entity ety₂) [] →
    HasType (.unaryApp (.is ety₁) x₁) c env (.bool .ff) []

  /- ### Binary: eq on literals -/
  | binaryAppEqLitSame :
    ∀ p c env ty,
    HasType (.lit p) c env ty [] →
    HasType (.binaryApp .eq (.lit p) (.lit p)) c env (.bool .tt) []
  | binaryAppEqLitDiff :
    ∀ p₁ p₂ c env ty₁ ty₂,
    PrimNeq p₁ p₂ →
    HasType (.lit p₁) c env ty₁ [] →
    HasType (.lit p₂) c env ty₂ [] →
    HasType (.binaryApp .eq (.lit p₁) (.lit p₂)) c env (.bool .ff) []

  /- ### Binary: eq non-literal (lub exists) -/
  | binaryAppEqNonLitLub :
    ∀ x₁ x₂ c env t₁ t₂ lubTy,
    Lub t₁ t₂ lubTy →
    HasType x₁ c env t₁ [] →
    HasType x₂ c env t₂ [] →
    ¬ BothLit x₁ x₂ →
    HasType (.binaryApp .eq x₁ x₂) c env (.bool .anyBool) []

  /- ### Binary: eq entity-entity different -/
  | binaryAppEqEntityDiff :
    ∀ x₁ x₂ c env ety₁ ety₂,
    ValidEntityType ety₁ env.ets env.acts →
    ValidEntityType ety₂ env.ets env.acts →
    ety₁ ≠ ety₂ →
    HasType x₁ c env (.entity ety₁) [] →
    HasType x₂ c env (.entity ety₂) [] →
    ¬ BothLit x₁ x₂ →
    HasType (.binaryApp .eq x₁ x₂) c env (.bool .ff) []

  /- ### Binary: arithmetic -/
  | binaryAppLessInt :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int [] →
    HasType x₂ c env .int [] →
    HasType (.binaryApp .less x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessDatetime :
    ∀ x₁ x₂ c env,
    HasType x₁ c env (.ext .datetime) [] →
    HasType x₂ c env (.ext .datetime) [] →
    HasType (.binaryApp .less x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessDuration :
    ∀ x₁ x₂ c env,
    HasType x₁ c env (.ext .duration) [] →
    HasType x₂ c env (.ext .duration) [] →
    HasType (.binaryApp .less x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessEqInt :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int [] →
    HasType x₂ c env .int [] →
    HasType (.binaryApp .lessEq x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessEqDatetime :
    ∀ x₁ x₂ c env,
    HasType x₁ c env (.ext .datetime) [] →
    HasType x₂ c env (.ext .datetime) [] →
    HasType (.binaryApp .lessEq x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessEqDuration :
    ∀ x₁ x₂ c env,
    HasType x₁ c env (.ext .duration) [] →
    HasType x₂ c env (.ext .duration) [] →
    HasType (.binaryApp .lessEq x₁ x₂) c env (.bool .anyBool) []
  | binaryAppAdd :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int [] →
    HasType x₂ c env .int [] →
    HasType (.binaryApp .add x₁ x₂) c env .int []
  | binaryAppSub :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int [] →
    HasType x₂ c env .int [] →
    HasType (.binaryApp .sub x₁ x₂) c env .int []
  | binaryAppMul :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int [] →
    HasType x₂ c env .int [] →
    HasType (.binaryApp .mul x₁ x₂) c env .int []

  /- ### Binary: set operations -/
  | binaryAppContains :
    ∀ x₁ x₂ c env t₂ elemTy,
    LubCompat t₂ elemTy →
    HasType x₁ c env (.set elemTy) [] →
    HasType x₂ c env t₂ [] →
    HasType (.binaryApp .contains x₁ x₂) c env (.bool .anyBool) []
  | binaryAppContainsAll :
    ∀ x₁ x₂ c env elemTy₁ elemTy₂,
    LubCompat elemTy₁ elemTy₂ →
    HasType x₁ c env (.set elemTy₁) [] →
    HasType x₂ c env (.set elemTy₂) [] →
    HasType (.binaryApp .containsAll x₁ x₂) c env (.bool .anyBool) []
  | binaryAppContainsAny :
    ∀ x₁ x₂ c env elemTy₁ elemTy₂,
    LubCompat elemTy₁ elemTy₂ →
    HasType x₁ c env (.set elemTy₁) [] →
    HasType x₂ c env (.set elemTy₂) [] →
    HasType (.binaryApp .containsAny x₁ x₂) c env (.bool .anyBool) []

  /- ### Binary: mem (generic — excludes action-literal cases) -/
  -- `ValidEntityType` gives Specimen a finite producer for an operand entity type
  -- (schema keys / action types) instead of enumerating `Name`. It's implied by
  -- the operand typecheck under a well-formed env, so it rejects nothing `typeOf`
  -- accepts. For the positive cases we pin only `ety₁` and let `DescendentOf`
  -- *produce* `ety₂` (via its `ancestor`/`refl` constructors) — yielding just the
  -- valid descendents rather than enumerating all schema types and filtering.
  | binaryAppMemEntityEntity :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    DescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.entity ety₂) [] →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []
  | binaryAppMemEntitySame :
    ∀ x₁ x₂ c ets acts reqty ety,
    ValidEntityType ety ets acts →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []
  | binaryAppMemEntitySet :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    DescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) [] →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []
  | binaryAppMemEntitySetSame :
    ∀ x₁ x₂ c ets acts reqty ety,
    ValidEntityType ety ets acts →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety)) [] →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []

  /- ### Binary: mem — false (not descendent, excludes action-literal cases) -/
  | binaryAppMemEntityEntityFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    ValidEntityType ety₂ ets acts →
    NotDescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.entity ety₂) [] →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []
  | binaryAppMemEntitySetFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    ValidEntityType ety₂ ets acts →
    NotDescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) [] →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### Binary: mem — true (known action literal hierarchy) -/
  | binaryAppMemActionLitTt :
    ∀ uid₁ uid₂ c ets acts reqty,
    ActionDescendentOf acts uid₁ uid₂ →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) [] →
    HasType (.lit (.entityUID uid₂)) c ⟨ets, acts, reqty⟩ (.entity uid₂.ty) [] →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂))) c ⟨ets, acts, reqty⟩ (.bool .tt) []
  | binaryAppMemActionLitFf :
    ∀ uid₁ uid₂ c ets acts reqty,
    NotActionDescendentOf acts uid₁ uid₂ →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) [] →
    HasType (.lit (.entityUID uid₂)) c ⟨ets, acts, reqty⟩ (.entity uid₂.ty) [] →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂))) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### Binary: mem — action literal in set of entity literals (tt if any descendent) -/
  | binaryAppMemActionLitSetTt :
    ∀ uid₁ xs c ets acts reqty ety₂,
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts →
    ActionInSet acts uid₁ xs →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) [] →
    HasType (.set xs) c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) [] →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.set xs)) c ⟨ets, acts, reqty⟩ (.bool .tt) []
  /- ### Binary: mem — action literal in set of entity literals (ff if no descendent) -/
  | binaryAppMemActionLitSetFf :
    ∀ uid₁ xs c ets acts reqty ety₂,
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts →
    ¬ ActionInSet acts uid₁ xs →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) [] →
    HasType (.set xs) c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) [] →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.set xs)) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### hasAttr — record (attribute found) -/
  -- `id rty`: keep `rty` check-only here so it is produced by the record-type
  -- inference `HasType x₁ (.record rty)` (bounded), not enumerated by
  -- `HasAttrInRecord` over all record types (unbounded). Same rationale as the
  -- entity attr rules below.
  | hasAttrRecord :
    ∀ x₁ a c env rty ty caps,
    HasType x₁ c env (.record rty) [] →
    HasAttrInRecord rty x₁ a c true ty caps →
    HasType (.hasAttr x₁ a) c env ty caps

  /- ### hasAttr — record (attribute not found) -/
  | hasAttrRecordNotFound :
    ∀ x₁ a c env rty,
    HasType x₁ c env (.record (.mk rty)) [] →
    MapNotContainsKey a (.mk rty) →
    HasType (.hasAttr x₁ a) c env (.bool .ff) []

  /- ### hasAttr — entity (attribute found) -/
  -- `id rty`: keep `rty` check-only in `HasAttrInRecord` so Specimen must obtain
  -- it from `MapContainsAttrs` (a finite walk of the schema `ets`). Without this,
  -- the checker/enumerator draws `rty` from `HasAttrInRecord` — an *unbounded*
  -- enumeration over record types — and diverges. Cf. the `id` trick in `getTag`.
  | hasAttrEntity :
    ∀ x₁ a c ets acts reqty ety ty caps rty,
    MapContainsAttrs ety rty ets →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    HasAttrInRecord rty x₁ a c false ty caps →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ ty caps

  /- ### hasAttr — entity (attribute not found) -/
  | hasAttrEntityNotFound :
    ∀ x₁ a c ets acts reqty ety rty,
    MapContainsAttrs ety rty ets →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    MapNotContainsKey a rty →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### getAttr — record -/
  -- `id rty`: produce `rty` from the record-type inference `HasType x₁ (.record
  -- rty)` (bounded), not by enumerating it inside `GetAttrInRecord` over all
  -- record types (which diverges). Same rationale as `getAttrEntity`.
  | getAttrRecord :
    ∀ x₁ a c env rty ty,
    HasType x₁ c env (.record rty) [] →
    GetAttrInRecord rty x₁ a c ty →
    HasType (.getAttr x₁ a) c env ty []

  /- ### getAttr — entity -/
  -- `id rty`: force `rty` to come from `MapContainsAttrs` (a finite walk of the
  -- schema `ets`) rather than from `GetAttrInRecord` (which would enumerate record
  -- types via `Enum Map`). Combined with dropping `GetAttrInRecord`'s phantom
  -- receiver type, this keeps the checker fully bounded.
  | getAttrEntity :
    ∀ x₁ a c ets acts reqty ety ty rty,
    MapContainsAttrs ety rty ets →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    GetAttrInRecord rty x₁ a c ty →
    HasType (.getAttr x₁ a) c ⟨ets, acts, reqty⟩ ty []

  /- ### hasTag — entity has tags, not in capabilities -/
  | hasTagAnyBool :
    ∀ x₁ x₂ c ets acts reqty ety ty,
    HasTagSchema ets ety ty →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ .string [] →
    HasType (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) [(x₁, .tag x₂)]

  /- ### hasTag — entity has tags, already in capabilities -/
  | hasTagTt :
    ∀ x₁ x₂ c ets acts reqty ety ty,
    -- `id x₁`/`id x₂`: keep both typechecks as *checks* so Specimen can't produce
    -- either operand here (it won't output from under a function), forcing
    -- `CapTagMem` to produce *both* the entity and the key from `c`.
    CapTagMem x₁ x₂ c →
    HasTagSchema ets ety ty →
    HasType (id x₁) c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    HasType (id x₂) c ⟨ets, acts, reqty⟩ .string [] →
    HasType (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .tt) []

  /- ### hasTag — entity has no tags -/
  | hasTagFf :
    ∀ x₁ x₂ c ets acts reqty ety,
    NoTags ets ety →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    HasType x₂ c ⟨ets, acts, reqty⟩ .string [] →
    HasType (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### getTag — entity with tags, capability present -/
  | getTag :
    ∀ x₁ x₂ c ets acts reqty ety ty,
    -- `id x₁`/`id x₂`: force `CapTagMem` to produce *both* operands from `c`.
    -- Without `id x₁`, the scheduler produces `x₁` via `HasType … (.entity ety)`
    -- (ety is fixed by the requested `ty`), demoting `CapTagMem` to a check and
    -- leaving the id-wrapped `x₂` with no producer — so getTag never generates.
    CapTagMem x₁ x₂ c →
    HasTagSchema ets ety ty →
    HasType (id x₁) c ⟨ets, acts, reqty⟩ (.entity ety) [] →
    HasType (id x₂) c ⟨ets, acts, reqty⟩ .string [] →
    HasType (.binaryApp .getTag x₁ x₂) c ⟨ets, acts, reqty⟩ ty []

  /- ### ite — condition true -/
  | iteTt :
    ∀ x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ t₃ cout,
    HasType x₁ c env (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env t₂ c₂ →
    HasType x₃ c env t₃ [] →
    CapMerge c₁ c₂ cout →
    HasType (.ite x₁ x₂ x₃) c env t₂ cout

  /- ### ite — condition false -/
  | iteFf :
    ∀ x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ t₃ c₃,
    HasType x₁ c env (.bool .ff) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env t₂ c₂ →
    HasType x₃ c env t₃ c₃ →
    HasType (.ite x₁ x₂ x₃) c env t₃ c₃

  /- ### ite — condition anyBool -/
  | iteAnyBool :
    ∀ x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ t₃ c₃ lubTy c₁₂,
    HasType x₁ c env (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env t₂ c₂ →
    HasType x₃ c env t₃ c₃ →
    Lub t₂ t₃ lubTy →
    CapMerge c₁ c₂ c₁₂ →
    HasType (.ite x₁ x₂ x₃) c env lubTy (capIntersect c₁₂ c₃)

  /- ### and — short-circuit -/
  | andShort :
    ∀ x₁ x₂ c env c₁,
    HasType x₁ c env (.bool .ff) c₁ →
    HasType (.and x₁ x₂) c env (.bool .ff) []

  /- ### and — tt then ff -/
  | andTtFf :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂,
    HasType x₁ c env (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env (.bool .ff) c₂ →
    HasType (.and x₁ x₂) c env (.bool .ff) []

  /- ### and — tt then tt -/
  | andTtTt :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂ cout,
    HasType x₁ c env (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env (.bool .tt) c₂ →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c env (.bool .tt) cout

  /- ### and — tt then anyBool -/
  | andTtAny :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂ cout,
    HasType x₁ c env (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env (.bool .anyBool) c₂ →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c env (.bool .anyBool) cout

  /- ### and — anyBool then ff -/
  | andAnyFf :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂,
    HasType x₁ c env (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env (.bool .ff) c₂ →
    HasType (.and x₁ x₂) c env (.bool .ff) []

  /- ### and — anyBool then tt -/
  | andAnyTt :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂ cout,
    HasType x₁ c env (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env (.bool .tt) c₂ →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c env (.bool .anyBool) cout

  /- ### and — anyBool then anyBool -/
  | andAnyAny :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂ cout,
    HasType x₁ c env (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env (.bool .anyBool) c₂ →
    CapMerge c₁ c₂ cout →
    HasType (.and x₁ x₂) c env (.bool .anyBool) cout

  /- ### or — short-circuit -/
  | orShort :
    ∀ x₁ x₂ c env c₁,
    HasType x₁ c env (.bool .tt) c₁ →
    HasType (.or x₁ x₂) c env (.bool .tt) []

  /- ### or — ff then b₂ -/
  | orFfThen :
    ∀ x₁ x₂ c env c₁ b₂ c₂,
    HasType x₁ c env (.bool .ff) c₁ →
    HasType x₂ c env (.bool b₂) c₂ →
    HasType (.or x₁ x₂) c env (.bool b₂) c₂

  /- ### or — anyBool then tt -/
  | orAnyTt :
    ∀ x₁ x₂ c env c₁ c₂,
    HasType x₁ c env (.bool .anyBool) c₁ →
    HasType x₂ c env (.bool .tt) c₂ →
    HasType (.or x₁ x₂) c env (.bool .tt) []

  /- ### or — anyBool then ff -/
  | orAnyFf :
    ∀ x₁ x₂ c env c₁ c₂,
    HasType x₁ c env (.bool .anyBool) c₁ →
    HasType x₂ c env (.bool .ff) c₂ →
    HasType (.or x₁ x₂) c env (.bool .anyBool) c₁

  /- ### or — anyBool then anyBool -/
  | orAnyAny :
    ∀ x₁ x₂ c env c₁ c₂,
    HasType x₁ c env (.bool .anyBool) c₁ →
    HasType x₂ c env (.bool .anyBool) c₂ →
    HasType (.or x₁ x₂) c env (.bool .anyBool) (capIntersect c₁ c₂)

  /- ### Set literal -/
  | set :
    ∀ x xs c env ty tyList lubTy,
    HasType x c env ty [] →
    HasTypeList xs c env tyList →
    AllLub ty tyList lubTy →
    HasType (.set (x :: xs)) c env (.set lubTy) []

  /- ### Record literal -/
  | record :
    ∀ axs c env atyList,
    HasTypeRecord axs c env atyList →
    HasType (.record axs) c env (.record (.mk atyList)) []

  /- ### Extension function call -/
  -- Delegates to `HasTypeExtCall` (a mutual relation, below), which states each
  -- function's argument types directly as `HasType` premises — no `HasTypeList`.
  | callExt : ∀ xfn args c env ty,
    HasTypeExtCall xfn args c env ty →
    HasType (.call xfn args) c env ty []

/-- Typing a list of expressions. -/
inductive HasTypeList : List Expr → Capabilities → TypeEnv → List CedarType → Prop where
  | nil :
    ∀ c env,
    HasTypeList [] c env []
  | cons :
    ∀ x xs c env ty tys,
    HasType x c env ty [] →
    HasTypeList xs c env tys →
    HasTypeList (x :: xs) c env (ty :: tys)

/-- Typing a record. -/
inductive HasTypeRecord : List (Attr × Expr) → Capabilities → TypeEnv → List (Attr × QualifiedType) → Prop where
  | nil :
    ∀ c env,
    HasTypeRecord [] c env []
  | cons :
    ∀ a x axs c env ty atyList,
    HasType x c env ty [] →
    HasTypeRecord axs c env atyList →
    HasTypeRecord ((a, x) :: axs) c env ((a, .required ty) :: atyList)

/-- Typing of extension-function calls. Mutual with `HasType`: each function's
    argument types are stated directly as `HasType` premises (construction takes a
    string literal via `ValidX`; methods take extension-typed args), so generating
    a method call recurses type-directed on each argument (nesting construction
    calls as needed) rather than routing an argument-type list through
    `HasTypeList`. -/
inductive HasTypeExtCall : ExtFun → List Expr → Capabilities → TypeEnv → CedarType → Prop where
  /- Construction: fn applied to a string literal. -/
  | decimal  : ∀ s c env, ValidDecimal s  → HasTypeExtCall .decimal [.lit (.string s)] c env (.ext .decimal)
  | ip       : ∀ s c env, ValidIP s       → HasTypeExtCall .ip [.lit (.string s)] c env (.ext .ipAddr)
  | datetime : ∀ s c env, ValidDatetime s → HasTypeExtCall .datetime [.lit (.string s)] c env (.ext .datetime)
  | duration : ∀ s c env, ValidDuration s → HasTypeExtCall .duration [.lit (.string s)] c env (.ext .duration)
  /- Methods: argument types stated directly as `HasType` premises. -/
  | lessThan : ∀ a b c env,
    HasType a c env (.ext .decimal) [] → HasType b c env (.ext .decimal) [] →
    HasTypeExtCall .lessThan [a, b] c env (.bool .anyBool)
  | lessThanOrEqual : ∀ a b c env,
    HasType a c env (.ext .decimal) [] → HasType b c env (.ext .decimal) [] →
    HasTypeExtCall .lessThanOrEqual [a, b] c env (.bool .anyBool)
  | greaterThan : ∀ a b c env,
    HasType a c env (.ext .decimal) [] → HasType b c env (.ext .decimal) [] →
    HasTypeExtCall .greaterThan [a, b] c env (.bool .anyBool)
  | greaterThanOrEqual : ∀ a b c env,
    HasType a c env (.ext .decimal) [] → HasType b c env (.ext .decimal) [] →
    HasTypeExtCall .greaterThanOrEqual [a, b] c env (.bool .anyBool)
  | isIpv4 : ∀ a c env,
    HasType a c env (.ext .ipAddr) [] →
    HasTypeExtCall .isIpv4 [a] c env (.bool .anyBool)
  | isIpv6 : ∀ a c env,
    HasType a c env (.ext .ipAddr) [] →
    HasTypeExtCall .isIpv6 [a] c env (.bool .anyBool)
  | isLoopback : ∀ a c env,
    HasType a c env (.ext .ipAddr) [] →
    HasTypeExtCall .isLoopback [a] c env (.bool .anyBool)
  | isMulticast : ∀ a c env,
    HasType a c env (.ext .ipAddr) [] →
    HasTypeExtCall .isMulticast [a] c env (.bool .anyBool)
  | isInRange : ∀ a b c env,
    HasType a c env (.ext .ipAddr) [] → HasType b c env (.ext .ipAddr) [] →
    HasTypeExtCall .isInRange [a, b] c env (.bool .anyBool)
  | offset : ∀ a b c env,
    HasType a c env (.ext .datetime) [] → HasType b c env (.ext .duration) [] →
    HasTypeExtCall .offset [a, b] c env (.ext .datetime)
  | durationSince : ∀ a b c env,
    HasType a c env (.ext .datetime) [] → HasType b c env (.ext .datetime) [] →
    HasTypeExtCall .durationSince [a, b] c env (.ext .duration)
  | toDate : ∀ a c env,
    HasType a c env (.ext .datetime) [] →
    HasTypeExtCall .toDate [a] c env (.ext .datetime)
  | toTime : ∀ a c env,
    HasType a c env (.ext .datetime) [] →
    HasTypeExtCall .toTime [a] c env (.ext .duration)
  | toMilliseconds : ∀ a c env,
    HasType a c env (.ext .duration) [] →
    HasTypeExtCall .toMilliseconds [a] c env .int
  | toSeconds : ∀ a c env,
    HasType a c env (.ext .duration) [] →
    HasTypeExtCall .toSeconds [a] c env .int
  | toMinutes : ∀ a c env,
    HasType a c env (.ext .duration) [] →
    HasTypeExtCall .toMinutes [a] c env .int
  | toHours : ∀ a c env,
    HasType a c env (.ext .duration) [] →
    HasTypeExtCall .toHours [a] c env .int
  | toDays : ∀ a c env,
    HasType a c env (.ext .duration) [] →
    HasTypeExtCall .toDays [a] c env .int

end

end CedarGen.Relational.Lean

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

namespace Cedar.Validation.Relational

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

inductive MapContainsEnum : EntityType → Set String → EntitySchema → Prop where
  | here : ∀ ety eids rest,
    MapContainsEnum ety eids (.mk ((ety, .enum eids) :: rest))
  | there : ∀ ety eids k' v' rest,
    k' ≠ ety →
    MapContainsEnum ety eids (.mk rest) →
    MapContainsEnum ety eids (.mk ((k', v') :: rest))

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
  -- An enum entity type has no ancestors, so it descends from nothing but itself.
  | enum : ∀ ets acts ety₁ ety₂ eids,
    ety₁ ≠ ety₂ →
    MapContainsEnum ety₁ eids ets →
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
  -- An enum entity type carries no tags (`tags?` returns the empty tag set).
  | enum : ∀ ets ety eids,
    MapContainsEnum ety eids ets →
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

/- ## Predicates -/

inductive BothLit : Expr → Expr → Prop where
  | mk : ∀ p₁ p₂, BothLit (.lit p₁) (.lit p₂)

/-- x₁ is an action-schema literal AND x₂ is an entity literal.
    When both hold, the functional uses action-hierarchy logic for `mem`. -/
inductive IsActionLitMem : Expr → Expr → ActionSchema → Prop where
  | mk : ∀ uid₁ uid₂ acts entry,
    MapContains uid₁ entry acts →
    IsActionLitMem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂)) acts

/-- x₁ is an action-schema literal AND x₂ is a set of entity-UID literals.
    When both hold, the functional uses action-hierarchy logic for set `mem`. -/
inductive IsActionLitMemSet : Expr → Expr → ActionSchema → Prop where
  | mk : ∀ uid₁ xs acts entry,
    MapContains uid₁ entry acts →
    (∀ x, x ∈ xs → ∃ uid, x = .lit (.entityUID uid)) →
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts

/- ## Record-key ordering bound

`KeyAbove lb a` holds when `a` strictly exceeds the lower bound `lb`
(`none` acts as −∞). Threaded through `HasTypeRecord` so each successive
record key strictly exceeds the previous one, making the accumulated
attribute list strictly sorted by key — i.e. sorted *and* duplicate-free,
hence already canonical: `.mk atyList = Map.make atyList`. The comparison is
`<` on `Attr = String` (lexicographic by codepoint, `String.strictLT`). -/
inductive KeyAbove : Option Attr → Attr → Prop where
  | none : ∀ a, KeyAbove none a
  | some : ∀ b a, b < a → KeyAbove (some b) a

/- Producer for a key strictly above `b`: a proper extension `b ++ suffix` is
   lexicographically greater than `b` (`b` is a strict prefix), so `b < a`
   holds for any nonempty suffix. Lets Specimen *generate* ascending record
   keys (synthesis mode), not just check them. -/
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
    HasType x₁ c env (.bool .tt) oc1 →
    HasType (.unaryApp .not x₁) c env (.bool .ff) []
  | unaryAppNotFf :
    ∀ x₁ c env,
    HasType x₁ c env (.bool .ff) oc2 →
    HasType (.unaryApp .not x₁) c env (.bool .tt) []
  | unaryAppNotAny :
    ∀ x₁ c env,
    HasType x₁ c env (.bool .anyBool) oc3 →
    HasType (.unaryApp .not x₁) c env (.bool .anyBool) []

  /- ### Unary: neg -/
  | unaryAppNeg :
    ∀ x₁ c env,
    HasType x₁ c env .int oc4 →
    HasType (.unaryApp .neg x₁) c env .int []

  /- ### Unary: isEmpty -/
  | unaryAppIsEmpty :
    ∀ x₁ c env elemTy,
    HasType x₁ c env (.set elemTy) oc5 →
    HasType (.unaryApp .isEmpty x₁) c env (.bool .anyBool) []

  /- ### Unary: like -/
  | unaryAppLike :
    ∀ pat x₁ c env,
    HasType x₁ c env .string oc6 →
    HasType (.unaryApp (.like pat) x₁) c env (.bool .anyBool) []

  /- ### Unary: is (true) -/
  | unaryAppIsTrue :
    ∀ ety x₁ c env,
    ValidEntityType ety env.ets env.acts →
    HasType x₁ c env (.entity ety) oc7 →
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
    HasType x₁ c env (.entity ety₂) oc8 →
    HasType (.unaryApp (.is ety₁) x₁) c env (.bool .ff) []

  /- ### Binary: eq on literals -/
  | binaryAppEqLitSame :
    ∀ p c env ty,
    HasType (.lit p) c env ty oc9 →
    HasType (.binaryApp .eq (.lit p) (.lit p)) c env (.bool .tt) []
  | binaryAppEqLitDiff :
    ∀ p₁ p₂ c env ty₁ ty₂,
    PrimNeq p₁ p₂ →
    HasType (.lit p₁) c env ty₁ oc10 →
    HasType (.lit p₂) c env ty₂ oc11 →
    HasType (.binaryApp .eq (.lit p₁) (.lit p₂)) c env (.bool .ff) []

  /- ### Binary: eq non-literal (lub exists) -/
  | binaryAppEqNonLitLub :
    ∀ x₁ x₂ c env t₁ t₂ lubTy,
    Lub t₁ t₂ lubTy →
    HasType x₁ c env t₁ oc12 →
    HasType x₂ c env t₂ oc13 →
    ¬ BothLit x₁ x₂ →
    HasType (.binaryApp .eq x₁ x₂) c env (.bool .anyBool) []

  /- ### Binary: eq entity-entity different -/
  | binaryAppEqEntityDiff :
    ∀ x₁ x₂ c env ety₁ ety₂,
    ValidEntityType ety₁ env.ets env.acts →
    ValidEntityType ety₂ env.ets env.acts →
    ety₁ ≠ ety₂ →
    HasType x₁ c env (.entity ety₁) oc14 →
    HasType x₂ c env (.entity ety₂) oc15 →
    ¬ BothLit x₁ x₂ →
    HasType (.binaryApp .eq x₁ x₂) c env (.bool .ff) []

  /- ### Binary: arithmetic -/
  | binaryAppLessInt :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int oc16 →
    HasType x₂ c env .int oc17 →
    HasType (.binaryApp .less x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessDatetime :
    ∀ x₁ x₂ c env,
    HasType x₁ c env (.ext .datetime) oc18 →
    HasType x₂ c env (.ext .datetime) oc19 →
    HasType (.binaryApp .less x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessDuration :
    ∀ x₁ x₂ c env,
    HasType x₁ c env (.ext .duration) oc20 →
    HasType x₂ c env (.ext .duration) oc21 →
    HasType (.binaryApp .less x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessEqInt :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int oc22 →
    HasType x₂ c env .int oc23 →
    HasType (.binaryApp .lessEq x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessEqDatetime :
    ∀ x₁ x₂ c env,
    HasType x₁ c env (.ext .datetime) oc24 →
    HasType x₂ c env (.ext .datetime) oc25 →
    HasType (.binaryApp .lessEq x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessEqDuration :
    ∀ x₁ x₂ c env,
    HasType x₁ c env (.ext .duration) oc26 →
    HasType x₂ c env (.ext .duration) oc27 →
    HasType (.binaryApp .lessEq x₁ x₂) c env (.bool .anyBool) []
  | binaryAppAdd :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int oc28 →
    HasType x₂ c env .int oc29 →
    HasType (.binaryApp .add x₁ x₂) c env .int []
  | binaryAppSub :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int oc30 →
    HasType x₂ c env .int oc31 →
    HasType (.binaryApp .sub x₁ x₂) c env .int []
  | binaryAppMul :
    ∀ x₁ x₂ c env,
    HasType x₁ c env .int oc32 →
    HasType x₂ c env .int oc33 →
    HasType (.binaryApp .mul x₁ x₂) c env .int []

  /- ### Binary: set operations -/
  | binaryAppContains :
    ∀ x₁ x₂ c env t₂ elemTy,
    LubCompat t₂ elemTy →
    HasType x₁ c env (.set elemTy) oc34 →
    HasType x₂ c env t₂ oc35 →
    HasType (.binaryApp .contains x₁ x₂) c env (.bool .anyBool) []
  | binaryAppContainsAll :
    ∀ x₁ x₂ c env elemTy₁ elemTy₂,
    LubCompat elemTy₁ elemTy₂ →
    HasType x₁ c env (.set elemTy₁) oc36 →
    HasType x₂ c env (.set elemTy₂) oc37 →
    HasType (.binaryApp .containsAll x₁ x₂) c env (.bool .anyBool) []
  | binaryAppContainsAny :
    ∀ x₁ x₂ c env elemTy₁ elemTy₂,
    LubCompat elemTy₁ elemTy₂ →
    HasType x₁ c env (.set elemTy₁) oc38 →
    HasType x₂ c env (.set elemTy₂) oc39 →
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
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc40 →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.entity ety₂) oc41 →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []
  | binaryAppMemEntitySame :
    ∀ x₁ x₂ c ets acts reqty ety,
    ValidEntityType ety ets acts →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc42 →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.entity ety) oc43 →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []
  | binaryAppMemEntitySet :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    DescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc44 →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc45 →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []
  | binaryAppMemEntitySetSame :
    ∀ x₁ x₂ c ets acts reqty ety,
    ValidEntityType ety ets acts →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc46 →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety)) oc47 →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []

  /- ### Binary: mem — false (not descendent, excludes action-literal cases) -/
  | binaryAppMemEntityEntityFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    ValidEntityType ety₂ ets acts →
    NotDescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc48 →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.entity ety₂) oc49 →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []
  | binaryAppMemEntitySetFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    ValidEntityType ety₂ ets acts →
    NotDescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc50 →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc51 →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### Binary: mem — false (action-typed operand, non-literal) -/
  -- An action-typed operand `ety₁` (all action UIDs have the reserved `Action` type) can
  -- only descend from another action type; comparing it to a *different* type `ety₂` is
  -- always `.ff` (`typeOfInₑ`/`typeOfInₛ` take the `maybeDescendentOf` fallback, which is
  -- false since action ancestors are `Action`-typed). `NotDescendentOf` can't witness this
  -- (it walks standard `ets` entries), so these are separate rules; soundness uses the
  -- `WfActionSchema` invariant that action ancestors are `Action`-typed.
  | binaryAppMemActionEntityFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    MapNotContainsKey ety₁ ets →
    ety₁ ≠ ety₂ →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc103 →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.entity ety₂) oc104 →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []
  | binaryAppMemActionSetFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    MapNotContainsKey ety₁ ets →
    ety₁ ≠ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc105 →
    HasType x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc106 →
    HasType (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### Binary: mem — true (known action literal hierarchy) -/
  | binaryAppMemActionLitTt :
    ∀ uid₁ uid₂ c ets acts reqty,
    ActionDescendentOf acts uid₁ uid₂ →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) oc52 →
    HasType (.lit (.entityUID uid₂)) c ⟨ets, acts, reqty⟩ (.entity uid₂.ty) oc53 →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂))) c ⟨ets, acts, reqty⟩ (.bool .tt) []
  | binaryAppMemActionLitFf :
    ∀ uid₁ uid₂ c ets acts reqty,
    NotActionDescendentOf acts uid₁ uid₂ →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) oc54 →
    HasType (.lit (.entityUID uid₂)) c ⟨ets, acts, reqty⟩ (.entity uid₂.ty) oc55 →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂))) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### Binary: mem — action literal in set of entity literals (tt if any descendent) -/
  | binaryAppMemActionLitSetTt :
    ∀ uid₁ xs c ets acts reqty ety₂,
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts →
    ActionInSet acts uid₁ xs →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) oc56 →
    HasType (.set xs) c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc57 →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.set xs)) c ⟨ets, acts, reqty⟩ (.bool .tt) []
  /- ### Binary: mem — action literal in set of entity literals (ff if no descendent) -/
  | binaryAppMemActionLitSetFf :
    ∀ uid₁ xs c ets acts reqty ety₂,
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts →
    ¬ ActionInSet acts uid₁ xs →
    HasType (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) oc58 →
    HasType (.set xs) c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc59 →
    HasType (.binaryApp .mem (.lit (.entityUID uid₁)) (.set xs)) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### hasAttr — record (attribute found) -/
  -- `id rty`: keep `rty` check-only here so it is produced by the record-type
  -- inference `HasType x₁ (.record rty)` (bounded), not enumerated by
  -- `HasAttrInRecord` over all record types (unbounded). Same rationale as the
  -- entity attr rules below.
  | hasAttrRecord :
    ∀ x₁ a c env rty ty caps,
    HasType x₁ c env (.record rty) oc60 →
    HasAttrInRecord rty x₁ a c true ty caps →
    HasType (.hasAttr x₁ a) c env ty caps

  /- ### hasAttr — record (attribute not found) -/
  | hasAttrRecordNotFound :
    ∀ x₁ a c env rty,
    HasType x₁ c env (.record (.mk rty)) oc61 →
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
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc62 →
    HasAttrInRecord rty x₁ a c false ty caps →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ ty caps

  /- ### hasAttr — entity (attribute not found) -/
  | hasAttrEntityNotFound :
    ∀ x₁ a c ets acts reqty ety rty,
    MapContainsAttrs ety rty ets →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc63 →
    MapNotContainsKey a rty →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### hasAttr — enum entity (no attributes) -/
  -- An enum entity type carries no attributes: `EntitySchema.attrs?` returns the
  -- empty record for it, so `hasAttr` on an enum-typed operand types as `.bool .ff`.
  -- Mirrors `typeOfHasAttr`'s enum path (`attrs? ety = some Map.empty` →
  -- `hasAttrInRecord` finds nothing → `.bool .ff`). Uses `MapContains … (.enum …)`
  -- (the enum entry) rather than `MapContainsAttrs` (which matches only standard
  -- entries), so enum-typed operands get a derivation. `MapContainsEnum` extracts
  -- the enum entry as a top-level output (Specimen-friendly), like the other
  -- `MapContains…` field projectors.
  | hasAttrEnum :
    ∀ x₁ a c ets acts reqty ety eids,
    MapContainsEnum ety eids ets →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc64 →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### hasAttr — action-typed entity (no attributes) -/
  -- An action type is absent from `ets`, so `typeOfHasAttr` takes its `actionType?` branch:
  -- `hasAttr` on an action-typed operand is `.bool .ff` (action attributes not allowed).
  | hasAttrActionFf :
    ∀ x₁ a c ets acts reqty ety eid entry,
    MapNotContainsKey ety ets →
    MapContainsPairKey ety eid entry acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc109 →
    HasType (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### getAttr — record -/
  -- `id rty`: produce `rty` from the record-type inference `HasType x₁ (.record
  -- rty)` (bounded), not by enumerating it inside `GetAttrInRecord` over all
  -- record types (which diverges). Same rationale as `getAttrEntity`.
  | getAttrRecord :
    ∀ x₁ a c env rty ty,
    HasType x₁ c env (.record rty) oc65 →
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
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc66 →
    GetAttrInRecord rty x₁ a c ty →
    HasType (.getAttr x₁ a) c ⟨ets, acts, reqty⟩ ty []

  /- ### hasTag — entity has tags, not in capabilities -/
  -- `¬ CapTagMem`: `typeOfHasTag` returns `.tt` (with `[]`) when `(x₁, .tag x₂) ∈ c`,
  -- so the `anyBool` + new-capability branch fires only when the cap is absent.
  -- Mirrors the `¬ CapAttrMem` guard on `HasAttrInRecord.found_not_known`; without
  -- it the relation is unsound (derives `anyBool` where the functional gives `tt`).
  | hasTagAnyBool :
    ∀ x₁ x₂ c ets acts reqty ety ty,
    HasTagSchema ets ety ty →
    ¬ CapTagMem x₁ x₂ c →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc67 →
    HasType x₂ c ⟨ets, acts, reqty⟩ .string oc68 →
    HasType (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) [(x₁, .tag x₂)]

  /- ### hasTag — entity has tags, already in capabilities -/
  | hasTagTt :
    ∀ x₁ x₂ c ets acts reqty ety ty,
    -- `id x₁`/`id x₂`: keep both typechecks as *checks* so Specimen can't produce
    -- either operand here (it won't output from under a function), forcing
    -- `CapTagMem` to produce *both* the entity and the key from `c`.
    CapTagMem x₁ x₂ c →
    HasTagSchema ets ety ty →
    HasType (id x₁) c ⟨ets, acts, reqty⟩ (.entity ety) oc69 →
    HasType (id x₂) c ⟨ets, acts, reqty⟩ .string oc70 →
    HasType (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .tt) []

  /- ### hasTag — entity has no tags -/
  | hasTagFf :
    ∀ x₁ x₂ c ets acts reqty ety,
    NoTags ets ety →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc71 →
    HasType x₂ c ⟨ets, acts, reqty⟩ .string oc72 →
    HasType (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### hasTag — action-typed entity (no tags) -/
  -- An action type is absent from `ets`, so `typeOfHasTag` takes its `actionType?` branch:
  -- `hasTag` on an action-typed operand is `.bool .ff` (action tags not allowed).
  | hasTagActionFf :
    ∀ x₁ x₂ c ets acts reqty ety eid entry,
    MapNotContainsKey ety ets →
    MapContainsPairKey ety eid entry acts →
    HasType x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc107 →
    HasType x₂ c ⟨ets, acts, reqty⟩ .string oc108 →
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
    HasType (id x₁) c ⟨ets, acts, reqty⟩ (.entity ety) oc73 →
    HasType (id x₂) c ⟨ets, acts, reqty⟩ .string oc74 →
    HasType (.binaryApp .getTag x₁ x₂) c ⟨ets, acts, reqty⟩ ty []

  /- ### ite — condition true (untaken branch `x₃` is arbitrary: `typeOf` ignores it) -/
  | iteTt :
    ∀ x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ cout,
    HasType x₁ c env (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType x₂ c_c₁ env t₂ c₂ →
    CapMerge c₁ c₂ cout →
    HasType (.ite x₁ x₂ x₃) c env t₂ cout

  /- ### ite — condition false (untaken branch `x₂` is arbitrary: `typeOf` ignores it) -/
  | iteFf :
    ∀ x₁ x₂ x₃ c env c₁ t₃ c₃,
    HasType x₁ c env (.bool .ff) c₁ →
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
    HasType x c env ty oc75 →
    HasTypeList xs c env tyList →
    AllLub ty tyList lubTy →
    HasType (.set (x :: xs)) c env (.set lubTy) []

  /- ### Record literal -/
  | record :
    ∀ axs c env atyList,
    HasTypeRecord none axs c env atyList →
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
    HasType x c env ty oc76 →
    HasTypeList xs c env tys →
    HasTypeList (x :: xs) c env (ty :: tys)

/-- Typing a record. The `Option Attr` argument is a strict lower bound on the
    key of the head entry (`none` = −∞): each key must exceed the previous one
    (`KeyAbove lb a`), so the accumulated `atyList` is strictly sorted by key —
    sorted and duplicate-free, i.e. already canonical. -/
inductive HasTypeRecord : Option Attr → List (Attr × Expr) → Capabilities → TypeEnv → List (Attr × QualifiedType) → Prop where
  | nil :
    ∀ lb c env,
    HasTypeRecord lb [] c env []
  | cons :
    ∀ lb a x axs c env ty atyList,
    KeyAbove lb a →
    HasType x c env ty oc77 →
    HasTypeRecord (some a) axs c env atyList →
    HasTypeRecord lb ((a, x) :: axs) c env ((a, .required ty) :: atyList)

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
    HasType a c env (.ext .decimal) oc96 → HasType b c env (.ext .decimal) oc78 →
    HasTypeExtCall .lessThan [a, b] c env (.bool .anyBool)
  | lessThanOrEqual : ∀ a b c env,
    HasType a c env (.ext .decimal) oc97 → HasType b c env (.ext .decimal) oc79 →
    HasTypeExtCall .lessThanOrEqual [a, b] c env (.bool .anyBool)
  | greaterThan : ∀ a b c env,
    HasType a c env (.ext .decimal) oc98 → HasType b c env (.ext .decimal) oc80 →
    HasTypeExtCall .greaterThan [a, b] c env (.bool .anyBool)
  | greaterThanOrEqual : ∀ a b c env,
    HasType a c env (.ext .decimal) oc99 → HasType b c env (.ext .decimal) oc81 →
    HasTypeExtCall .greaterThanOrEqual [a, b] c env (.bool .anyBool)
  | isIpv4 : ∀ a c env,
    HasType a c env (.ext .ipAddr) oc82 →
    HasTypeExtCall .isIpv4 [a] c env (.bool .anyBool)
  | isIpv6 : ∀ a c env,
    HasType a c env (.ext .ipAddr) oc83 →
    HasTypeExtCall .isIpv6 [a] c env (.bool .anyBool)
  | isLoopback : ∀ a c env,
    HasType a c env (.ext .ipAddr) oc84 →
    HasTypeExtCall .isLoopback [a] c env (.bool .anyBool)
  | isMulticast : ∀ a c env,
    HasType a c env (.ext .ipAddr) oc85 →
    HasTypeExtCall .isMulticast [a] c env (.bool .anyBool)
  | isInRange : ∀ a b c env,
    HasType a c env (.ext .ipAddr) oc100 → HasType b c env (.ext .ipAddr) oc86 →
    HasTypeExtCall .isInRange [a, b] c env (.bool .anyBool)
  | offset : ∀ a b c env,
    HasType a c env (.ext .datetime) oc101 → HasType b c env (.ext .duration) oc87 →
    HasTypeExtCall .offset [a, b] c env (.ext .datetime)
  | durationSince : ∀ a b c env,
    HasType a c env (.ext .datetime) oc102 → HasType b c env (.ext .datetime) oc88 →
    HasTypeExtCall .durationSince [a, b] c env (.ext .duration)
  | toDate : ∀ a c env,
    HasType a c env (.ext .datetime) oc89 →
    HasTypeExtCall .toDate [a] c env (.ext .datetime)
  | toTime : ∀ a c env,
    HasType a c env (.ext .datetime) oc90 →
    HasTypeExtCall .toTime [a] c env (.ext .duration)
  | toMilliseconds : ∀ a c env,
    HasType a c env (.ext .duration) oc91 →
    HasTypeExtCall .toMilliseconds [a] c env .int
  | toSeconds : ∀ a c env,
    HasType a c env (.ext .duration) oc92 →
    HasTypeExtCall .toSeconds [a] c env .int
  | toMinutes : ∀ a c env,
    HasType a c env (.ext .duration) oc93 →
    HasTypeExtCall .toMinutes [a] c env .int
  | toHours : ∀ a c env,
    HasType a c env (.ext .duration) oc94 →
    HasTypeExtCall .toHours [a] c env .int
  | toDays : ∀ a c env,
    HasType a c env (.ext .duration) oc95 →
    HasTypeExtCall .toDays [a] c env .int

end

end Cedar.Validation.Relational

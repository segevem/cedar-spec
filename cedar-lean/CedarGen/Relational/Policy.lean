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
import CedarGen.Relational.TypeOfLean

/-! # Relational specification of well-typed Cedar policies

Generates policies whose scope constraints are consistent with the TypeEnv's
request type. The Rust validator checks scope constraints against RBAC rules
without converting to expressions; this relation mirrors that structural check.

Key design decisions:
- Principal/resource scopes are consistent with `reqty.principal`/`reqty.resource`
- Action scope references `reqty.action` (or its ancestors)
- The condition body is left as an opaque `Expr` — typing happens separately via `HasType`
- No function calls or record field access: all structural, Specimen-friendly
-/

namespace CedarGen.Relational.Policy

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open CedarGen.Relational.Schema
open CedarGen.Relational.Lean

/-! ## String list membership (for enum entity eid validation) -/

inductive InStringList : List String → String → Prop where
  | here : ∀ s rest,
      InStringList (s :: rest) s
  | there : ∀ s s' rest,
      InStringList rest s →
      InStringList (s' :: rest) s

/-! ## Valid entity UID (structural traversal of entity schema)

An entity UID is valid when its type exists in the entity schema and:
- For standard entity types, any eid is valid
- For enum entity types, the eid must be a member of the enum set

This mirrors `EntitySchema.isValidEntityUID` and is needed by `checkEntities`.
-/

inductive IsValidEntityUID :
    List (EntityType × EntitySchemaEntry) → EntityUID → Prop where
  | standard : ∀ ety eid ancestors attrs tags rest,
      IsValidEntityUID
        ((ety, EntitySchemaEntry.standard (StandardSchemaEntry.mk (Set.mk ancestors) (Map.mk attrs) tags)) :: rest)
        ⟨ety, eid⟩
  | enum : ∀ ety eid eids rest,
      InStringList eids eid →
      IsValidEntityUID
        ((ety, EntitySchemaEntry.enum (Set.mk eids)) :: rest)
        ⟨ety, eid⟩
  | there : ∀ entry rest uid,
      IsValidEntityUID rest uid →
      IsValidEntityUID (entry :: rest) uid

/-! ## Valid action UID (structural traversal of action schema)

An action UID is valid when it exists as a key in the action schema.
This mirrors `ActionSchema.contains`.
-/

inductive IsValidActionUID :
    List (EntityUID × ActionSchemaEntry) → EntityUID → Prop where
  | here : ∀ uid entry rest,
      IsValidActionUID ((uid, entry) :: rest) uid
  | there : ∀ pair rest uid,
      IsValidActionUID rest uid →
      IsValidActionUID (pair :: rest) uid

/-! ## Ancestor membership (structural traversal of entity schema)

An entity type `ety` is a descendant-or-equal of `ancestor` when either they
are the same type, or `ancestor` appears in `ety`'s ancestors set in the schema.

This mirrors `TypeEnv.descendentOf`:
```
if ety₁ = ety₂ then true
else match env.ets.find? ety₁ with
  | .some entry => entry.ancestors.contains ety₂
  | .none       => ...
```
-/

inductive InAncestorList : List EntityType → EntityType → Prop where
  | here : ∀ anc rest,
      InAncestorList (anc :: rest) anc
  | there : ∀ anc anc' rest,
      InAncestorList rest anc →
      InAncestorList (anc' :: rest) anc

inductive DescendentOf :
    List (EntityType × EntitySchemaEntry) → EntityType → EntityType → Prop where
  | refl : ∀ entries ety,
      DescendentOf entries ety ety
  | here : ∀ ety ancestor ancestors attrs tags rest,
      InAncestorList ancestors ancestor →
      DescendentOf
        ((ety, EntitySchemaEntry.standard (StandardSchemaEntry.mk (Set.mk ancestors) (Map.mk attrs) tags)) :: rest)
        ety ancestor
  | there : ∀ ety ancestor entry rest,
      DescendentOf rest ety ancestor →
      DescendentOf (entry :: rest) ety ancestor

/-! ## Action ancestor membership (structural traversal of action schema)

Mirrors `ActionSchema.descendentOf`:
```
if uid₁ == uid₂ then true
else match as.find? uid₁ with
  | .some entry => entry.ancestors.contains uid₂
  | .none => false
```
-/

inductive InActionAncestorList : List EntityUID → EntityUID → Prop where
  | here : ∀ uid rest,
      InActionAncestorList (uid :: rest) uid
  | there : ∀ uid uid' rest,
      InActionAncestorList rest uid →
      InActionAncestorList (uid' :: rest) uid

inductive ActionDescendentOf :
    List (EntityUID × ActionSchemaEntry) → EntityUID → EntityUID → Prop where
  | refl : ∀ entries uid,
      ActionDescendentOf entries uid uid
  | here : ∀ uid ancestor principals resources ancestors context rest,
      InActionAncestorList ancestors ancestor →
      ActionDescendentOf
        ((uid, ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors) (Map.mk context)) :: rest)
        uid ancestor
  | there : ∀ uid ancestor entry rest,
      ActionDescendentOf rest uid ancestor →
      ActionDescendentOf (entry :: rest) uid ancestor

/-! ## Principal scope consistent with reqty.principal

For the scope expression not to type to `bool .ff`, we need:
- `any`: always ok
- `eq uid`: `uid.ty == reqty.principal` and uid is a valid entity UID (passes `checkEntities`)
- `mem uid`: principal type is a descendant-or-equal of `uid.ty` and uid is valid
- `is ety`: `ety == reqty.principal` (otherwise `is` gives `.ff`)
- `isMem ety uid`: `ety == reqty.principal` AND principal is descendant-or-equal of `uid.ty`

The validity check on UIDs mirrors what `checkEntities` does: every entity UID
literal in the policy expression must reference a known entity type with a valid eid.
-/

inductive WellTypedPrincipalScope :
    List (EntityType × EntitySchemaEntry) →
    List (EntityUID × ActionSchemaEntry) →
    EntityType → PrincipalScope → Prop where
  | any : ∀ entityEntries actionEntries pty,
      WellTypedPrincipalScope entityEntries actionEntries pty (.principalScope .any)
  | eq : ∀ entityEntries actionEntries pty eid,
      IsValidEntityUID entityEntries ⟨pty, eid⟩ →
      WellTypedPrincipalScope entityEntries actionEntries pty (.principalScope (.eq ⟨pty, eid⟩))
  | mem : ∀ entityEntries actionEntries pty targetTy eid,
      DescendentOf entityEntries pty targetTy →
      IsValidEntityUID entityEntries ⟨targetTy, eid⟩ →
      WellTypedPrincipalScope entityEntries actionEntries pty (.principalScope (.mem ⟨targetTy, eid⟩))
  | is : ∀ entityEntries actionEntries pty,
      WellTypedPrincipalScope entityEntries actionEntries pty (.principalScope (.is pty))
  | isMem : ∀ entityEntries actionEntries pty targetTy eid,
      DescendentOf entityEntries pty targetTy →
      IsValidEntityUID entityEntries ⟨targetTy, eid⟩ →
      WellTypedPrincipalScope entityEntries actionEntries pty (.principalScope (.isMem pty ⟨targetTy, eid⟩))

/-! ## Resource scope consistent with reqty.resource

Symmetric to principal scope.
-/

inductive WellTypedResourceScope :
    List (EntityType × EntitySchemaEntry) →
    List (EntityUID × ActionSchemaEntry) →
    EntityType → ResourceScope → Prop where
  | any : ∀ entityEntries actionEntries rty,
      WellTypedResourceScope entityEntries actionEntries rty (.resourceScope .any)
  | eq : ∀ entityEntries actionEntries rty eid,
      IsValidEntityUID entityEntries ⟨rty, eid⟩ →
      WellTypedResourceScope entityEntries actionEntries rty (.resourceScope (.eq ⟨rty, eid⟩))
  | mem : ∀ entityEntries actionEntries rty targetTy eid,
      DescendentOf entityEntries rty targetTy →
      IsValidEntityUID entityEntries ⟨targetTy, eid⟩ →
      WellTypedResourceScope entityEntries actionEntries rty (.resourceScope (.mem ⟨targetTy, eid⟩))
  | is : ∀ entityEntries actionEntries rty,
      WellTypedResourceScope entityEntries actionEntries rty (.resourceScope (.is rty))
  | isMem : ∀ entityEntries actionEntries rty targetTy eid,
      DescendentOf entityEntries rty targetTy →
      IsValidEntityUID entityEntries ⟨targetTy, eid⟩ →
      WellTypedResourceScope entityEntries actionEntries rty (.resourceScope (.isMem rty ⟨targetTy, eid⟩))

/-! ## Action scope consistent with reqty.action

After `substituteAction`, the action variable becomes a literal. So:
- `any`: always ok
- `eq uid`: `uid == reqty.action` (exact match for `.tt`; same-type for `.anyBool`)
- `mem uid`: `reqty.action` is a descendant of `uid` in the action schema
- `actionInAny uids`: `reqty.action` is a descendant of some uid in the list

For `eq`, we restrict to the exact action UID (which gives `.bool .tt` after
substituteAction). This is a safe subset — a different UID of the same action
type would typecheck to `.anyBool`, but generating the exact UID is simpler and
avoids the impossibility check across environments.

All action UIDs referenced in the scope must be valid (exist in the action schema)
per `checkEntities`.
-/

/-! Every UID in a list is a valid action UID (per `checkEntities`). Used to
constrain the tail of an `action in [..]` list once the matching ancestor is found. -/
inductive AllValidActionUIDs :
    List (EntityUID × ActionSchemaEntry) → List EntityUID → Prop where
  | nil : ∀ entries,
      AllValidActionUIDs entries []
  | cons : ∀ entries uid rest,
      IsValidActionUID entries uid →
      AllValidActionUIDs entries rest →
      AllValidActionUIDs entries (uid :: rest)

/-! The action (or an ancestor) appears in the uid list, and EVERY UID in the list
is a valid action UID (per `checkEntities`). Without the `AllValidActionUIDs` premise
on the `here` tail, the elements after the matching ancestor would be unconstrained —
the generator would fabricate arbitrary (invalid) action UIDs there, producing
scopes the Rust validator rejects. -/
inductive WellTypedActionInList :
    List (EntityUID × ActionSchemaEntry) → EntityUID → List EntityUID → Prop where
  | here : ∀ entries action target rest,
      ActionDescendentOf entries action target →
      IsValidActionUID entries target →
      AllValidActionUIDs entries rest →
      WellTypedActionInList entries action (target :: rest)
  | there : ∀ entries action uid rest,
      IsValidActionUID entries uid →
      WellTypedActionInList entries action rest →
      WellTypedActionInList entries action (uid :: rest)

inductive WellTypedActionScope :
    List (EntityUID × ActionSchemaEntry) → EntityUID → ActionScope → Prop where
  | any : ∀ entries action,
      WellTypedActionScope entries action (.actionScope .any)
  | eq : ∀ entries action,
      WellTypedActionScope entries action (.actionScope (.eq action))
  | mem : ∀ entries action target,
      ActionDescendentOf entries action target →
      IsValidActionUID entries target →
      WellTypedActionScope entries action (.actionScope (.mem target))
  | inAny : ∀ entries action uids,
      WellTypedActionInList entries action uids →
      WellTypedActionScope entries action (.actionInAny uids)

/-! ## Conditions: a list of `when`/`unless` clauses, each a well-typed boolean

The validator folds `principalScope && actionScope && resourceScope && conditions.toExpr`
and typechecks it from `∅` capabilities. `&&` threads capabilities left-to-right
(`typeOf x₂ (c ∪ c₁) env`) but never refines `env`, and every scope conjunct produces `∅`
capabilities (`==`/`in`/`is` all return via the `ok` helper whose caps default to `∅`), so
the condition list begins with exactly `∅` caps against the raw env.

`Conditions.toExpr [c₁,…,cₙ]` = `c₁.toExpr && (c₂.toExpr && (… && cₙ.toExpr))` where a
`when` clause contributes its body and an `unless` clause contributes `!body`. So we thread
capabilities exactly as the `&&` fold does:
- `when body`: the body is typechecked under the accumulated caps, producing `cout`; the
  next clause sees `caps ∪ cout`.
- `unless body`: the body is still typechecked under the accumulated caps (it must be a
  boolean for `!` to apply), but `!body` produces `∅` capabilities (`typeOfUnaryApp .not`
  returns via `ok`, and `.not` discards the operand's caps), so the next clause sees `caps`
  unchanged.

Reusing `HasType` for each body is what makes the derived generator produce genuinely
well-typed conditions (via the existing typechecker generator) rather than opaque `Expr`s. -/

inductive WellTypedConditions : TypeEnv → Capabilities → List Condition → Prop where
  | nil : ∀ env caps,
      WellTypedConditions env caps []
  | when : ∀ env caps body bty cout rest,
      -- `id bty`: suppress `HasType` as the producer of the bool subtype so Specimen
      -- sources `bty` from ambient `Arbitrary BoolType` FIRST, making `.bool bty` a
      -- ground input. That routes the premise to the fully type-directed `HasType`
      -- generator (type-as-input), ~10× faster per condition than the generate-any-
      -- term-then-reject-non-bool mode that results when `bty` is a type-index output.
      HasType body caps env (.bool (id bty)) cout →
      WellTypedConditions env (caps ∪ cout) rest →
      WellTypedConditions env caps (Condition.mk .when body :: rest)
  | unless : ∀ env caps body bty cout rest,
      HasType body caps env (.bool (id bty)) cout →
      WellTypedConditions env caps rest →
      WellTypedConditions env caps (Condition.mk .unless body :: rest)

/-! ## Complete well-typed policy

Given a TypeEnv, generate a policy with scope constraints consistent with the
request type. The condition body `Expr` is unconstrained here — its typing
against the TypeEnv is handled at composition time by the `HasType` relation.
-/

inductive WellTypedPolicy : TypeEnv → Policy → Prop where
  | mk : ∀ entityEntries actionEntries reqty
        pid effect principalScope actionScope resourceScope conditions,
      WellTypedPrincipalScope entityEntries actionEntries reqty.principal principalScope →
      WellTypedActionScope actionEntries reqty.action actionScope →
      WellTypedResourceScope entityEntries actionEntries reqty.resource resourceScope →
      WellTypedConditions (TypeEnv.mk (Map.mk entityEntries) (Map.mk actionEntries) reqty) ∅ conditions →
      WellTypedPolicy
        (TypeEnv.mk (Map.mk entityEntries) (Map.mk actionEntries) reqty)
        (Policy.mk pid effect principalScope actionScope resourceScope conditions)

end CedarGen.Relational.Policy

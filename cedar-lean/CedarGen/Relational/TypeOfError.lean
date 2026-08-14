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

import CedarGen.Relational.TypeOfLean

/- # Relational specification of Cedar VALIDATION errors (augments `HasType`)

`HasType` (`TypeOfLean.lean`) relates a *well-typed* expression to its type; it has no
error case. This file adds the complementary relation `ErrorExpr`, which relates an
*ill-typed* expression to the KIND of validation error it triggers, faithful to the Cedar
validator (`Cedar/Validation/Validator.lean`, i.e. `validate` /
`typecheckPolicyWithEnvironments`), NOT bare `typeOf`.

The validator layers four error sources over `typeOf`:
  1. `checkEntities` — an EAGER whole-tree pre-pass → `unknownEntity` for any undeclared
     entity literal or `is`-type (runs first, so it preempts every other error).
  2. `typeOf` — the short-circuit single-error typechecker.
  3. non-boolean result → `unexpectedType`.
  4. all-false under every environment → `impossiblePolicy`.

Because the DRT comparison of validation errors is *lossy* (`validationErrorToJson` keeps
only the error KIND string), `ErrorExpr` targets the kind, not the `TypeError` payload.

## Faithfulness discipline (Phase 1)
Each rule injects EXACTLY ONE defect built from ENV-INDEPENDENT constants over an otherwise
clean frame, so the reported error kind is unambiguous regardless of the validator's pass
ordering AND identical under every environment of the schema (the generated env never
short-circuits its own well-typed scope, and a constant defect can only yield its intended
kind or a benign `ok`/`ff` under other envs — never a different error kind). Phase 2/3 will
add nested type-mismatch propagation reusing the `HasType` generator. -/

namespace CedarGen.Relational.Lean

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- The kind of a Cedar validation error, mirroring `Validator.validationErrorToJson`
    (the lossy projection the DRT compares). `impossiblePolicy` is a policy-level kind. -/
inductive VErrKind where
  | unknownEntity
  | unexpectedType
  | attrNotFound
  | tagNotFound
  | lubErr
  | extensionErr
  | emptySetErr
  | incompatibleSetTypes
  | impossiblePolicy
deriving Repr, DecidableEq, Inhabited

/-- `ety` is NOT a declared entity type: it is neither a key of the entity schema `ets`
    nor the type of any action in `acts`. This is exactly the negation of `checkEntities`'
    guard for `is`-types (`ets.contains ety || acts.actionType? ety`); it also implies
    `¬ ets.isValidEntityUID ⟨ety, _⟩ ∧ ¬ acts.contains ⟨ety, _⟩`, the literal-case guard.
    The candidate `ety` is drawn from the ambient `Arbitrary EntityType`; this relation is
    a CHECK (`DecOpt`) that keeps only genuinely-undeclared names, so it is sound even
    though `Arbitrary` names can collide with the schema. -/
inductive EntityTypeUndeclared : EntityType → EntitySchema → ActionSchema → Prop where
  | mk : ∀ ety ets acts,
      ets.contains ety = false →
      acts.actionType? ety = false →
      EntityTypeUndeclared ety ets acts

instance : DecOpt (EntityTypeUndeclared ety ets acts) where
  decOpt _ := .ok (!ets.contains ety && !acts.actionType? ety)

/-- An env-independent, well-typed, NON-boolean constant expression. Used to trigger the
    validator's non-boolean-result / operand error → `unexpectedType`. Every inhabitant
    typechecks to a fixed non-`bool` type under any environment (no schema/`reqty` lookup),
    so the resulting policy is `unexpectedType` under every environment. -/
inductive NonBoolConst : Expr → Prop where
  | int    : ∀ i, NonBoolConst (.lit (.int i))
  | string : ∀ s, NonBoolConst (.lit (.string s))
  | setInt : ∀ i, NonBoolConst (.set [.lit (.int i)])

/-- Env-independent, well-typed, entity-clean CONSTANT expressions used as the inert siblings
    of a propagation rule (the sub-terms `typeOf` types successfully *before* reaching the
    erroring one). Their type is irrelevant to the propagated error, so any of these suffice. -/
inductive StableWt : Expr → Prop where
  | int    : ∀ i, StableWt (.lit (.int i))
  | string : ∀ s, StableWt (.lit (.string s))
  | boolT  : StableWt (.lit (.bool true))

/-- `ErrorExpr c env x k` : the LEAF `typeOf`/`checkEntities` errors — expressions that are
    genuinely rejected by `typeOf` (or the eager entity pass) with kind `k`, at the node itself.
    These are the ONLY errors that propagate through enclosing forced positions (see `TypeErr`);
    `impossiblePolicy` and the "well-typed non-boolean body" case are NOT leaves here — they are
    validator/policy-level and handled by `PolicyBodyErr`. Every leaf is env-independent, so its
    kind is identical under every environment of the schema. -/
inductive ErrorExpr : Capabilities → TypeEnv → Expr → VErrKind → Prop where
  /- ### unknownEntity — entity literal of an undeclared type (caught eagerly by `checkEntities`) -/
  | unknownEntityLit : ∀ c ets acts reqty ety eid,
      EntityTypeUndeclared ety ets acts →
      ErrorExpr c ⟨ets, acts, reqty⟩ (.lit (.entityUID ⟨ety, eid⟩)) .unknownEntity
  /- ### unknownEntity — `principal is <undeclared>` (caught eagerly by `checkEntities`) -/
  | unknownEntityIs : ∀ c ets acts reqty ety,
      EntityTypeUndeclared ety ets acts →
      ErrorExpr c ⟨ets, acts, reqty⟩ (.unaryApp (.is ety) (.var .principal)) .unknownEntity
  /- ### emptySetErr — the empty set literal has no element type -/
  | emptySet : ∀ c env,
      ErrorExpr c env (.set []) .emptySetErr
  /- ### attrNotFound — `{}.a` : get an absent attribute of the empty record. Env-independent. -/
  | attrNotFound : ∀ c env a,
      ErrorExpr c env (.getAttr (.record []) a) .attrNotFound
  /- ### tagNotFound — `Foo::"e".getTag("t")` on a *standard* entity of `ets` (valid literal,
     `tags? = some _`) with `c = ∅` (tag never in caps). `ets` shared ⇒ env-independent. -/
  | tagNotFound : ∀ c ets acts reqty ety eid rty s,
      MapContainsAttrs ety rty ets →
      ErrorExpr c ⟨ets, acts, reqty⟩
        (.binaryApp .getTag (.lit (.entityUID ⟨ety, eid⟩)) (.lit (.string s))) .tagNotFound
  /- ### lubErr — `[i] == "s"` : eq of set-of-int and string (no lub, not both entities). -/
  | lubErr : ∀ c env i s,
      ErrorExpr c env
        (.binaryApp .eq (.set [.lit (.int i)]) (.lit (.string s))) .lubErr
  /- ### incompatibleSetTypes — `[i, "s"]` : set literal whose element types have no lub. -/
  | incompatibleSetTypes : ∀ c env i s,
      ErrorExpr c env (.set [.lit (.int i), .lit (.string s)]) .incompatibleSetTypes
  /- ### extensionErr — `decimal(i)` : extension constructor applied to a non-string arg. -/
  | extensionErr : ∀ c env i,
      ErrorExpr c env (.call .decimal [.lit (.int i)]) .extensionErr
  /- ### unexpectedType — genuine operator/operand type errors (real `typeOf` errors, unlike a
     merely non-boolean body). `b + 0` with `b : bool`, and `!i` with `i : int`. Env-independent. -/
  | unexpectedAdd : ∀ c env i,
      ErrorExpr c env (.binaryApp .add (.lit (.bool true)) (.lit (.int i))) .unexpectedType
  | unexpectedNot : ∀ c env i,
      ErrorExpr c env (.unaryApp .not (.lit (.int i))) .unexpectedType

/-- `TypeErr c env x k` : `typeOf x c env` errors with kind `k`, reconstructed structurally
    from `typeOf`'s recursion. `leaf` injects an `ErrorExpr`; every other rule PROPAGATES a
    sub-term's error through a position `typeOf` forces (mirroring its short-circuit order and
    branch laziness), with the earlier-typed siblings supplied by env-stable `StableWt` constants
    / literal boolean guards. Correct by construction — no per-context preservation argument.
    Recursive ⇒ defects at arbitrary depth (bounded by Specimen's `size`); env-independent ⇒
    faithful under the full multi-environment `validate`. -/
inductive TypeErr : Capabilities → TypeEnv → Expr → VErrKind → Prop where
  | leaf : ∀ c env x k, ErrorExpr c env x k → TypeErr c env x k
  /- unaryApp forces its operand. The op is restricted to the entity-FREE unary ops: `.is ety`
     embeds a type that `checkEntities` would check (potentially flipping the kind to
     `unknownEntity`), so it is excluded. `.not`/`.neg`/`.isEmpty` carry no entity. -/
  | unaryNot     : ∀ c env x k, TypeErr c env x k → TypeErr c env (.unaryApp .not x) k
  | unaryNeg     : ∀ c env x k, TypeErr c env x k → TypeErr c env (.unaryApp .neg x) k
  | unaryIsEmpty : ∀ c env x k, TypeErr c env x k → TypeErr c env (.unaryApp .isEmpty x) k
  /- binaryApp types the left operand first (any op — no `BinaryOp` embeds an entity). The inert
     sibling is `StableWt` (entity-clean) so `checkEntities`' eager traversal can't flip the kind. -/
  | binL : ∀ c env op x₁ x₂ k, TypeErr c env x₁ k → StableWt x₂ → TypeErr c env (.binaryApp op x₁ x₂) k
  /- binaryApp: left ok (stable), then the right is forced. -/
  | binR : ∀ c env op x₁ x₂ k, StableWt x₁ → TypeErr c env x₂ k → TypeErr c env (.binaryApp op x₁ x₂) k
  /- `&&` / `||` type the guard first; the (untyped-but-traversed) rhs is kept `StableWt`. -/
  | andGuard : ∀ c env x₁ x₂ k, TypeErr c env x₁ k → StableWt x₂ → TypeErr c env (.and x₁ x₂) k
  | orGuard  : ∀ c env x₁ x₂ k, TypeErr c env x₁ k → StableWt x₂ → TypeErr c env (.or x₁ x₂) k
  /- `true && e` : guard `tt` forces the rhs. -/
  | andR : ∀ c env x₂ k, TypeErr c env x₂ k → TypeErr c env (.and (.lit (.bool true)) x₂) k
  /- `false || e` : guard `ff` forces the rhs. -/
  | orR : ∀ c env x₂ k, TypeErr c env x₂ k → TypeErr c env (.or (.lit (.bool false)) x₂) k
  /- `if e then s₂ else s₃` : the guard is forced first; both branches are inert `StableWt`. -/
  | iteGuard : ∀ c env x₁ s₂ s₃ k, TypeErr c env x₁ k → StableWt s₂ → StableWt s₃ → TypeErr c env (.ite x₁ s₂ s₃) k
  /- `if true then e else s₃` : guard `tt` forces the then-branch; the else-branch is inert. -/
  | iteThen : ∀ c env x₂ s₃ k, TypeErr c env x₂ k → StableWt s₃ → TypeErr c env (.ite (.lit (.bool true)) x₂ s₃) k
  /- `if false then s₂ else e` : guard `ff` forces the else-branch; the then-branch is inert. -/
  | iteElse : ∀ c env s₂ x₃ k, StableWt s₂ → TypeErr c env x₃ k → TypeErr c env (.ite (.lit (.bool false)) s₂ x₃) k
  /- getAttr / hasAttr force the receiver (`a : Attr` is a string, entity-free). -/
  | getAttr : ∀ c env x a k, TypeErr c env x k → TypeErr c env (.getAttr x a) k
  | hasAttr : ∀ c env x a k, TypeErr c env x k → TypeErr c env (.hasAttr x a) k
  /- a singleton set literal forces its sole element. -/
  | setSingleton : ∀ c env x k, TypeErr c env x k → TypeErr c env (.set [x]) k

/-- `PolicyBodyErr c env x k` : the body `x` makes the *policy* fail validation with kind `k`.
    It is either a genuine `typeOf` error (`TypeErr`, nested), or one of the two validator/
    policy-level properties that are NOT `typeOf` errors and so appear only at the top: a
    well-typed non-boolean body (→ `unexpectedType` at the enclosing `&&`/bool-check), or a body
    that is `false` under every environment (→ `impossiblePolicy`). -/
inductive PolicyBodyErr : Capabilities → TypeEnv → Expr → VErrKind → Prop where
  -- `k ≠ impossiblePolicy`: `TypeErr` never yields `impossiblePolicy` (it has no such leaf — that
  -- kind lives only at the top-level `impossible` base). The guard is logically vacuous for the
  -- SUCCESS relation, but in the TARGETED (`k`-as-input) generator mode it stops Specimen from
  -- fruitlessly searching the whole `TypeErr` recursion for an `impossiblePolicy` leaf when
  -- `k = impossiblePolicy` is requested — turning that request from a deep backtrack into an
  -- immediate hit on `impossible`.
  | typeErr    : ∀ c env x k, k ≠ .impossiblePolicy → TypeErr c env x k → PolicyBodyErr c env x k
  | nonBool    : ∀ c env x, NonBoolConst x → PolicyBodyErr c env x .unexpectedType
  | impossible : ∀ c env, PolicyBodyErr c env (.lit (.bool false)) .impossiblePolicy

end CedarGen.Relational.Lean

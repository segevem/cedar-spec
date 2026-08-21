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

import CedarGen.Relational.TypeOfLeanSound

/-! # Completeness of the relational typing spec

Converse of `hasType_sound`: on a well-formed environment, every *successful*
run of the functional typechecker `Cedar.Validation.typeOf` is witnessed by a
`HasType` derivation (up to `CapsEquiv` on the output capabilities).

Completeness holds only relative to `WfTypeEnv` and only for expressions whose
record literals are already canonical (strictly-sorted, duplicate-free keys) —
captured by `WfExpr`. `typeOf` canonicalizes record literals via `Map.make`, but
`HasTypeRecord` bakes sortedness into the source syntax, so an unsorted record
literal is typeable by `typeOf` yet has no derivation; `WfExpr` rules those out
(the user-accepted "records are canonicalized" assumption). All other gaps are
closed by the well-formedness of the environment. -/

namespace CedarGen.Relational.Lean

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- Expression-level well-formedness for completeness (relative to `env`), capturing
    the two places where the relational spec is deliberately narrower than *bare*
    `typeOf` on an otherwise-accepted input:

    * **Record literals must have strictly-sorted, distinct keys.** `typeOf`
      canonicalizes them via `Map.make`, but `HasTypeRecord` bakes sortedness into
      the source syntax. (The user-accepted "records are canonical" assumption.)
    * **The tested type of an `is` must be declared.** `HasType` targets the real
      validator `validate` (which runs `checkEntities` first, rejecting `x is T` for
      undeclared `T`); bare `typeOf` skips that check. The tested type is a syntactic
      annotation, so — unlike operand entity types, which are declared automatically
      in a well-formed env — it must be required here.

    Every other `ValidEntityType`/schema premise in `HasType` is *derivable* from a
    successful `typeOf` on a `WfTypeEnv` (operand entity types are always declared),
    so no further conditions are needed. -/
inductive WfExpr : TypeEnv → Expr → Prop where
  | lit : ∀ env p, WfExpr env (.lit p)
  | var : ∀ env v, WfExpr env (.var v)
  | ite : ∀ env a b c, WfExpr env a → WfExpr env b → WfExpr env c → WfExpr env (.ite a b c)
  | and : ∀ env a b, WfExpr env a → WfExpr env b → WfExpr env (.and a b)
  | or : ∀ env a b, WfExpr env a → WfExpr env b → WfExpr env (.or a b)
  | unaryApp : ∀ env op a, (∀ ety, op = .is ety → ValidEntityType ety env.ets env.acts) →
      WfExpr env a → WfExpr env (.unaryApp op a)
  | binaryApp : ∀ env op a b, WfExpr env a → WfExpr env b → WfExpr env (.binaryApp op a b)
  | getAttr : ∀ env a k, WfExpr env a → WfExpr env (.getAttr a k)
  | hasAttr : ∀ env a k, WfExpr env a → WfExpr env (.hasAttr a k)
  | set : ∀ env xs, (∀ e ∈ xs, WfExpr env e) → WfExpr env (.set xs)
  | record : ∀ env axs, (axs.map Prod.fst).SortedBy id → (∀ e ∈ axs.map Prod.snd, WfExpr env e) →
      WfExpr env (.record axs)
  | call : ∀ env f xs, (∀ e ∈ xs, WfExpr env e) → WfExpr env (.call f xs)

/-- **Completeness of `HasType`** (converse of `hasType_sound`): on a well-formed
    environment, any successful `typeOf` run on a `WfExpr` (canonical-record,
    declared-`is`-type) expression is witnessed by a `HasType` derivation with a
    capability-equivalent output. -/
theorem typeOf_complete {env : TypeEnv} (hwf : Schema.WfTypeEnv env) :
    ∀ {x : Expr} {c : Capabilities} {tx : TypedExpr} {c' : Capabilities},
      WfExpr env x → typeOf x c env = .ok (tx, c') →
      ∃ cout, HasType x c env tx.typeOf cout ∧ CapsEquiv cout c' := by
  intro x c
  induction x, c using typeOf.induct with
  | case1 c p => intro hwfx tx c' h; sorry
  | case2 c v => intro hwfx tx c' h; sorry
  | case3 c x₁ x₂ x₃ ih1 ih2 ih3 => intro hwfx tx c' h; sorry
  | case4 c x₁ x₂ ih1 ih2 => intro hwfx tx c' h; sorry
  | case5 c x₁ x₂ ih1 ih2 => intro hwfx tx c' h; sorry
  | case6 c op₁ x₁ ih1 => intro hwfx tx c' h; sorry
  | case7 c op₂ x₁ x₂ ih1 ih2 => intro hwfx tx c' h; sorry
  | case8 c x₁ a ih1 => intro hwfx tx c' h; sorry
  | case9 c x₁ a ih1 => intro hwfx tx c' h; sorry
  | case10 c xs ih => intro hwfx tx c' h; sorry
  | case11 c axs ih => intro hwfx tx c' h; sorry
  | case12 c xfn xs ih => intro hwfx tx c' h; sorry

end CedarGen.Relational.Lean

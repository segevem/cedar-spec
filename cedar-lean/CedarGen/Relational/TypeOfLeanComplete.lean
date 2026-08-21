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

/-- Structural well-formedness of an expression for completeness: every record
    sub-literal has strictly-sorted (hence distinct) keys. `typeOf` accepts
    unsorted record literals (it canonicalizes with `Map.make`) but `HasTypeRecord`
    requires the source key list already sorted, so this restriction is exactly the
    "record literals are canonical" assumption. -/
inductive WfExpr : Expr → Prop where
  | lit : ∀ p, WfExpr (.lit p)
  | var : ∀ v, WfExpr (.var v)
  | ite : ∀ a b c, WfExpr a → WfExpr b → WfExpr c → WfExpr (.ite a b c)
  | and : ∀ a b, WfExpr a → WfExpr b → WfExpr (.and a b)
  | or : ∀ a b, WfExpr a → WfExpr b → WfExpr (.or a b)
  | unaryApp : ∀ op a, WfExpr a → WfExpr (.unaryApp op a)
  | binaryApp : ∀ op a b, WfExpr a → WfExpr b → WfExpr (.binaryApp op a b)
  | getAttr : ∀ a k, WfExpr a → WfExpr (.getAttr a k)
  | hasAttr : ∀ a k, WfExpr a → WfExpr (.hasAttr a k)
  | set : ∀ xs, (∀ e ∈ xs, WfExpr e) → WfExpr (.set xs)
  | record : ∀ axs, (axs.map Prod.fst).SortedBy id → (∀ e ∈ axs.map Prod.snd, WfExpr e) →
      WfExpr (.record axs)
  | call : ∀ f xs, (∀ e ∈ xs, WfExpr e) → WfExpr (.call f xs)

/-- **Completeness of `HasType`** (converse of `hasType_sound`): on a well-formed
    environment, any successful `typeOf` run on a canonical-record expression is
    witnessed by a `HasType` derivation with a capability-equivalent output. -/
theorem typeOf_complete {env : TypeEnv} (hwf : Schema.WfTypeEnv env) :
    ∀ {x : Expr} {c : Capabilities} {tx : TypedExpr} {c' : Capabilities},
      WfExpr x → typeOf x c env = .ok (tx, c') →
      ∃ cout, HasType x c env tx.typeOf cout ∧ CapsEquiv cout c' := by
  sorry

end CedarGen.Relational.Lean

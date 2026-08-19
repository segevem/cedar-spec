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
import Cedar.Thm.Data.Control

/-! # Soundness of the relational typing spec

This file proves that the relational judgement `HasType` (in `TypeOfLean.lean`)
is *sound* with respect to the functional typechecker `Cedar.Validation.typeOf`:
every derivation of `HasType x c env ty cout` corresponds to a successful run of
`typeOf x c env` that produces a typed expression of type `ty` and output
capabilities equivalent (as a set) to `cout`.

Capabilities are compared up to set-equality (`CapsEquiv`) rather than list
equality, because the relation combines them with the nondeterministic `CapMerge`
relation and the concrete `capIntersect` function, whose list order/multiplicity
need not match `typeOf`'s `∪`/`∩`. `typeOf` only ever *consults* capabilities via
membership, so set-equality is the right granularity.
-/

namespace CedarGen.Relational.Lean

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Capability set-equality -/

/-- Two capability lists are equivalent when they have the same elements. -/
def CapsEquiv (c₁ c₂ : Capabilities) : Prop := ∀ k, k ∈ c₁ ↔ k ∈ c₂

theorem CapsEquiv.refl (c : Capabilities) : CapsEquiv c c := fun _ => Iff.rfl

theorem CapsEquiv.symm {c₁ c₂ : Capabilities} (h : CapsEquiv c₁ c₂) : CapsEquiv c₂ c₁ :=
  fun k => (h k).symm

theorem CapsEquiv.trans {c₁ c₂ c₃ : Capabilities}
    (h₁ : CapsEquiv c₁ c₂) (h₂ : CapsEquiv c₂ c₃) : CapsEquiv c₁ c₃ :=
  fun k => (h₁ k).trans (h₂ k)

/-- `∪` respects capability set-equality. -/
theorem CapsEquiv.union {a a' b b' : Capabilities}
    (ha : CapsEquiv a a') (hb : CapsEquiv b b') : CapsEquiv (a ∪ b) (a' ∪ b') := by
  intro k; simp only [List.mem_union_iff, ha k, hb k]

/-- `∩` respects capability set-equality. -/
theorem CapsEquiv.inter {a a' b b' : Capabilities}
    (ha : CapsEquiv a a') (hb : CapsEquiv b b') : CapsEquiv (a ∩ b) (a' ∩ b') := by
  intro k; simp only [List.mem_inter_iff, ha k, hb k]

/-! ## Foundational lemmas about the auxiliary relations

These are self-contained (no induction over `HasType`) and establish that each
structural relation faithfully mirrors the function it replaces. -/

/-- `PrimNeq` faithfully witnesses primitive disequality. -/
theorem primNeq_ne {p₁ p₂ : Prim} (h : PrimNeq p₁ p₂) : p₁ ≠ p₂ := by
  cases h <;> simp_all

/-- `BoolTypeNeq` faithfully witnesses `BoolType` disequality. -/
theorem boolTypeNeq_ne {b₁ b₂ : BoolType} (h : BoolTypeNeq b₁ b₂) : b₁ ≠ b₂ := by
  cases h <;> simp

/-- Membership through a structural `CapMerge` is exactly membership in either side. -/
theorem capMerge_mem {c₁ c₂ c : Capabilities} (h : CapMerge c₁ c₂ c) (k : Expr × Key) :
    k ∈ c ↔ k ∈ c₁ ∨ k ∈ c₂ := by
  induction h with
  | nil => simp
  | left _ _ _ _ _ ih => simp only [List.mem_cons, ih]; grind
  | right _ _ _ _ _ ih => simp only [List.mem_cons, ih]; grind
  | both _ _ _ _ _ ih => simp only [List.mem_cons, ih]; grind

/-- A structural `CapMerge` output is set-equivalent to the functional `∪`. -/
theorem capMerge_capsEquiv_union {c₁ c₂ c : Capabilities} (h : CapMerge c₁ c₂ c) :
    CapsEquiv c (c₁ ∪ c₂) := by
  intro k
  rw [capMerge_mem h k, List.mem_union_iff]

/-- Membership in `capIntersect` is membership in both operands. -/
theorem capIntersect_mem (c₁ c₂ : Capabilities) (k : Expr × Key) :
    k ∈ capIntersect c₁ c₂ ↔ k ∈ c₁ ∧ k ∈ c₂ := by
  obtain ⟨ke, kk⟩ := k
  simp only [capIntersect, List.mem_filter, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  grind

/-- `capIntersect` is set-equivalent to the functional `∩`. -/
theorem capIntersect_capsEquiv_inter (c₁ c₂ : Capabilities) :
    CapsEquiv (capIntersect c₁ c₂) (c₁ ∩ c₂) := by
  intro k
  rw [capIntersect_mem c₁ c₂ k, List.mem_inter_iff]

/-- `SetContains` is exactly list membership on the underlying elements. -/
theorem setContains_mem {α} [BEq α] {x : α} {s : Set α} (h : SetContains x s) :
    x ∈ s.elts := by
  induction h with
  | here => simp [Set.elts]
  | there _ _ _ ih => simp only [Set.elts] at *; exact List.mem_cons_of_mem _ ih

/-! ## Least-upper-bound soundness

`Lub` mirrors `⊔`/`lub?`.  Mutual with `LubRecord`/`LubQualified`. -/

mutual

theorem lub_sound {t₁ t₂ t : CedarType} (h : Lub t₁ t₂ t) : (t₁ ⊔ t₂) = some t := by
  cases h with
  | boolSame b => simp [lub?, lubBool]
  | boolDiff b₁ b₂ hne => simp [lub?, lubBool, if_neg (boolTypeNeq_ne hne)]
  | int => simp [lub?]
  | string => simp [lub?]
  | entity ety => simp [lub?]
  | ext xty => simp [lub?]
  | set s₁ s₂ s hs => simp [lub?, lub_sound hs]
  | record r₁ r₂ r hr => simp [lub?, lubRecord_sound hr]

theorem lubQualified_sound {q₁ q₂ q : QualifiedType} (h : LubQualified q₁ q₂ q) :
    lubQualifiedType q₁ q₂ = some q := by
  cases h with
  | optional t₁ t₂ t ht => simp [lubQualifiedType, lub_sound ht]
  | required t₁ t₂ t ht => simp [lubQualifiedType, lub_sound ht]

theorem lubRecord_sound {r₁ r₂ r : List (Attr × QualifiedType)} (h : LubRecord r₁ r₂ r) :
    lubRecordType r₁ r₂ = some r := by
  cases h with
  | nil => simp [lubRecordType]
  | cons k v₁ v₂ v a b c hq hr => simp [lubRecordType, lubQualified_sound hq, lubRecord_sound hr]

end

/-! ## `typeOf` capability congruence

`typeOf` only reads capabilities via membership, so its result type is invariant
and its output capabilities vary only up to `CapsEquiv` when the input caps do.
This lets us substitute `CapMerge`/`capIntersect` outputs for `typeOf`'s `∪`/`∩`
inside the inductive step. -/

-- Prove by induction mirroring `typeOf`'s recursion. One-directional: if `typeOf`
-- succeeds under `c₁`, it succeeds under any `≈`-equivalent `c₂` with the *same*
-- `TypedExpr` and `≈`-equivalent output capabilities.
/-- `hasAttrInRecord` reads capabilities only via `(x, .attr a) ∈ c`, so
    `≈`-equivalent capabilities give an identical result. -/
theorem hasAttrInRecord_capsEquiv {rty : RecordType} {x : Expr} {a : Attr}
    {c₁ c₂ : Capabilities} {b : Bool} (h : CapsEquiv c₁ c₂) :
    hasAttrInRecord rty x a c₁ b = hasAttrInRecord rty x a c₂ b := by
  unfold hasAttrInRecord
  simp only [h (x, .attr a)]

/-- `getAttrInRecord` reads capabilities only via `(x, .attr a) ∈ c`. -/
theorem getAttrInRecord_capsEquiv {ty : CedarType} {rty : RecordType} {x : Expr} {a : Attr}
    {c₁ c₂ : Capabilities} (h : CapsEquiv c₁ c₂) :
    getAttrInRecord ty rty x a c₁ = getAttrInRecord ty rty x a c₂ := by
  unfold getAttrInRecord
  simp only [h (x, .attr a)]

/-- `typeOfHasTag` reads capabilities only via `(x, .tag t) ∈ c`. -/
theorem typeOfHasTag_capsEquiv {ety : EntityType} {x t : Expr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfHasTag ety x t c₁ env = typeOfHasTag ety x t c₂ env := by
  unfold typeOfHasTag
  simp only [h (x, .tag t)]

/-- `typeOfGetTag` reads capabilities only via `(x, .tag t) ∈ c`. -/
theorem typeOfGetTag_capsEquiv {ety : EntityType} {x t : Expr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfGetTag ety x t c₁ env = typeOfGetTag ety x t c₂ env := by
  unfold typeOfGetTag
  simp only [h (x, .tag t)]

theorem typeOfBinaryApp_capsEquiv {op : BinaryOp} {ty₁ ty₂ : TypedExpr} {x₁ x₂ : Expr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c₁ env = typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c₂ env := by
  unfold typeOfBinaryApp
  simp only [typeOfHasTag_capsEquiv h, typeOfGetTag_capsEquiv h]

theorem typeOfHasAttr_capsEquiv {ty : TypedExpr} {x : Expr} {a : Attr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfHasAttr ty x a c₁ env = typeOfHasAttr ty x a c₂ env := by
  unfold typeOfHasAttr
  simp only [hasAttrInRecord_capsEquiv h]

theorem typeOfGetAttr_capsEquiv {ty : TypedExpr} {x : Expr} {a : Attr}
    {c₁ c₂ : Capabilities} {env : TypeEnv} (h : CapsEquiv c₁ c₂) :
    typeOfGetAttr ty x a c₁ env = typeOfGetAttr ty x a c₂ env := by
  unfold typeOfGetAttr
  simp only [getAttrInRecord_capsEquiv h]

theorem typeOf_capsEquiv {x : Expr} {c₁ c₂ : Capabilities} {env : TypeEnv}
    {tx : TypedExpr} {o₁ : Capabilities}
    (h : CapsEquiv c₁ c₂) (h1 : typeOf x c₁ env = .ok (tx, o₁)) :
    ∃ o₂, typeOf x c₂ env = .ok (tx, o₂) ∧ CapsEquiv o₁ o₂ := by
  induction x, c₁ using typeOf.induct generalizing c₂ tx o₁
  -- lit: `typeOfLit` ignores capabilities
  case _ =>
    simp only [typeOf] at h1 ⊢
    exact ⟨o₁, h1, CapsEquiv.refl _⟩
  -- var: `typeOfVar` ignores capabilities
  case _ =>
    simp only [typeOf] at h1 ⊢
    exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- ite: thread `c ∪ c₁` into the then-branch; combine outputs via ∪/∩
    rename_i c x₁ x₂ x₃ ihA ihB ihC
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r1 =>
      obtain ⟨ty₁, cc₁⟩ := r1
      obtain ⟨cc₁', hx1', hcc1⟩ := ihA h hx1
      have hu : CapsEquiv (c ∪ cc₁) (c₂ ∪ cc₁') := CapsEquiv.union h hcc1
      simp only [hx1, hx1', Except.bind_ok, typeOfIf] at h1 ⊢
      split at h1
      next => -- condition : .bool .tt
        cases hx2 : typeOf x₂ (c ∪ cc₁) env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB cc₁ hu hx2
          simp only [hx2, Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          simp only [hx2', Except.bind_ok, ok]
          exact ⟨_, rfl, CapsEquiv.union hcc1 hc2⟩
      next => -- condition : .bool .ff
        cases hx3 : typeOf x₃ c env with
        | error e => simp [hx3] at h1
        | ok r3 =>
          obtain ⟨ty₃, c3⟩ := r3
          obtain ⟨c3', hx3', hc3⟩ := ihC h hx3
          simp only [hx3, Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          simp only [hx3', Except.bind_ok, ok]
          exact ⟨_, rfl, hc3⟩
      next => -- condition : .bool .anyBool
        cases hx2 : typeOf x₂ (c ∪ cc₁) env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB cc₁ hu hx2
          cases hx3 : typeOf x₃ c env with
          | error e => simp [hx2, hx3] at h1
          | ok r3 =>
            obtain ⟨ty₃, c3⟩ := r3
            obtain ⟨c3', hx3', hc3⟩ := ihC h hx3
            simp only [hx2, hx3, Except.bind_ok] at h1
            simp only [hx2', hx3', Except.bind_ok]
            split at h1
            next ty hlub =>
              simp only [hlub, ok, Except.ok.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, rfl⟩ := h1
              simp only [hlub, ok]
              exact ⟨_, rfl, CapsEquiv.inter (CapsEquiv.union hcc1 hc2) hc3⟩
            next hlub => simp [err] at h1
      next => simp [err] at h1 -- condition : non-boolean
  case _ => -- and: threads `c ∪ c₁` into the second operand like `ite`
    rename_i c x₁ x₂ ihA ihB
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r1 =>
      obtain ⟨ty₁, cc₁⟩ := r1
      obtain ⟨cc₁', hx1', hcc1⟩ := ihA h hx1
      have hu : CapsEquiv (c ∪ cc₁) (c₂ ∪ cc₁') := CapsEquiv.union h hcc1
      simp only [hx1, hx1', Except.bind_ok, typeOfAnd] at h1 ⊢
      split at h1
      next => -- ty₁ = .bool .ff : short-circuit, output ∅
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp only [ok]
        exact ⟨_, rfl, CapsEquiv.refl _⟩
      next => -- ty₁ = .bool _ (tt / anyBool)
        cases hx2 : typeOf x₂ (c ∪ cc₁) env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB cc₁ hu hx2
          simp only [hx2, Except.bind_ok] at h1
          simp only [hx2', Except.bind_ok]
          split at h1
          next => -- ty₂ = .bool .ff : output ∅
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            simp only [ok]; exact ⟨_, rfl, CapsEquiv.refl _⟩
          next => -- ty₂ = .bool .tt
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            simp only [ok]; exact ⟨_, rfl, CapsEquiv.union hcc1 hc2⟩
          next => -- ty₂ = .bool .anyBool
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            simp only [ok]; exact ⟨_, rfl, CapsEquiv.union hcc1 hc2⟩
          next => simp [err] at h1 -- ty₂ non-boolean
      next => simp [err] at h1 -- ty₁ non-boolean
  case _ => -- or: second operand typed under `c` (not threaded)
    rename_i c x₁ x₂ ihA ihB
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r1 =>
      obtain ⟨ty₁, cc₁⟩ := r1
      obtain ⟨cc₁', hx1', hcc1⟩ := ihA h hx1
      simp only [hx1, hx1', Except.bind_ok, typeOfOr] at h1 ⊢
      split at h1
      next => -- ty₁ = .bool .tt : output ∅
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp only [ok]; exact ⟨_, rfl, CapsEquiv.refl _⟩
      next => -- ty₁ = .bool .ff
        cases hx2 : typeOf x₂ c env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB h hx2
          simp only [hx2, Except.bind_ok] at h1
          simp only [hx2', Except.bind_ok]
          split at h1
          next => -- ty₂ = .bool _ : output c₂
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1; simp only [ok]; exact ⟨_, rfl, hc2⟩
          next => simp [err] at h1
      next => -- ty₁ = .bool .anyBool
        cases hx2 : typeOf x₂ c env with
        | error e => simp [hx2] at h1
        | ok r2 =>
          obtain ⟨ty₂, c2⟩ := r2
          obtain ⟨c2', hx2', hc2⟩ := ihB h hx2
          simp only [hx2, Except.bind_ok] at h1
          simp only [hx2', Except.bind_ok]
          split at h1
          next => -- ty₂ = .bool .tt : output ∅
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1; simp only [ok]; exact ⟨_, rfl, CapsEquiv.refl _⟩
          next => -- ty₂ = .bool .ff : output c₁
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1; simp only [ok]; exact ⟨_, rfl, hcc1⟩
          next => -- ty₂ = .bool .anyBool : output c₁ ∩ c₂
            simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1; simp only [ok]; exact ⟨_, rfl, CapsEquiv.inter hcc1 hc2⟩
          next => simp [err] at h1
      next => simp [err] at h1 -- ty₁ non-boolean
  case _ => -- unaryApp: recurse on `x₁`; `typeOfUnaryApp` is capability-free
    rename_i c op x₁ ih1
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r =>
      obtain ⟨ty₁, oc₁⟩ := r
      obtain ⟨oc₂, hx2, _⟩ := ih1 h hx1
      simp only [hx1, hx2, Except.bind_ok] at h1 ⊢
      exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- binaryApp: recurse on both operands; `typeOfBinaryApp` reads caps
            -- only in the hasTag/getTag arms (invariant under ≈)
    rename_i c op x₁ x₂ ihx1 ihx2
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r1 =>
      obtain ⟨t1, oc1⟩ := r1
      cases hx2 : typeOf x₂ c env with
      | error e => simp [hx1, hx2, Except.bind_ok] at h1
      | ok r2 =>
        obtain ⟨t2, oc2⟩ := r2
        obtain ⟨oc1', hx1', _⟩ := ihx1 h hx1
        obtain ⟨oc2', hx2', _⟩ := ihx2 h hx2
        simp only [hx1, hx2, hx1', hx2', Except.bind_ok, typeOfBinaryApp_capsEquiv h] at h1 ⊢
        exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- hasAttr: `typeOfHasAttr` reads caps only via membership (invariant under ≈)
    rename_i c x₁ a ih1
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r =>
      obtain ⟨ty₁, oc₁⟩ := r
      obtain ⟨oc₂, hx2, _⟩ := ih1 h hx1
      simp only [hx1, hx2, Except.bind_ok, typeOfHasAttr_capsEquiv h] at h1 ⊢
      exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => -- getAttr
    rename_i c x₁ a ih1
    simp only [typeOf] at h1 ⊢
    cases hx1 : typeOf x₁ c env with
    | error e => simp [hx1] at h1
    | ok r =>
      obtain ⟨ty₁, oc₁⟩ := r
      obtain ⟨oc₂, hx2, _⟩ := ih1 h hx1
      simp only [hx1, hx2, Except.bind_ok, typeOfGetAttr_capsEquiv h] at h1 ⊢
      exact ⟨o₁, h1, CapsEquiv.refl _⟩
  case _ => sorry -- set
  case _ => sorry -- record
  case _ => sorry -- call

/-! ## Main soundness theorem

Stated over the whole mutual family (`HasType` / `HasTypeList` / `HasTypeRecord`
/ `HasTypeExtCall`). The four statements are proven simultaneously by mutual
induction on the derivation.

Case plan (each maps to one `typeOf*` arm):
* `litBool*/litInt/litString/litEntity`  → `typeOfLit`
* `varPrincipal/Action/Resource/Context`  → `typeOfVar`
* `unaryApp*`                             → `typeOfUnaryApp`
* `binaryAppEq*`                          → `typeOfEq`
* `binaryAppLess*/Add/Sub/Mul`            → `typeOfBinaryApp` arithmetic arms
* `binaryAppContains*`                    → `typeOfBinaryApp` set-op arms (needs `lub_sound`/`LubCompat`)
* `binaryAppMem*`, action-literal cases   → `typeOfInₑ`/`typeOfInₛ` (needs ancestry correspondence)
* `hasAttr*`                              → `typeOfHasAttr`/`hasAttrInRecord`
* `getAttr*`                              → `typeOfGetAttr`/`getAttrInRecord`
* `hasTag*`/`getTag`                      → `typeOfHasTag`/`typeOfGetTag`
* `ite*`/`and*`/`or*`                     → `typeOfIf`/`typeOfAnd`/`typeOfOr` (needs cap congruence)
* `set`/`record`/`callExt`                → `typeOfSet`/record arm/`typeOfCall` (needs list/record glue)
-/

/-- Soundness of `HasType`: a derivation implies `typeOf` succeeds with the same
    type and capability-equivalent output. -/
theorem hasType_sound {x : Expr} {c : Capabilities} {env : TypeEnv}
    {ty : CedarType} {cout : Capabilities}
    (h : HasType x c env ty cout) :
    ∃ tx c', typeOf x c env = .ok (tx, c') ∧ tx.typeOf = ty ∧ CapsEquiv cout c' := by
  -- `cases` (not `induction`: `HasType` is mutually inductive). Leaf cases need no
  -- IH; the recursive cases will be discharged via a 4-way mutual-theorem structure
  -- (as in `lub_sound`), which is the documented next step.
  cases h
  -- Literals → `typeOfLit`.  Provide the `TypedExpr` witness explicitly so
  -- elaboration never has to synthesize it; the equation is then a `simp`, the
  -- type projection an `rfl`, and the (empty) capabilities are trivially equal.
  case litBoolTrue ets acts reqty =>
    exact ⟨.lit (.bool true) (.bool .tt), [], by simp [typeOf, typeOfLit, ok], rfl, fun _ => Iff.rfl⟩
  case litBoolFalse ets acts reqty =>
    exact ⟨.lit (.bool false) (.bool .ff), [], by simp [typeOf, typeOfLit, ok], rfl, fun _ => Iff.rfl⟩
  case litInt i ets acts reqty =>
    exact ⟨.lit (.int i) .int, [], by simp [typeOf, typeOfLit, ok], rfl, fun _ => Iff.rfl⟩
  case litString s ets acts reqty =>
    exact ⟨.lit (.string s) .string, [], by simp [typeOf, typeOfLit, ok], rfl, fun _ => Iff.rfl⟩
  -- Variables → `typeOfVar`
  case varPrincipal ets acts princ action resource ctx =>
    exact ⟨.var .principal (.entity princ), [], by simp [typeOf, typeOfVar, ok], rfl, fun _ => Iff.rfl⟩
  case varAction ets acts princ actionTy actionEid resource ctx =>
    exact ⟨.var .action (.entity actionTy), [], by simp [typeOf, typeOfVar, ok], rfl, fun _ => Iff.rfl⟩
  case varResource ets acts princ action resource ctx =>
    exact ⟨.var .resource (.entity resource), [], by simp [typeOf, typeOfVar, ok], rfl, fun _ => Iff.rfl⟩
  case varContext ets acts princ action resource ctx =>
    exact ⟨.var .context (.record ctx), [], by simp [typeOf, typeOfVar, ok], rfl, fun _ => Iff.rfl⟩
  -- Remaining cases: see the case plan above.
  all_goals sorry

end CedarGen.Relational.Lean

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
import CedarGen.Relational.Schema
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Map

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

/-! ## Structural map/set membership ↔ lookup

`MapContains`/`SetContains` mirror `Map.find?`/`Set.contains`. The `find?`
direction needs the map to be well-formed (duplicate-free) — supplied by
`Schema.WfTypeEnv` in `hasType_sound`. -/

/-- `MapContains` implies the pair is in the underlying list (well-formedness free). -/
theorem mapContains_mem {α β : Type} {k : α} {v : β} {m : Map α β} (h : MapContains k v m) :
    (k, v) ∈ m.toList := by
  induction h with
  | here => simp [Map.toList]
  | there _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- On a well-formed (duplicate-free) map, `MapContains` agrees with `find?`. -/
theorem mapContains_find? {α β : Type} [DecidableEq α] [LT α] [DecidableLT α] [StrictLT α]
    {k : α} {v : β} {m : Map α β} (h : MapContains k v m) (wf : m.WellFormed) :
    m.find? k = some v :=
  (Map.in_list_iff_find?_some wf).mp (mapContains_mem h)

/-- Converse of `mapContains_mem`: list membership rebuilds a `MapContains` witness. -/
theorem mem_toList_mapContains {α β : Type} {k : α} {v : β} {m : Map α β}
    (h : (k, v) ∈ m.toList) : MapContains k v m := by
  obtain ⟨l⟩ := m
  simp only [Map.toList] at h
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rcases List.mem_cons.mp h with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact MapContains.here _ _ _
    · exact MapContains.there _ _ _ _ _ (ih hmem)

/-- On a map with duplicate-free keys, `MapContains` agrees with `find?`. This is the
    distinctness-based analogue of `mapContains_find?` (which needs full `WellFormed`); the
    generated schema maps are distinct-keyed but *not* sorted, so this is the usable form. -/
theorem mapContains_find?_nodup {α β : Type} [BEq α] [LawfulBEq α]
    {k : α} {v : β} {m : Map α β}
    (h : MapContains k v m) (hnd : (m.toList.map Prod.fst).Nodup) :
    m.find? k = some v := by
  induction h with
  | here rest => simp [Map.find?, Map.toList]
  | there k' v' rest hmc ih =>
    simp only [Map.toList, List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hnd'⟩ := hnd
    have hkin : k ∈ rest.map Prod.fst :=
      List.mem_map.mpr ⟨(k, v), by simpa only [Map.toList] using mapContains_mem hmc, rfl⟩
    have hne : (k' == k) = false := by
      rw [beq_eq_false_iff_ne]; exact fun heq => hnotin (heq ▸ hkin)
    have hih := ih hnd'
    simp only [Map.find?, Map.toList, List.find?_cons, hne] at hih ⊢
    exact hih

/-- `MapNotContainsKey` mirrors `find? = none`. -/
theorem mapNotContainsKey_find? {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    {k : α} {m : Map α β} (h : MapNotContainsKey k m) : m.find? k = none := by
  induction h with
  | empty => simp [Map.find?, Map.toList]
  | skip k' v' rest hne hrec ih =>
    have : (k' == k) = false := by rw [beq_eq_false_iff_ne]; exact fun heq => hne heq.symm
    simp only [Map.find?, Map.toList, List.find?_cons, this] at ih ⊢
    exact ih

/-- Converse of `setContains_mem`. -/
theorem mem_elts_setContains {α} {x : α} {s : Set α} (h : x ∈ s.elts) : SetContains x s := by
  obtain ⟨l⟩ := s
  simp only [Set.elts] at h
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact SetContains.here _ _
    · exact SetContains.there _ _ _ (ih hmem)

/-- `SetContains` mirrors `Set.contains`. -/
theorem setContains_iff_contains {α} [DecidableEq α] {x : α} {s : Set α} :
    SetContains x s ↔ s.contains x = true := by
  constructor
  · intro h; simp only [Set.contains, List.elem_eq_mem, decide_eq_true_eq]; exact setContains_mem h
  · intro h; simp only [Set.contains, List.elem_eq_mem, decide_eq_true_eq] at h
    exact mem_elts_setContains h

/-- `CapTagMem` mirrors capability membership. -/
theorem capTagMem_iff {x e : Expr} {c : Capabilities} :
    CapTagMem x e c ↔ (x, Key.tag e) ∈ c := by
  constructor
  · intro h; induction h with
    | here => simp
    | there _ _ _ _ ih => exact List.mem_cons_of_mem _ ih
  · intro h; induction c with
    | nil => simp at h
    | cons hd tl ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · exact CapTagMem.here _ _ _
      · obtain ⟨x', k'⟩ := hd; exact CapTagMem.there _ _ _ _ _ (ih hmem)

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

/-- Capability-congruence for a `mapM` of `justType ∘ typeOf` (the `set`/`call`
    element pass): given per-element congruence, a successful run under `c₁`
    reruns identically under `≈`-equivalent `c₂`. -/
theorem typeOfList_capsEquiv {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv}
    (ih : ∀ x ∈ xs, ∀ {tx : TypedExpr} {o : Capabilities}, typeOf x c₁ env = .ok (tx, o) →
            ∃ o', typeOf x c₂ env = .ok (tx, o') ∧ CapsEquiv o o') :
    ∀ {tys : List TypedExpr}, xs.mapM (fun x => justType (typeOf x c₁ env)) = .ok tys →
             xs.mapM (fun x => justType (typeOf x c₂ env)) = .ok tys := by
  induction xs with
  | nil => intro tys hm; simpa using hm
  | cons x xs ihxs =>
    intro tys hm
    simp only [List.mapM_cons] at hm ⊢
    cases hx1 : typeOf x c₁ env with
    | error e =>
      have hj1 : justType (typeOf x c₁ env) = .error e := by simp only [hx1, justType, Except.map]
      simp [hj1] at hm
    | ok r =>
      obtain ⟨t, o⟩ := r
      obtain ⟨o', hx2, _⟩ := ih x (List.mem_cons_self ..) hx1
      have hj1 : justType (typeOf x c₁ env) = .ok t := by simp only [hx1, justType, Except.map]
      have hj2 : justType (typeOf x c₂ env) = .ok t := by simp only [hx2, justType, Except.map]
      cases htl : xs.mapM (fun x => justType (typeOf x c₁ env)) with
      | error e => simp [hj1, htl] at hm
      | ok ts =>
        have htl2 := ihxs (fun x hx => ih x (List.mem_cons_of_mem _ hx)) htl
        simp [hj1, hj2, htl, htl2] at hm ⊢
        exact hm

/-- Capability-congruence for the `record` element pass (`mapM₂`). -/
theorem typeOfRecordList_capsEquiv {axs : List (Attr × Expr)} {c₁ c₂ : Capabilities} {env : TypeEnv}
    (ih : ∀ ax ∈ axs, ∀ {tx : TypedExpr} {o : Capabilities}, typeOf ax.2 c₁ env = .ok (tx, o) →
            ∃ o', typeOf ax.2 c₂ env = .ok (tx, o') ∧ CapsEquiv o o') :
    ∀ {atys : List (Attr × TypedExpr)},
      axs.mapM (fun ax => (typeOf ax.2 c₁ env).map (fun r => (ax.1, r.1))) = .ok atys →
      axs.mapM (fun ax => (typeOf ax.2 c₂ env).map (fun r => (ax.1, r.1))) = .ok atys := by
  induction axs with
  | nil => intro atys hm; simpa using hm
  | cons ax axs ihxs =>
    intro atys hm
    simp only [List.mapM_cons] at hm ⊢
    cases hx1 : typeOf ax.2 c₁ env with
    | error e =>
      have hj1 : (typeOf ax.2 c₁ env).map (fun r => (ax.1, r.1)) = .error e := by
        simp only [hx1, Except.map]
      simp [hj1] at hm
    | ok r =>
      obtain ⟨t, o⟩ := r
      obtain ⟨o', hx2, _⟩ := ih ax (List.mem_cons_self ..) hx1
      have hj1 : (typeOf ax.2 c₁ env).map (fun r => (ax.1, r.1)) = .ok (ax.1, t) := by
        simp only [hx1, Except.map]
      have hj2 : (typeOf ax.2 c₂ env).map (fun r => (ax.1, r.1)) = .ok (ax.1, t) := by
        simp only [hx2, Except.map]
      cases htl : axs.mapM (fun ax => (typeOf ax.2 c₁ env).map (fun r => (ax.1, r.1))) with
      | error e => simp [hj1, htl] at hm
      | ok ts =>
        have htl2 := ihxs (fun ax hx => ih ax (List.mem_cons_of_mem _ hx)) htl
        simp [hj1, hj2, htl, htl2] at hm ⊢
        exact hm

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
  case _ => -- set: element pass via `typeOfList_capsEquiv`; `typeOfSet` is cap-free
    rename_i c xs ih1
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)),
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c₂ env))] at h1 ⊢
    cases hm : List.mapM (fun x => justType (typeOf x c env)) xs with
    | error e => simp [hm] at h1
    | ok tys =>
      have hm2 := typeOfList_capsEquiv (fun x hx => ih1 x hx h) hm
      simp only [hm, hm2, Except.bind_ok] at h1 ⊢
      exact ⟨_, h1, CapsEquiv.refl _⟩
  case _ => -- record: element pass via `typeOfRecordList_capsEquiv`; builder is cap-free
    rename_i c axs ih1
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun p : Attr × Expr => (typeOf p.2 c env).map (fun r => (p.1, r.1))),
      List.mapM₂_eq_mapM (fun p : Attr × Expr => (typeOf p.2 c₂ env).map (fun r => (p.1, r.1)))] at h1 ⊢
    cases hm : axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) with
    | error e => simp [hm] at h1
    | ok atys =>
      have hm2 := typeOfRecordList_capsEquiv
        (fun ax hx => ih1 ax.1 ax.2 (List.sizeOf_snd_lt_sizeOf_list hx) h) hm
      simp only [hm, hm2, Except.bind_ok, ok] at h1 ⊢
      exact ⟨_, h1, CapsEquiv.refl _⟩
  case _ => -- call: same element pass as `set`; `typeOfCall` is cap-free
    rename_i c xfn xs ih1
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env)),
      List.mapM₁_eq_mapM (fun x => justType (typeOf x c₂ env))] at h1 ⊢
    cases hm : List.mapM (fun x => justType (typeOf x c env)) xs with
    | error e => simp [hm] at h1
    | ok tys =>
      have hm2 := typeOfList_capsEquiv (fun x hx => ih1 x hx h) hm
      simp only [hm, hm2, Except.bind_ok] at h1 ⊢
      exact ⟨_, h1, CapsEquiv.refl _⟩

/-! ## Schema well-formedness ⇒ distinct keys

`WfEntitiesGo`/`WfActionsGo` build entries with distinct keys (via `NotInET`
threading and `SelectRemove` draw-without-replacement) but *not* sorted, so
`mapContains_find?_nodup` — not the `WellFormed` form — is the applicable bridge. -/

theorem notInET_not_mem {et : EntityType} {names : List EntityType}
    (h : Schema.NotInET et names) : et ∉ names := by
  induction h with
  | nil => simp
  | cons x rest hne hrec ih => simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩

theorem wfEntitiesGo_nodup {built names allNames entries}
    (h : Schema.WfEntitiesGo built names allNames entries) :
    (entries.map Prod.fst).Nodup ∧ ∀ k ∈ entries.map Prod.fst, k ∉ names := by
  induction h with
  | nil => simp
  | standard built names et ancestors attrs tags allNames rest hni hpca hattrs htags hgo ih =>
    obtain ⟨ihnd, ihnotin⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun hmem => (ihnotin et hmem) List.mem_cons_self, ihnd⟩
    · intro k hk
      simp only [List.map_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact notInET_not_mem hni
      · exact fun hmem => ihnotin k hk (List.mem_cons_of_mem et hmem)
  | enum built names et eids allNames rest hni hgo ih =>
    obtain ⟨ihnd, ihnotin⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun hmem => (ihnotin et hmem) List.mem_cons_self, ihnd⟩
    · intro k hk
      simp only [List.map_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact notInET_not_mem hni
      · exact fun hmem => ihnotin k hk (List.mem_cons_of_mem et hmem)

theorem wfEntitySchema_nodup {allNames entries}
    (h : Schema.WfEntitySchema allNames entries) : (entries.map Prod.fst).Nodup := by
  cases h with
  | mk hgo => exact (wfEntitiesGo_nodup hgo).1

/-- Entity-store keys of a well-formed `TypeEnv` are distinct. -/
theorem wfTypeEnv_ets_nodup {env : TypeEnv} (h : Schema.WfTypeEnv env) :
    (env.ets.toList.map Prod.fst).Nodup := by
  cases h with
  | mk entityTypes entityEntries actionEntries reqty hes _ _ =>
    simpa only [Map.toList] using wfEntitySchema_nodup hes

theorem selectRemove_mem {α} {avail : List α} {eid : α} {avail' : List α}
    (h : Schema.SelectRemove avail eid avail') : eid ∈ avail := by
  induction h with
  | here => exact List.mem_cons_self
  | there x xs y ys hsr ih => exact List.mem_cons_of_mem _ ih

theorem selectRemove_subset {α} {avail : List α} {eid : α} {avail' : List α}
    (h : Schema.SelectRemove avail eid avail') : ∀ x ∈ avail', x ∈ avail := by
  induction h with
  | here => exact fun x hx => List.mem_cons_of_mem _ hx
  | there x xs y ys hsr ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih z hz)

theorem selectRemove_nodup {α} {avail : List α} {eid : α} {avail' : List α}
    (h : Schema.SelectRemove avail eid avail') (hnd : avail.Nodup) :
    avail'.Nodup ∧ eid ∉ avail' := by
  induction h with
  | here => rw [List.nodup_cons] at hnd; exact ⟨hnd.2, hnd.1⟩
  | there x xs y ys hsr ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hxnotin, hndxs⟩ := hnd
    obtain ⟨ihnd, ihnotin⟩ := ih hndxs
    refine ⟨?_, ?_⟩
    · rw [List.nodup_cons]; exact ⟨fun hmem => hxnotin (selectRemove_subset hsr x hmem), ihnd⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨fun heq => hxnotin (heq ▸ selectRemove_mem hsr), ihnotin⟩

theorem actionEidPool_nodup : Schema.actionEidPool.Nodup := by decide

theorem wfActionsGo_nodup {ets built avail entries}
    (h : Schema.WfActionsGo ets built avail entries) :
    avail.Nodup → (entries.map Prod.fst).Nodup ∧
      ∀ uid ∈ entries.map Prod.fst, EntityUID.eid uid ∈ avail := by
  induction h with
  | nil => intro _; simp
  | cons =>
    rename_i hsr hpca hp hr hattrs hgo ih
    intro hnd
    obtain ⟨hndavail', hnotin⟩ := selectRemove_nodup hsr hnd
    obtain ⟨ihnd, ihmem⟩ := ih hndavail'
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun hmem => hnotin (ihmem _ hmem), ihnd⟩
    · intro uid huid
      simp only [List.map_cons, List.mem_cons] at huid
      rcases huid with rfl | huid
      · exact selectRemove_mem hsr
      · exact selectRemove_subset hsr _ (ihmem _ huid)

theorem wfActionSchema_nodup {ets entries} (h : Schema.WfActionSchema ets entries) :
    (entries.map Prod.fst).Nodup := by
  cases h with
  | mk hgo => exact (wfActionsGo_nodup hgo actionEidPool_nodup).1

/-- Action-store keys of a well-formed `TypeEnv` are distinct. -/
theorem wfTypeEnv_acts_nodup {env : TypeEnv} (h : Schema.WfTypeEnv env) :
    (env.acts.toList.map Prod.fst).Nodup := by
  cases h with
  | mk entityTypes entityEntries actionEntries reqty _ has _ =>
    simpa only [Map.toList] using wfActionSchema_nodup has

/-! ## Structural extractors ↔ schema lookups -/

theorem mapContainsAttrs_mc {ety rty ets} (h : MapContainsAttrs ety rty ets) :
    ∃ entry, MapContains ety entry ets ∧ EntitySchemaEntry.attrs entry = rty := by
  induction h with
  | here => exact ⟨_, MapContains.here _ _ _, rfl⟩
  | there => rename_i ih; obtain ⟨e, hmc, he⟩ := ih; exact ⟨e, MapContains.there _ _ _ _ _ hmc, he⟩

theorem mapContainsTagType_mc {ety ty ets} (h : MapContainsTagType ety ty ets) :
    ∃ entry, MapContains ety entry ets ∧ EntitySchemaEntry.tags? entry = some ty := by
  induction h with
  | here => exact ⟨_, MapContains.here _ _ _, rfl⟩
  | there => rename_i ih; obtain ⟨e, hmc, he⟩ := ih; exact ⟨e, MapContains.there _ _ _ _ _ hmc, he⟩

theorem mapContainsNoTags_mc {ety ets} (h : MapContainsNoTags ety ets) :
    ∃ entry, MapContains ety entry ets ∧ EntitySchemaEntry.tags? entry = none := by
  induction h with
  | here => exact ⟨_, MapContains.here _ _ _, rfl⟩
  | there => rename_i ih; obtain ⟨e, hmc, he⟩ := ih; exact ⟨e, MapContains.there _ _ _ _ _ hmc, he⟩

theorem mapContainsAncestors_mc {ety ancs ets} (h : MapContainsAncestors ety ancs ets) :
    ∃ entry, MapContains ety entry ets ∧ EntitySchemaEntry.ancestors entry = ancs := by
  induction h with
  | here => exact ⟨_, MapContains.here _ _ _, rfl⟩
  | there => rename_i ih; obtain ⟨e, hmc, he⟩ := ih; exact ⟨e, MapContains.there _ _ _ _ _ hmc, he⟩

theorem mapContainsPairKey_mc {v : Type} {ety : EntityType} {eid : String} {entry : v}
    {acts : Map EntityUID v} (h : MapContainsPairKey ety eid entry acts) :
    MapContains ⟨ety, eid⟩ entry acts := by
  induction h with
  | here => exact MapContains.here _ _ _
  | nextA hne _ ih => exact MapContains.there _ _ _ _ _ ih
  | nextB hne _ ih => exact MapContains.there _ _ _ _ _ ih

/-- `MapContainsAttrs` ⇒ `EntitySchema.attrs?` (on distinct-keyed store). -/
theorem mapContainsAttrs_attrs? {ety rty ets} (h : MapContainsAttrs ety rty ets)
    (hnd : (ets.toList.map Prod.fst).Nodup) : EntitySchema.attrs? ets ety = some rty := by
  obtain ⟨entry, hmc, he⟩ := mapContainsAttrs_mc h
  simp only [EntitySchema.attrs?, mapContains_find?_nodup hmc hnd, Option.map_some, he]

/-- `HasTagSchema` ⇒ `EntitySchema.tags? = some (some ty)`. -/
theorem hasTagSchema_tags? {ety ty ets} (h : HasTagSchema ets ety ty)
    (hnd : (ets.toList.map Prod.fst).Nodup) : EntitySchema.tags? ets ety = some (some ty) := by
  cases h with
  | mk hmct =>
    obtain ⟨entry, hmc, he⟩ := mapContainsTagType_mc hmct
    simp only [EntitySchema.tags?, mapContains_find?_nodup hmc hnd, Option.map_some, he]

/-- `NoTags` ⇒ `EntitySchema.tags? = some none`. -/
theorem noTags_tags? {ety ets} (h : NoTags ets ety)
    (hnd : (ets.toList.map Prod.fst).Nodup) : EntitySchema.tags? ets ety = some none := by
  cases h with
  | none hmcn =>
    obtain ⟨entry, hmc, he⟩ := mapContainsNoTags_mc hmcn
    simp only [EntitySchema.tags?, mapContains_find?_nodup hmc hnd, Option.map_some, he]

/-- `lub?` of two distinct entity types is `none`. -/
theorem lub_entity_ne {ety₁ ety₂ : EntityType} (h : ety₁ ≠ ety₂) :
    lub? (.entity ety₁) (.entity ety₂) = none := by
  simp only [lub?, CedarType.entity.injEq, ite_eq_right_iff]
  intro heq; exact absurd heq h

/-- `ValidDifferentEntityType` carries the disequality. -/
theorem validDifferentEntityType_ne {other ety ets acts}
    (h : ValidDifferentEntityType other ety ets acts) : ety ≠ other := by
  cases h <;> assumption

/-! ## Entity/action hierarchy ↔ `descendentOf` -/

/-- `DescendentOf` ⇒ `TypeEnv.descendentOf = true`. -/
theorem descendentOf_sound {ets acts ety₁ ety₂ reqty} (h : DescendentOf ets acts ety₁ ety₂)
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = true := by
  cases h with
  | refl => simp only [TypeEnv.descendentOf, ↓reduceIte]
  | ancestor ancs hanc hsc =>
    by_cases heq : ety₁ = ety₂
    · simp only [TypeEnv.descendentOf, heq, ↓reduceIte]
    · obtain ⟨entry, hmc, he⟩ := mapContainsAncestors_mc hanc
      simp only [TypeEnv.descendentOf, if_neg heq, mapContains_find?_nodup hmc hnd, he,
        (setContains_iff_contains).mp hsc]

/-- `NotDescendentOf` ⇒ `TypeEnv.descendentOf = false`. -/
theorem notDescendentOf_sound {ets acts ety₁ ety₂ reqty} (h : NotDescendentOf ets acts ety₁ ety₂)
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    TypeEnv.descendentOf ⟨ets, acts, reqty⟩ ety₁ ety₂ = false := by
  cases h with
  | diff ancs hne hanc hnsc =>
    obtain ⟨entry, hmc, he⟩ := mapContainsAncestors_mc hanc
    have hc : Set.contains ancs ety₂ = false :=
      Bool.eq_false_iff.mpr (fun hcon => hnsc ((setContains_iff_contains).mpr hcon))
    simp only [TypeEnv.descendentOf, if_neg hne, mapContains_find?_nodup hmc hnd, he, hc]

/-- `ActionDescendentOf` ⇒ `ActionSchema.descendentOf = true`. -/
theorem actionDescendentOf_sound {acts uid₁ uid₂} (h : ActionDescendentOf acts uid₁ uid₂)
    (hnd : (acts.toList.map Prod.fst).Nodup) :
    ActionSchema.descendentOf acts uid₁ uid₂ = true := by
  cases h with
  | refl entry hmc => simp only [ActionSchema.descendentOf, beq_self_eq_true, ↓reduceIte]
  | ancestor entry hmc hsc =>
    by_cases heq : uid₁ = uid₂
    · simp only [ActionSchema.descendentOf, heq, beq_self_eq_true, ↓reduceIte]
    · simp only [ActionSchema.descendentOf, beq_iff_eq, if_neg heq,
        mapContains_find?_nodup hmc hnd, (setContains_iff_contains).mp hsc]

/-- `NotActionDescendentOf` ⇒ `ActionSchema.descendentOf = false`. -/
theorem notActionDescendentOf_sound {acts uid₁ uid₂} (h : NotActionDescendentOf acts uid₁ uid₂)
    (hnd : (acts.toList.map Prod.fst).Nodup) :
    ActionSchema.descendentOf acts uid₁ uid₂ = false := by
  cases h with
  | diff entry hne hmc hnsc =>
    have hc : Set.contains entry.ancestors uid₂ = false :=
      Bool.eq_false_iff.mpr (fun hcon => hnsc ((setContains_iff_contains).mpr hcon))
    simp only [ActionSchema.descendentOf, beq_iff_eq, if_neg hne,
      mapContains_find?_nodup hmc hnd, hc]

/-! ## `AllLub` ↔ `foldlM lub?` -/

/-- `AllLub` mirrors the `foldlM lub?` pass in `typeOfSet`. -/
theorem allLub_foldlM {acc tyList result} (h : AllLub acc tyList result) :
    tyList.foldlM lub? acc = some result := by
  induction h with
  | nil => simp [List.foldlM]
  | cons acc hd tl lubTy result hlub hrest ih =>
    simp only [List.foldlM_cons, lub_sound hlub, Option.some_bind]
    exact ih

/-! ## `ValidEntityUID` ↔ `typeOfLit` entity validity -/

/-- `ValidEntityUID` ⇒ the `typeOfLit` validity guard holds. -/
theorem validEntityUID_lit {ety eid ets acts}
    (h : ValidEntityUID ety eid ets acts)
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    (EntitySchema.isValidEntityUID ets ⟨ety, eid⟩ || ActionSchema.contains acts ⟨ety, eid⟩) = true := by
  cases h with
  | standard entry hmc =>
    simp only [EntitySchema.isValidEntityUID, mapContains_find?_nodup hmc hndE,
      EntitySchemaEntry.isValidEntityEID, Bool.true_or]
  | enum eids hmc hsc =>
    simp only [EntitySchema.isValidEntityUID, mapContains_find?_nodup hmc hndE,
      EntitySchemaEntry.isValidEntityEID, (setContains_iff_contains).mp hsc, Bool.true_or]
  | action entry hpk =>
    simp only [ActionSchema.contains, mapContains_find?_nodup (mapContainsPairKey_mc hpk) hndA,
      Option.isSome_some, Bool.or_true]

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
    (hwf : Schema.WfTypeEnv env)
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

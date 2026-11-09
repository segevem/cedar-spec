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

import CedarGen.Relational.SchemaGen
import Specimen.Correctness.GenExpectSPMF

/-! # Distribution facts about the derived schema generator

Proved of the derived code itself, at the sampler's monad (`SGen`), with Specimen's expectations over
a generator's successes (`Specimen.Correctness.sexpect`):

* `app_sok`: the append producer succeeds surely when its size covers its list;
* `pickA_sok`: the action-ancestor picker succeeds surely when its size covers the actions built so
  far and the leaf size covers each of their ancestor lists;
* `pickA_nonempty`: under the same conditions, an action after the first gets at least one parent
  with probability at least one half;
* `pickA_empty`, `pickE_empty`: exactly, in the `dense` regime, an action with `n` actions before it,
  and an entity type with `n` standard types before it, gets no parent with probability `(3/6)^n`:
  each earlier one is a parent with probability one half, as in Cedar's own schema generator;
* `pickOne_empty`, `pickOneAction_empty`: exactly, in the `sparse` regime, a type or action with `n`
  before it gets no parent with probability `1/(n+1)`, and otherwise one, uniformly. -/

namespace Cedar.Validation.Relational.SchemaGen.Prob

open Specimen.Correctness Specimen.Backtrack Cedar.Spec

/-- The derived append producer for `AppendUID xs ys merged`, `merged` out. -/
noncomputable abbrev App := @specimen_gen_Cedar_Validation_Relational_Schema_AppendUID_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

/-- The derived picker for `PickClosedActionAncestors built ancestors`, `ancestors` out. -/
noncomputable abbrev PickA := @specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

theorem app_sok : ∀ (xs ys : List EntityUID) (fuel iS sz : Nat), xs.length ≤ sz → sz < fuel →
    sok (App fuel iS sz xs ys) = 1 := by
  intro xs
  induction xs with
  | nil =>
    intro ys fuel iS sz _ hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [App, specimen_gen_Cedar_Validation_Relational_Schema_AppendUID_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    cases sz <;> simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte] <;>
      exact sok_backtrack_one _ (by simp [sumWeights]) (by simp)
  | cons x xs ih =>
    intro ys fuel iS sz hl hf
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    rw [App, specimen_gen_Cedar_Validation_Relational_Schema_AppendUID_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte]
    refine sok_backtrack_one _ (by simp [sumWeights]) ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact sok_bind_one (ih ys f iS s (by omega) (by omega)) (fun _ => sok_pure _)

theorem pickA_sok : ∀ (b : List (EntityUID × List EntityUID)) (fuel iS sz : Nat),
    b.length ≤ sz → sz < fuel → (∀ q ∈ b, q.2.length ≤ iS) → iS < 10000 →
    sok (PickA fuel iS sz b) = 1 := by
  intro b
  induction b with
  | nil =>
    intro fuel iS sz _ hf _ _
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [PickA, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    cases sz <;> simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte,
      Bool.or_self] <;>
      exact sok_backtrack_one _ (by simp [sumWeights]) (by simp)
  | cons q b ih =>
    intro fuel iS sz hl hf hps hiS
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    obtain ⟨p, pset⟩ := q
    have ihb := ih f iS s (by omega) (by omega) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hiS
    have happ : ∀ chosen, sok (BacktrackGenFor.gen
        (P := fun merged => Cedar.Validation.Relational.Schema.AppendUID pset chosen merged)
        (G := SGen) iS iS) = 1 := fun chosen =>
      app_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _)
    rw [PickA, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte]
    refine sok_backtrack_one _ (by simp [sumWeights]) ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨sok_bind_one ihb (fun _ => sok_pure _),
      sok_bind_one ihb (fun c => sok_bind_one (happ c) (fun _ => sok_pure _))⟩

private theorem half_le (x : ENNReal) :
    1 / 2 ≤ (((3 : Nat) : ENNReal) * x + (((3 : Nat) : ENNReal) * 1 + 0)) / (((3 + (3 + 0) : Nat)) : ENNReal) := by
  have h : (1 : ENNReal) / 2 = 3 / 6 := by
    rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  rw [h]
  push_cast
  exact ENNReal.div_le_div_right (by simp) _

/-- An action after the first gets at least one parent with probability at least one half. -/
theorem pickA_nonempty (q : EntityUID × List EntityUID) (b : List (EntityUID × List EntityUID))
    (fuel iS sz : Nat) (hl : b.length < sz) (hf : sz < fuel) (hps : ∀ q' ∈ q :: b, q'.2.length ≤ iS)
    (hiS : iS < 10000) :
    1 / 2 ≤ sprob (PickA fuel iS sz (q :: b)) {xs | xs ≠ []} := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
  obtain ⟨p, pset⟩ := q
  have ihb := pickA_sok b f iS s (by omega) (by omega) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hiS
  have happ : ∀ chosen, sok (BacktrackGenFor.gen
      (P := fun merged => Cedar.Validation.Relational.Schema.AppendUID pset chosen merged)
      (G := SGen) iS iS) = 1 := fun chosen =>
    app_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _)
  unfold sprob
  rw [PickA, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte]
  refine le_trans ?_ (sexpect_backtrack_ge _ _ (by simp [sumWeights]))
  -- The pick branch's every success is a nonempty list, so it contributes its full weight.
  have hpick : ∀ (g : SGen (List EntityUID)), sok g = 1 →
      sexpect (g >>= fun chosen => BacktrackGenFor.gen
          (P := fun merged => Cedar.Validation.Relational.Schema.AppendUID pset chosen merged)
          (G := SGen) iS iS >>= fun merged => pure (p :: merged))
        ({xs : List EntityUID | xs ≠ []}.indicator 1) = 1 := by
    intro g hg
    rw [sexpect_bind]
    have : ∀ chosen, sexpect (BacktrackGenFor.gen
          (P := fun merged => Cedar.Validation.Relational.Schema.AppendUID pset chosen merged)
          (G := SGen) iS iS >>= fun merged => pure (p :: merged))
        ({xs : List EntityUID | xs ≠ []}.indicator 1) = 1 := by
      intro chosen
      rw [sexpect_bind]
      simp only [sexpect_pure, Set.indicator, Set.mem_setOf_eq, ne_eq, reduceCtorEq,
        not_false_eq_true, ↓reduceIte, Pi.one_apply]
      exact happ chosen
    simp only [this]
    exact hg
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hpick _ ihb, sumWeights,
    List.sum_cons, List.sum_nil]
  exact half_le _

/-! ## Exact: the probability of no parent -/

/-- The derived append producer for `AppendET xs ys merged`, `merged` out. -/
noncomputable abbrev AppE := @specimen_gen_Cedar_Validation_Relational_Schema_AppendET_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

/-- The derived picker for `PickClosedAncestors built ancestors` (entity types), `ancestors` out. -/
noncomputable abbrev PickE := @specimen_gen_Cedar_Validation_Relational_Schema_PickClosedAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

theorem appE_sok : ∀ (xs ys : List EntityType) (fuel iS sz : Nat), xs.length ≤ sz → sz < fuel →
    sok (AppE fuel iS sz xs ys) = 1 := by
  intro xs
  induction xs with
  | nil =>
    intro ys fuel iS sz _ hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [AppE, specimen_gen_Cedar_Validation_Relational_Schema_AppendET_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    cases sz <;> simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte] <;>
      exact sok_backtrack_one _ (by simp [sumWeights]) (by simp)
  | cons x xs ih =>
    intro ys fuel iS sz hl hf
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    rw [AppE, specimen_gen_Cedar_Validation_Relational_Schema_AppendET_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte]
    refine sok_backtrack_one _ (by simp [sumWeights]) ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    exact sok_bind_one (ih ys f iS s (by omega) (by omega)) (fun _ => sok_pure _)

theorem pickE_sok : ∀ (b : List (EntityType × List EntityType)) (fuel iS sz : Nat),
    b.length ≤ sz → sz < fuel → (∀ q ∈ b, q.2.length ≤ iS) → iS < 10000 →
    sok (PickE fuel iS sz b) = 1 := by
  intro b
  induction b with
  | nil =>
    intro fuel iS sz _ hf _ _
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [PickE, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    cases sz <;> simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte,
      Bool.or_self] <;>
      exact sok_backtrack_one _ (by simp [sumWeights]) (by simp)
  | cons q b ih =>
    intro fuel iS sz hl hf hps hiS
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    obtain ⟨p, pset⟩ := q
    have ihb := ih f iS s (by omega) (by omega) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hiS
    have happ : ∀ chosen, sok (BacktrackGenFor.gen
        (P := fun merged => Cedar.Validation.Relational.Schema.AppendET pset chosen merged)
        (G := SGen) iS iS) = 1 := fun chosen =>
      appE_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _)
    rw [PickE, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte]
    refine sok_backtrack_one _ (by simp [sumWeights]) ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨sok_bind_one ihb (fun _ => sok_pure _),
      sok_bind_one ihb (fun c => sok_bind_one (happ c) (fun _ => sok_pure _))⟩

private theorem sexpect_zero {α : Type} (g : SGen α) : sexpect g (fun _ => 0) = 0 := by
  unfold sexpect
  have : succVal (fun _ : α => (0 : ENNReal)) = fun _ => 0 := by
    funext o; rcases o with _ | _ | a <;> rfl
  rw [this, SPMF.expect_const, mul_zero]

/-- A first draw between a branch that keeps `X` and one that never does. -/
private theorem draw_arith (a b : Nat) (X : ENNReal) :
    (((a : Nat) : ENNReal) * X + (((b : Nat) : ENNReal) * 0 + 0)) / (((a + (b + 0) : Nat)) : ENNReal) =
      ((a : ENNReal) / ((a + b : Nat) : ENNReal)) * X := by
  simp only [mul_zero, add_zero]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- Exactly: an action with `n` actions before it gets no parent with probability `(3/6)^n`. -/
theorem pickA_empty : ∀ (b : List (EntityUID × List EntityUID)) (fuel iS sz : Nat),
    b.length ≤ sz → sz < fuel → (∀ q ∈ b, q.2.length ≤ iS) → iS < 10000 →
    sprob (PickA fuel iS sz b) {[]} = ((3 : ENNReal) / ((3 + 3 : Nat) : ENNReal)) ^ b.length := by
  intro b
  induction b with
  | nil =>
    intro fuel iS sz _ hf _ _
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    unfold sprob
    rw [PickA, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    cases sz <;> simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte,
      Bool.or_self] <;>
      rw [sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by simp)] <;>
      simp [sumWeights, sexpect_pure, ENNReal.div_self]
  | cons q b ih =>
    intro fuel iS sz hl hf hps hiS
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    obtain ⟨p, pset⟩ := q
    have hps' : ∀ q ∈ b, q.2.length ≤ iS := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    have ihb := pickA_sok b f iS s (by omega) (by omega) hps' hiS
    have happ : ∀ chosen, sok (BacktrackGenFor.gen
        (P := fun merged => Cedar.Validation.Relational.Schema.AppendUID pset chosen merged)
        (G := SGen) iS iS) = 1 := fun chosen =>
      app_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _)
    have ihe := ih f iS s (by omega) (by omega) hps' hiS
    unfold sprob at ihe ⊢
    rw [PickA, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte]
    rw [sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨sok_bind_one ihb (fun _ => sok_pure _),
        sok_bind_one ihb (fun c => sok_bind_one (happ c) (fun _ => sok_pure _))⟩)]
    -- skip keeps the rest's probability; pick never yields `[]`.
    have hskip : sexpect (PickA f iS s b >>= fun x => pure x) (({[]} : Set (List EntityUID)).indicator 1) =
        ((3 : ENNReal) / ((3 + 3 : Nat) : ENNReal)) ^ b.length := by
      rw [sexpect_bind]; simp only [sexpect_pure]; exact ihe
    have hpick : ∀ (g : SGen (List EntityUID)), sexpect (g >>= fun chosen => BacktrackGenFor.gen
          (P := fun merged => Cedar.Validation.Relational.Schema.AppendUID pset chosen merged)
          (G := SGen) iS iS >>= fun merged => pure (p :: merged))
        (({[]} : Set (List EntityUID)).indicator 1) = 0 := by
      intro g
      rw [sexpect_bind]
      have : ∀ chosen, sexpect (BacktrackGenFor.gen
            (P := fun merged => Cedar.Validation.Relational.Schema.AppendUID pset chosen merged)
            (G := SGen) iS iS >>= fun merged => pure (p :: merged))
          (({[]} : Set (List EntityUID)).indicator 1) = 0 := by
        intro chosen
        rw [sexpect_bind]
        have hz : (fun merged : List EntityUID =>
            sexpect (pure (p :: merged) : SGen _) (({[]} : Set (List EntityUID)).indicator 1)) =
            fun _ => 0 := by
          funext m; simp [sexpect_pure, Set.indicator]
        rw [hz, sexpect_zero]
      simp only [this]
      exact sexpect_zero g
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sumWeights]
    rw [hskip, hpick, draw_arith, List.length_cons, pow_succ, mul_comm, Nat.cast_ofNat]

/-- Exactly: in the `dense` regime, an entity type with `n` standard types before it gets no parent
    with probability `(3/6)^n`. -/
theorem pickE_empty : ∀ (b : List (EntityType × List EntityType)) (fuel iS sz : Nat),
    b.length ≤ sz → sz < fuel → (∀ q ∈ b, q.2.length ≤ iS) → iS < 10000 →
    sprob (PickE fuel iS sz b) {[]} = ((3 : ENNReal) / ((3 + 3 : Nat) : ENNReal)) ^ b.length := by
  intro b
  induction b with
  | nil =>
    intro fuel iS sz _ hf _ _
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    unfold sprob
    rw [PickE, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    cases sz <;> simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte,
      Bool.or_self] <;>
      rw [sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by simp)] <;>
      simp [sumWeights, sexpect_pure, ENNReal.div_self]
  | cons q b ih =>
    intro fuel iS sz hl hf hps hiS
    simp only [List.length_cons] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
    obtain ⟨p, pset⟩ := q
    have hps' : ∀ q ∈ b, q.2.length ≤ iS := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    have ihb := pickE_sok b f iS s (by omega) (by omega) hps' hiS
    have happ : ∀ chosen, sok (BacktrackGenFor.gen
        (P := fun merged => Cedar.Validation.Relational.Schema.AppendET pset chosen merged)
        (G := SGen) iS iS) = 1 := fun chosen =>
      appE_sok pset chosen (iS + 1) iS iS (hps _ List.mem_cons_self) (Nat.lt_succ_self _)
    have ihe := ih f iS s (by omega) (by omega) hps' hiS
    unfold sprob at ihe ⊢
    rw [PickE, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte]
    rw [sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨sok_bind_one ihb (fun _ => sok_pure _),
        sok_bind_one ihb (fun c => sok_bind_one (happ c) (fun _ => sok_pure _))⟩)]
    -- skip keeps the rest's probability; pick never yields `[]`.
    have hskip : sexpect (PickE f iS s b >>= fun x => pure x) (({[]} : Set (List EntityType)).indicator 1) =
        ((3 : ENNReal) / ((3 + 3 : Nat) : ENNReal)) ^ b.length := by
      rw [sexpect_bind]; simp only [sexpect_pure]; exact ihe
    have hpick : ∀ (g : SGen (List EntityType)), sexpect (g >>= fun chosen => BacktrackGenFor.gen
          (P := fun merged => Cedar.Validation.Relational.Schema.AppendET pset chosen merged)
          (G := SGen) iS iS >>= fun merged => pure (p :: merged))
        (({[]} : Set (List EntityType)).indicator 1) = 0 := by
      intro g
      rw [sexpect_bind]
      have : ∀ chosen, sexpect (BacktrackGenFor.gen
            (P := fun merged => Cedar.Validation.Relational.Schema.AppendET pset chosen merged)
            (G := SGen) iS iS >>= fun merged => pure (p :: merged))
          (({[]} : Set (List EntityType)).indicator 1) = 0 := by
        intro chosen
        rw [sexpect_bind]
        have hz : (fun merged : List EntityType =>
            sexpect (pure (p :: merged) : SGen _) (({[]} : Set (List EntityType)).indicator 1)) =
            fun _ => 0 := by
          funext m; simp [sexpect_pure, Set.indicator]
        rw [hz, sexpect_zero]
      simp only [this]
      exact sexpect_zero g
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sumWeights]
    rw [hskip, hpick, draw_arith, List.length_cons, pow_succ, mul_comm, Nat.cast_ofNat]

/-! ## Exact: the `sparse` regime -/

theorem pickOne_empty (built : List (EntityType × List EntityType)) (sz iS : Nat) :
    sprob (BacktrackGenFor.gen (P := fun ancestors => PickOneAncestor built ancestors)
      (G := SGen) sz iS) {[]} = 1 / ((built.length + 1 : Nat) : ENNReal) := by
  unfold sprob
  simp only [BacktrackGenFor.gen]
  rw [sexpect_bind, sexpect_chooseNat, Finset.sum_eq_single 0]
  · simp [sexpect_pure, Set.indicator]
  · intro i _ hi
    simp only [hi, ↓reduceIte]
    split
    · simp [sexpect_pure, Set.indicator]
    · exact sexpect_refute _
  · simp

theorem pickOneAction_empty (built : List (EntityUID × List EntityUID)) (sz iS : Nat) :
    sprob (BacktrackGenFor.gen (P := fun ancestors => PickOneActionAncestor built ancestors)
      (G := SGen) sz iS) {[]} = 1 / ((built.length + 1 : Nat) : ENNReal) := by
  unfold sprob
  simp only [BacktrackGenFor.gen]
  rw [sexpect_bind, sexpect_chooseNat, Finset.sum_eq_single 0]
  · simp [sexpect_pure, Set.indicator]
  · intro i _ hi
    simp only [hi, ↓reduceIte]
    split
    · simp [sexpect_pure, Set.indicator]
    · exact sexpect_refute _
  · simp

end Cedar.Validation.Relational.SchemaGen.Prob

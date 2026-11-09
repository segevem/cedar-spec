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

import CedarGen.Relational.SchemaGenProb
import Specimen.Correctness.WalkSGenExpect
import Specimen.Correctness.CondMean
import Specimen.Correctness.SureLaws

/-! # Variety of request environments

The schema generator's request environments are bounded by its budget (`genTypeEnvB_iff`); this file
shows they are not degenerate: the request action has two distinct principals, and so at least two
request environments, with probability bounded below, proved of the derived code at `SGen`. -/

namespace Cedar.Validation.Relational.SchemaGen.Variety

open Specimen.Correctness Specimen.Backtrack Cedar.Spec

/-- The hand-written picker for `DefinedEntityType ets`: uniform over `ets`. -/
noncomputable abbrev Pick (ets : List EntityType) (i j : Nat) : SGen EntityType :=
  BacktrackGenFor.gen (P := fun et => Cedar.Validation.Relational.Schema.DefinedEntityType ets et)
    (G := SGen) i j

/-- The picker's expectation: the average over `ets`. -/
theorem pick_sexpect (ets : List EntityType) (i j : Nat) (h : ets ≠ []) (f : EntityType → ENNReal) :
    sexpect (Pick ets i j) f =
      (∑ k ∈ Finset.Icc 0 (ets.length - 1), (ets[k]?.elim 0 f)) / ((ets.length - 1 - 0 + 1 : ℕ) : ENNReal) := by
  unfold Pick BacktrackGenFor.gen instBacktrackGenForEntityTypeDefinedEntityType_cedarGen
  simp only [List.isEmpty_iff, h, ↓reduceIte]
  rw [sexpect_bind, sexpect_chooseNat]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  cases ets[k]? with
  | none =>
    simpa [Specimen.Fail.fail, Specimen.refute, sexpect] using
      sexpect_refute (A := EntityType) f
  | some et => simp [Option.elim, sexpect, succVal]

/-- Over distinct types, all indices but at most one miss a given type. -/
theorem count_ne (ets : List EntityType) (hd : ets.Nodup) (h : ets ≠ []) (c : EntityType) :
    ets.length - 1 ≤ ∑ k ∈ Finset.Icc 0 (ets.length - 1), (ets[k]?.elim 0 (fun y => if y = c then 0 else 1) : ℕ) := by
  have hn : 0 < ets.length := List.length_pos_iff.mpr h
  set S := Finset.Icc 0 (ets.length - 1)
  have hS : ∀ k ∈ S, k < ets.length := fun k hk => by simp [S] at hk; omega
  -- the indices that hit `c`: at most one, as `ets` has no duplicates
  have hone : (S.filter fun k => ets[k]? = some c).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    have ha' := hS a ha.1; have hb' := hS b hb.1
    rw [List.getElem?_eq_getElem ha'] at ha
    rw [List.getElem?_eq_getElem hb'] at hb
    simp only [Option.some.injEq] at ha hb
    exact (hd.getElem_inj_iff (hi := ha') (hj := hb')).mp (ha.2.trans hb.2.symm)
  have hsum : ∑ k ∈ S, (ets[k]?.elim 0 (fun y => if y = c then 0 else 1) : ℕ) =
      (S.filter fun k => ¬ ets[k]? = some c).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := hS k hk
    rw [List.getElem?_eq_getElem hk']
    by_cases e : ets[k] = c <;> simp [e, Option.elim]
  have hcard : S.card = ets.length := by simp [S]; omega
  have := Finset.card_filter_add_card_filter_not (s := S) (fun k => ets[k]? = some c)
  rw [hsum]; omega

theorem sexpect_add {A : Type} (g : SGen A) (f h : A → ENNReal) :
    sexpect g (fun a => f a + h a) = sexpect g f + sexpect g h := by
  unfold sexpect
  rw [show succVal (fun a => f a + h a) = fun o => succVal f o + succVal h o from
    funext fun o => by rcases o with _ | _ | a <;> simp [succVal], SPMF.expect_add]

theorem sexpect_zero {A : Type} (g : SGen A) : sexpect g (fun _ => 0) = 0 := by
  simpa using sexpect_mul_left g 0 (fun _ => 1)

theorem sexpect_sum {A ι : Type} (S : Finset ι) (g : SGen A) (F : ι → A → ENNReal) :
    sexpect g (fun a => ∑ i ∈ S, F i a) = ∑ i ∈ S, sexpect g (F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using sexpect_zero g
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [sexpect_add, ih]

/-- **A uniform draw then misses what follows it.** Draw `y` uniformly from distinct types, then run
`x`: the type `x` produces first differs from `y` with probability at least `1 - 1/n` of `x`'s
success, whatever `x`'s distribution. So a continuation that succeeds surely into an event when they
differ reaches it with at least that probability. -/
theorem pick_miss {β γ : Type} (ets : List EntityType) (i j : Nat) (hd : ets.Nodup) (h : ets ≠ [])
    (x : SGen (EntityType × β)) (K : EntityType → EntityType × β → SGen γ) (f : γ → ENNReal)
    (hK : ∀ y r, y ≠ r.1 → 1 ≤ sexpect (K y r) f) :
    (((ets.length - 1 : ℕ) : ENNReal) * sok x) / (ets.length : ENNReal) ≤
      sexpect (Pick ets i j >>= fun y => x >>= K y) f := by
  have hn : 0 < ets.length := List.length_pos_iff.mpr h
  rw [sexpect_bind, pick_sexpect ets i j h]
  have hlen : (ets.length - 1 - 0 + 1 : ℕ) = ets.length := by omega
  rw [hlen]
  gcongr
  -- each draw's contribution, at least `x`'s chance of differing from it
  have per : ∀ y, sexpect x (fun r => if y = r.1 then 0 else 1) ≤ sexpect (x >>= K y) f := by
    intro y
    rw [sexpect_bind]
    refine sexpect_mono _ fun r => ?_
    by_cases e : y = r.1
    · simp [e]
    · simpa [e] using hK y r e
  calc ((ets.length - 1 : ℕ) : ENNReal) * sok x
      = sexpect x (fun _ => ((ets.length - 1 : ℕ) : ENNReal)) := by
        rw [sok, ← sexpect_mul_left]; simp
    _ ≤ sexpect x (fun r => ∑ k ∈ Finset.Icc 0 (ets.length - 1),
          ets[k]?.elim 0 (fun y => if y = r.1 then 0 else 1)) := by
        refine sexpect_mono _ fun r => ?_
        have := count_ne ets hd h r.1
        have hc : ((∑ k ∈ Finset.Icc 0 (ets.length - 1),
            (ets[k]?.elim 0 (fun y => if y = r.1 then 0 else 1) : ℕ) : ℕ) : ENNReal) =
            ∑ k ∈ Finset.Icc 0 (ets.length - 1),
              ets[k]?.elim 0 (fun y => if y = r.1 then (0 : ENNReal) else 1) := by
          push_cast
          refine Finset.sum_congr rfl fun k _ => ?_
          cases ets[k]? <;> simp [Option.elim]
        rw [← hc]; exact_mod_cast this
    _ = ∑ k ∈ Finset.Icc 0 (ets.length - 1),
          sexpect x (fun r => ets[k]?.elim 0 (fun y => if y = r.1 then 0 else 1)) := sexpect_sum _ _ _
    _ ≤ ∑ k ∈ Finset.Icc 0 (ets.length - 1), ets[k]?.elim 0 (fun y => sexpect (x >>= K y) f) := by
        refine Finset.sum_le_sum fun k _ => ?_
        cases ets[k]? with
        | none => simpa using (sexpect_zero x).le
        | some y => exact per y

theorem pick_sok (ets : List EntityType) (i j : Nat) (h : ets ≠ []) : sok (Pick ets i j) = 1 := by
  have hn : 0 < ets.length := List.length_pos_iff.mpr h
  rw [sok, pick_sexpect ets i j h]
  have : ∑ k ∈ Finset.Icc 0 (ets.length - 1), (ets[k]?.elim 0 (fun _ => (1 : ENNReal))) =
      ((ets.length - 1 - 0 + 1 : ℕ) : ENNReal) := by
    rw [show (ets.length - 1 - 0 + 1 : ℕ) = (Finset.Icc 0 (ets.length - 1)).card by simp]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    rw [List.getElem?_eq_getElem (by omega)]; simp [Option.elim]
  rw [this, ENNReal.div_self (by simp) (by simp)]

/-- A generator that loses no mass: it succeeds or fails, surely. -/
theorem total_bind {A B : Type} {g : SGen A} {k : A → SGen B} (hg : sok g + sfail g = 1)
    (hk : ∀ a, sok (k a) + sfail (k a) = 1) : sok (g >>= k) + sfail (g >>= k) = 1 := by
  rw [sok_bind, sfail_bind, add_comm (sfail g), ← add_assoc, ← sexpect_add]
  simp only [hk]
  exact hg

/-- The derived generator for `BoundedTypes ets n xs`, `xs` out. -/
noncomputable abbrev BT := @specimen_gen_Cedar_Validation_Relational_SchemaGen_BoundedTypes_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

/-- The derived generator for `ContainsBounded ets n x xs`, `x` and `xs` out. -/
noncomputable abbrev CB := @specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

theorem bt_sok : ∀ (sz fuel iS : Nat) (ets : List EntityType) (b : Nat), ets ≠ [] → sz < fuel →
    sok (BT fuel iS sz ets b) = 1 := by
  intro sz
  induction sz with
  | zero =>
    intro fuel iS ets b hne hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [BT, specimen_gen_Cedar_Validation_Relational_SchemaGen_BoundedTypes_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    cases b with
    | zero =>
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte]
      exact sok_backtrack_one _ (by simp [sumWeights]) (by simp)
    | succ n =>
      simp only [List.filterMap_cons, List.filterMap_nil, ↓reduceIte]
      refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, sok_pure _⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨total_of_sok (sok_pure _), total_truncations _⟩
  | succ s ih =>
    intro fuel iS ets b hne hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [BT, specimen_gen_Cedar_Validation_Relational_SchemaGen_BoundedTypes_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    cases b with
    | zero =>
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte]
      exact sok_backtrack_one _ (by simp [sumWeights]) (by simp)
    | succ n =>
      simp only [List.filterMap_cons, List.filterMap_nil, ↓reduceIte]
      refine sok_backtrack_one _ (by simp [sumWeights]) ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨sok_pure _, sok_bind_one (pick_sok ets iS iS hne)
        (fun _ => sok_bind_one (ih f iS ets n hne (by omega)) (fun _ => sok_pure _))⟩

theorem total_backtrack_nil {A : Type} :
    sok (Specimen.Backtrack.backtrack ([] : List (Nat × (Unit → SGen A)))) +
      sfail (Specimen.Backtrack.backtrack ([] : List (Nat × (Unit → SGen A)))) = 1 := by
  simp [sok, sfail, sexpect, Specimen.Backtrack.backtrack, searchWith, Specimen.Backtrack.finish,
    OptionT.run_failure, SPMF.expect_pure, failVal, succVal]

/-- With no budget, nothing to produce: the search is empty, and fails surely. -/
theorem cb_total_zero (fuel iS sz : Nat) (ets : List EntityType) :
    sok (CB fuel iS sz ets 0) + sfail (CB fuel iS sz ets 0) = 1 := by
  rw [CB, specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases fuel with _ | f
  · exact total_failWith _
  · rcases sz with _ | s <;>
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte] <;>
      exact total_backtrack_nil

theorem total_refute {A : Type} : sok (Specimen.refute : SGen A) + sfail (Specimen.refute : SGen A) = 1 := by
  simp [sok, sfail, sexpect, Specimen.Fail.fail, Specimen.refute, ExceptT.lift, OptionT.run_failure,
    SPMF.expect_pure, failVal, succVal]

/-- The `here` branch: the principal, then any other principals; it never fails. -/
theorem cb_here_sok (iS : Nat) (ets : List EntityType) (n : Nat) (hne : ets ≠ []) :
    sok (do
      let c ← Pick ets iS iS
      let xs ← BacktrackGenFor.gen (P := fun xs => BoundedTypes ets n xs) (G := SGen) iS iS
      pure (c, c :: xs)) = 1 :=
  sok_bind_one (pick_sok ets iS iS hne)
    (fun _ => sok_bind_one (bt_sok iS (iS + 1) iS ets n hne (by omega)) (fun _ => sok_pure _))

theorem cb_sok : ∀ (sz fuel iS : Nat) (ets : List EntityType) (b : Nat), ets ≠ [] → 1 ≤ b →
    sz < fuel → sok (CB fuel iS sz ets b) = 1 := by
  intro sz
  induction sz with
  | zero =>
    intro fuel iS ets b hne hb hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [CB, specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    simp only [List.filterMap_cons, List.filterMap_nil, ↓reduceIte]
    refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, cb_here_sok iS ets n hne⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨total_of_sok (cb_here_sok iS ets n hne), total_truncations _⟩
  | succ s ih =>
    intro fuel iS ets b hne hb hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    have hrec : sok (CB f iS s ets n) + sfail (CB f iS s ets n) = 1 := by
      rcases n with _ | m
      · exact cb_total_zero f iS s ets
      · exact total_of_sok (ih f iS ets (m + 1) hne (by omega) (by omega))
    rw [CB, specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    simp only [List.filterMap_cons, List.filterMap_nil, ↓reduceIte]
    refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, cb_here_sok iS ets n hne⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨total_of_sok (cb_here_sok iS ets n hne), ?_⟩
    refine total_bind (total_of_sok (pick_sok ets iS iS hne)) fun y => total_bind hrec fun r => ?_
    obtain ⟨c, xs⟩ := r
    dsimp only
    split
    · exact total_of_sok (sok_pure _)
    · exact total_refute
    · exact total_failWith _

/-- **The request's principals are varied.** With a budget of at least two environments, distinct
entity types, and size to recurse, `ContainsBounded` gives the request a principal list holding some
type other than the request's principal (so at least two principals, and two request environments)
with probability at least `5/9 · (1 - 1/n)`: the `there` branch's share of the weight, times a fresh
uniform type's chance of differing from the principal. -/
theorem cb_variety (sz fuel iS : Nat) (ets : List EntityType) (b : Nat) (hd : ets.Nodup)
    (hne : ets ≠ []) (hb : 2 ≤ b) (hsz : 1 ≤ sz) (hf : sz < fuel) :
    5 * ((((ets.length - 1 : ℕ) : ENNReal) * 1) / (ets.length : ENNReal)) / 9 ≤
      sprob (CB fuel iS sz ets b) {p | ∃ z ∈ p.2, z ≠ p.1} := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, sz = s + 1 := ⟨sz - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  have hrec : sok (CB f iS s ets n) = 1 := cb_sok s f iS ets n hne (by omega) (by omega)
  unfold sprob
  rw [CB, specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  simp only [List.filterMap_cons, List.filterMap_nil, ↓reduceIte]
  refine le_trans ?_ (sexpect_backtrack_ge _ _ (by simp [sumWeights]))
  have hthere := pick_miss ets iS iS hd hne (CB f iS s ets n)
    (fun y r => match DecOpt.negOpt (DecOpt.decOpt (r.1 = y) iS) with
        | Except.ok true => pure (r.1, y :: r.2)
        | Except.ok false => Specimen.refute
        | _ => Specimen.inconclusive)
    ({p : EntityType × List EntityType | ∃ z ∈ p.2, z ≠ p.1}.indicator 1) ?_
  · rw [hrec] at hthere
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sumWeights, add_zero]
    refine ENNReal.div_le_div (le_trans (mul_le_mul_right hthere 5) le_add_self) (by norm_num)
  · intro y r hy
    have hne' : ¬ r.1 = y := fun h => hy h.symm
    simp [DecOpt.negOpt, DecOpt.decOpt, hne', sexpect_pure, Set.indicator, hy]

end Cedar.Validation.Relational.SchemaGen.Variety

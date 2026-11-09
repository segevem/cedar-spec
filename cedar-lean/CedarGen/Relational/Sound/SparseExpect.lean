import CedarGen.Relational.SchemaGen
import Specimen.Correctness.CondMean
import Specimen.Correctness.StepOf
import Mathlib.NumberTheory.Harmonic.Bounds

/-! In the sparse regime, the mean closure is logarithmic. -/

namespace Cedar.Validation.Relational.SchemaGen.Sound

open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Specimen.Correctness Basalt ENNReal

local notation "SGenA" => (SGen (List EntityType))

/-- The sparse ancestors of a built list. -/
noncomputable abbrev ancGen (B : List (EntityType × List EntityType)) (s l : Nat) : SGenA :=
  BacktrackGenFor.gen (P := fun a => Ancestors .sparse B a) (G := SGen) s l

#specimen_body specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen

theorem ancGen_eq (B : List (EntityType × List EntityType)) (s l : Nat) :
    ancGen B s l = Specimen.Backtrack.backtrack
      [(4, fun _ => BacktrackGenFor.gen (P := fun a => PickOneAncestor B a) (G := SGen) l l)] := by
  unfold ancGen
  unfold_gen_instances []
  rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_body]
  delta specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.body
  cases s <;> simp

/-- The sparse pick. -/
noncomputable abbrev pickOne (B : List (EntityType × List EntityType)) (s l : Nat) : SGenA :=
  BacktrackGenFor.gen (P := fun a => PickOneAncestor B a) (G := SGen) s l

theorem pickOne_eq (B : List (EntityType × List EntityType)) (s l : Nat) :
    pickOne B s l = (do
      let i ← chooseNat 0 B.length
      if i = 0 then pure [] else
      match B[i - 1]? with
      | some (p, pset) => pure (p :: pset)
      | none => Specimen.Fail.fail : SGenA) := rfl

/-- Indices `1 … n` of a list are its entries. -/
theorem sum_range_getElem? {β : Type} (f : β → ℝ≥0∞) : ∀ (B : List β),
    ∑ i ∈ Finset.range B.length, (match B[i]? with | some b => f b | none => 0) = (B.map f).sum
  | [] => by simp
  | b :: B => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
    rw [sum_range_getElem? f B]

/-- **The sparse pick, on average:** no parent, or each built type with its closure, uniformly. -/
theorem sexpect_pickOne (B : List (EntityType × List EntityType)) (s l : Nat) (φ : List EntityType → ℝ≥0∞) :
    sexpect (pickOne B s l) φ = (φ [] + (B.map fun q => φ (q.1 :: q.2)).sum) / (B.length + 1 : ℕ) := by
  rw [pickOne_eq, sexpect_bind, sexpect_chooseNat]
  congr 1
  · rw [show Finset.Icc 0 B.length = Finset.range (B.length + 1) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_range]; omega,
      Finset.sum_range_succ', ← sum_range_getElem? (fun q => φ (q.1 :: q.2)) B]
    simp only [ite_true, sexpect_pure, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    cases B[i]? with
    | none => simp
    | some q => simp [sexpect_pure]

theorem sok_pickOne (B : List (EntityType × List EntityType)) (s l : Nat) : sok (pickOne B s l) = 1 := by
  unfold sok
  rw [sexpect_pickOne]
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]
  rw [Nat.cast_add, Nat.cast_one, add_comm]
  exact ENNReal.div_self (by simp) (by simp)

theorem sfail_pickOne (B : List (EntityType × List EntityType)) (s l : Nat) : sfail (pickOne B s l) = 0 :=
  sfail_eq_zero_of_sok (sok_pickOne B s l)

theorem sexpect_ancGen (B : List (EntityType × List EntityType)) (s l : Nat) (φ : List EntityType → ℝ≥0∞) :
    sexpect (ancGen B s l) φ = sexpect (pickOne B l l) φ := by
  rw [ancGen_eq, sexpect_backtrack_eq _ _ (by simp [Specimen.Backtrack.sumWeights])
    (by simp only [List.mem_singleton]; rintro p rfl; exact sok_pickOne B l l)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Specimen.Backtrack.sumWeights]
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right (by simp) (by simp)

theorem sok_ancGen (B : List (EntityType × List EntityType)) (s l : Nat) : sok (ancGen B s l) = 1 := by
  unfold sok; rw [sexpect_ancGen]; exact sok_pickOne B l l

theorem sfail_ancGen (B : List (EntityType × List EntityType)) (s l : Nat) : sfail (ancGen B s l) = 0 :=
  sfail_eq_zero_of_sok (sok_ancGen B s l)

/-! ## The entity list's chance of success does not depend on the ancestors built -/

#specimen_body specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen

local notation "WE" => specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen (G := SGen)

/-- In the sparse regime, the entity list succeeds and fails as often from any built list. -/
theorem entities_profile (iS : Nat) : ∀ (fuel size : Nat) (B B' : List (EntityType × List EntityType))
    (names : List EntityType),
    SameProfile (WE fuel iS size .sparse B names) (WE fuel iS size .sparse B' names)
  | 0, _, _, _, _ => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_1,
      specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_1]
    exact sameProfile_refl _
  | fuel + 1, size, B, B', names => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_body,
      specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_body]
    delta specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.body
    cases size with
    | zero => exact sameProfile_refl _
    | succ size' =>
      refine sameProfile_backtrack (.cons ⟨rfl, sameProfile_refl _⟩ (.cons ⟨rfl, ?_⟩ (.cons ⟨rfl, ?_⟩ .nil)))
      · refine sameProfile_bind fun et => sameProfile_bind fun attrs => sameProfile_bind fun tags => ?_
        refine sameProfile_bind_uniform
          ⟨by rw [sok_ancGen, sok_ancGen], by rw [sfail_ancGen, sfail_ancGen]⟩ fun anc anc' => ?_
        refine sameProfile_bind_uniform (entities_profile iS fuel size' _ _ _) fun ⟨d, rest⟩ ⟨d', rest'⟩ => ?_
        exact ⟨by simp, by simp⟩
      · refine sameProfile_bind fun et => ?_
        refine sameProfile_bind_uniform (entities_profile iS fuel size' B B' _) fun ⟨d, rest⟩ ⟨d', rest'⟩ => ?_
        exact ⟨by rw [sok_bind, sok_bind]; simp, by rw [sfail_bind, sfail_bind]; simp⟩

/-! ## The mean closure -/

/-- What the standard entries of an entity list add: their closures, each with its type, and their
number. -/
def stdStats : List (EntityType × EntitySchemaEntry) → ℕ × ℕ
  | [] => (0, 0)
  | (_, .standard e) :: rest => ((stdStats rest).1 + (1 + e.ancestors.elts.length), (stdStats rest).2 + 1)
  | (_, .enum _) :: rest => stdStats rest

/-- A built list's closures, each with its type. -/
def closureSum (B : List (EntityType × List EntityType)) : ℕ := (B.map fun q => 1 + q.2.length).sum

/-- The potential: the mean of `S` over `m` types and one more, and what the types still to come
add to the harmonic series, up to `N`. -/
noncomputable def Φ (S m N : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((S : ℝ) / (m + 1) + ∑ j ∈ Finset.Ioc (m + 1) (N + 1), (1 : ℝ) / j)

/-- The potential at the end of the entity list, from a built list `B`. -/
noncomputable def ΦOut (B : List (EntityType × List EntityType)) (N : ℕ)
    (out : List EntityType × List (EntityType × EntitySchemaEntry)) : ℝ≥0∞ :=
  Φ (closureSum B + (stdStats out.2).1) (B.length + (stdStats out.2).2) N

theorem ofReal_list_sum {β : Type} (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) : ∀ l : List β,
    (l.map fun b => ENNReal.ofReal (f b)).sum = ENNReal.ofReal (l.map f).sum
  | [] => by simp
  | b :: l => by
    rw [List.map_cons, List.sum_cons, ofReal_list_sum f hf l, List.map_cons, List.sum_cons,
      ENNReal.ofReal_add (hf b) (List.sum_nonneg fun x hx => by
        obtain ⟨b', -, rfl⟩ := List.mem_map.mp hx; exact hf b')]

/-- The harmonic tail from `m + 2`, its first term out. -/
theorem harmonic_tail (m N : ℕ) (h : m + 1 ≤ N) :
    ∑ j ∈ Finset.Ioc (m + 1) (N + 1), (1 : ℝ) / j =
      1 / ((m : ℝ) + 2) + ∑ j ∈ Finset.Ioc (m + 1 + 1) (N + 1), (1 : ℝ) / j := by
  rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ (m + 1)) (by omega), Nat.Ioc_succ_singleton,
    Finset.sum_singleton]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one]; ring

theorem T_nonneg (m N : ℕ) : 0 ≤ ∑ j ∈ Finset.Ioc (m + 1) (N + 1), (1 : ℝ) / j :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem Φ_nonneg (S m N : ℕ) : 0 ≤ (S : ℝ) / (m + 1) + ∑ j ∈ Finset.Ioc (m + 1) (N + 1), (1 : ℝ) / j :=
  add_nonneg (by positivity) (T_nonneg m N)

/-- The closures' lengths. -/
def closureLen (B : List (EntityType × List EntityType)) : ℕ := (B.map fun q => q.2.length).sum

theorem closureSum_cons (q : EntityType × List EntityType) (B : List (EntityType × List EntityType)) :
    closureSum (q :: B) = 1 + q.2.length + closureSum B := by simp [closureSum]

theorem closureLen_cons (q : EntityType × List EntityType) (B : List (EntityType × List EntityType)) :
    closureLen (q :: B) = q.2.length + closureLen B := by simp [closureLen]

theorem closureSum_eq (B : List (EntityType × List EntityType)) : closureSum B = B.length + closureLen B := by
  induction B with
  | nil => rfl
  | cons q B ih => simp only [closureSum, closureLen, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

theorem sum_map_affine (c : ℕ) (d T : ℝ) : ∀ B : List (EntityType × List EntityType),
    (B.map fun q => (((c + q.2.length : ℕ) : ℝ) / d + T)).sum =
      ((B.length * c + closureLen B : ℕ) : ℝ) / d + B.length * T
  | [] => by simp [closureLen]
  | q :: B => by
    rw [List.map_cons, List.sum_cons, sum_map_affine c d T B, closureLen_cons, List.length_cons]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring

/-- **The potential is a martingale under the sparse pick.** -/
theorem Φ_pick (et : EntityType) (B : List (EntityType × List EntityType)) (N : ℕ) (h : B.length + 1 ≤ N) :
    (Φ (closureSum ((et, []) :: B)) (B.length + 1) N +
        (B.map fun q => Φ (closureSum ((et, q.1 :: q.2) :: B)) (B.length + 1) N).sum) /
      (B.length + 1 : ℕ) = Φ (closureSum B) B.length N := by
  set T1 := ∑ j ∈ Finset.Ioc (B.length + 1 + 1) (N + 1), (1 : ℝ) / j
  have hB : (B.map fun q => Φ (closureSum ((et, q.1 :: q.2) :: B)) (B.length + 1) N) =
      B.map fun q => ENNReal.ofReal
        ((((2 + closureSum B) + q.2.length : ℕ) : ℝ) / ((B.length + 1 : ℕ) + 1) + T1) := by
    refine List.map_congr_left fun q _ => ?_
    simp only [Φ, closureSum, List.map_cons, List.sum_cons, List.length_cons, T1]
    congr 4; omega
  rw [hB, ofReal_list_sum _ (fun q => add_nonneg (by positivity) (T_nonneg _ _)), sum_map_affine]
  simp only [Φ]
  rw [← ENNReal.ofReal_add (Φ_nonneg _ _ _) (add_nonneg (by positivity) (mul_nonneg (by positivity) (T_nonneg _ _))),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  rw [harmonic_tail _ _ h]
  rw [closureSum_cons, closureSum_eq]
  simp only [List.length_nil, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero]
  field_simp
  ring

theorem entities_meanLe (iS N : Nat) : ∀ (fuel size : Nat) (B : List (EntityType × List EntityType))
    (names : List EntityType), B.length + size ≤ N →
    MeanLe (WE fuel iS size .sparse B names) (ΦOut B N) (Φ (closureSum B) B.length N)
  | 0, _, _, _, _ => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_1]
    unfold MeanLe; rw [sexpect_outOfFuel]; exact zero_le
  | fuel + 1, size, B, names, hN => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_body]
    delta specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.body
    have hnil : ∀ B : List (EntityType × List EntityType), ΦOut B N (names, []) = Φ (closureSum B) B.length N :=
      fun B => by simp [ΦOut, stdStats]
    cases size with
    | zero =>
      refine meanLe_backtrack fun p hp => ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact meanLe_pure (hnil B).le
      · dsimp only; exact meanLe_truncations
    | succ size' =>
      refine meanLe_backtrack fun p hp => ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact meanLe_pure (hnil B).le
      · -- a standard type: its name, attributes and tags, then its ancestors
        refine meanLe_bind_const fun et => meanLe_bind_const fun attrs => meanLe_bind_const fun tags => ?_
        refine meanLe_bind_uniform (c := fun anc => Φ (closureSum ((et, anc) :: B)) (B.length + 1) N)
          (q := sok (WE fuel iS size' .sparse [] (et :: names))) (fun anc => ?_) (fun anc => ?_) ?_
        · refine meanLe_bind_uniform (q := 1)
            (c := ΦOut ((et, anc) :: B) N) (fun ⟨d, rest⟩ => meanLe_pure ?_) (fun ⟨d, rest⟩ => by simp) ?_
          · simp only [ΦOut, stdStats, closureSum, List.map_cons, List.sum_cons, List.length_cons]
            exact le_of_eq (congrArg₂ (Φ · · N) (by simp only [Cedar.Data.Set.elts]; omega) (by omega))
          · exact entities_meanLe iS N fuel size' _ _ (by simp only [List.length_cons]; omega)
        · rw [sok_bind, sexpect_congr _ (f' := fun _ => 1) (fun ⟨d, rest⟩ => by simp)]
          exact (entities_profile iS fuel size' _ [] _).1
        · unfold MeanLe
          rw [sok_ancGen, mul_one, sexpect_ancGen, sexpect_pickOne]
          exact (Φ_pick et B N (by omega)).le
      · -- an enumerated type: its name, the rest, then its entities
        refine meanLe_bind_const fun et => ?_
        refine meanLe_bind_uniform (c := ΦOut B N)
          (q := sok (Basalt.ArbitrarySized.arbitrarySized iS : SGen (List String)))
          (fun ⟨d, rest⟩ => meanLe_bind_const fun eids =>
          meanLe_pure (le_of_eq (by simp [ΦOut, stdStats]))) (fun ⟨d, rest⟩ => ?_)
          (entities_meanLe iS N fuel size' B _ (by omega))
        rw [sok_bind]; simp only [sok_pure']; rfl

theorem harmonic_tail_one : ∀ n : ℕ, ∑ j ∈ Finset.Ioc 1 (n + 1), (1 : ℝ) / j = (harmonic (n + 1) : ℝ) - 1
  | 0 => by simp [harmonic]
  | n + 1 => by
    rw [Finset.sum_Ioc_succ_top (by omega), harmonic_tail_one n, harmonic_succ (n + 1), Rat.cast_add,
      Rat.cast_inv, Rat.cast_natCast]
    ring

/-- **Claim 2, in expectation.** In the sparse regime, from no types, the mean over the standard entity
types of each one's closure with itself, with one more type in the count, is over the generator's
successes at most `H(size + 1) - 1`: logarithmic in the size. -/
theorem sparse_mean_closure (fuel iS size : ℕ) (names : List EntityType) :
    MeanLe (WE fuel iS size .sparse [] names)
      (fun out => ENNReal.ofReal (((stdStats out.2).1 : ℝ) / ((stdStats out.2).2 + 1)))
      (ENNReal.ofReal ((harmonic (size + 1) : ℝ) - 1)) := by
  have h := entities_meanLe iS size fuel size [] names (by simp)
  unfold MeanLe at *
  refine le_trans (sexpect_mono _ fun out => ?_) (h.trans_eq ?_)
  · simp only [ΦOut, Φ, closureSum, List.map_nil, List.sum_nil, List.length_nil, zero_add]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (T_nonneg _ _))
  · simp only [closureSum, Φ, List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, zero_div,
      zero_add, harmonic_tail_one]

/-- …at most `log (size + 1)`. -/
theorem sparse_mean_closure_log (fuel iS size : ℕ) (names : List EntityType) :
    MeanLe (WE fuel iS size .sparse [] names)
      (fun out => ENNReal.ofReal (((stdStats out.2).1 : ℝ) / ((stdStats out.2).2 + 1)))
      (ENNReal.ofReal (Real.log (size + 1))) :=
  meanLe_mono (ENNReal.ofReal_le_ofReal (by
    have := harmonic_le_one_add_log (size + 1)
    push_cast at this; linarith)) (sparse_mean_closure fuel iS size names)

end Cedar.Validation.Relational.SchemaGen.Sound

#print axioms Cedar.Validation.Relational.SchemaGen.Sound.sparse_mean_closure_log

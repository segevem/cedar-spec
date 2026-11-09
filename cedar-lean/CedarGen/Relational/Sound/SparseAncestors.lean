import CedarGen.Relational.Sound.SparseExpect

/-! # Claim 2, per type: the mean ancestor closure is logarithmic

In the sparse regime, the expected number of ancestors of a uniformly chosen standard entity type is,
over the generator's successes with at least one standard type, at most `H(N) - 1 ≤ ln N`, where `N`
bounds the number of standard types. For the schema generator's entity part, as its instance runs it
at leaf size `l`, `N = l + 1`. -/

namespace Cedar.Validation.Relational.SchemaGen.Sound

open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Specimen.Correctness Specimen.Backtrack Basalt ENNReal

local notation "WE" => specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen (G := SGen)

/-! ## Means over a weighted event -/

/-- `g`'s mean of `F` over its successes, weighted by `W`, is at most `c`. With `W = 1`, `MeanLe`. -/
def MeanLeW {A : Type} (g : SGen A) (F W : A → ℝ≥0∞) (c : ℝ≥0∞) : Prop := sexpect g F ≤ c * sexpect g W

/-- Each success of the search is one of a branch's: `expect_searchWith_meanLe`, weighted. -/
theorem expect_searchWith_meanLeW {A : Type} (F W : A → ℝ≥0∞) (c : ℝ≥0∞) : ∀ (fuel : Nat)
    (gs : List (Nat × (Unit → SGen A))) (acc : Option Specimen.Exhaustion),
    (∀ p ∈ gs, MeanLeW (p.2 ()) F W c) →
    SPMF.expect (searchWith fuel gs acc).run (succVal F) ≤
      c * SPMF.expect (searchWith fuel gs acc).run (succVal W)
  | _, [], acc, _ => by simp only [searchWith, expect_finish_succ]; exact zero_le
  | 0, _ :: _, acc, _ => by simp only [searchWith, expect_finish_succ]; exact zero_le
  | fuel + 1, p :: gs, acc, hall => by
    simp only [searchWith, OptionT.run_mk]
    rw [SPMF.expect_bind, SPMF.expect_bind, ← SPMF.expect_mul_left]
    refine SPMF.expect_mono fun n => ?_
    split
    · simp only [expect_finish_succ]; exact zero_le
    · rename_i g rest heq
      have hg : MeanLeW (g ()) F W c := hall _ (pickDrop_mem heq)
      have hrest : ∀ q ∈ rest, MeanLeW (q.2 ()) F W c := fun q hq => hall q (pickDrop_rest_sub heq q hq)
      let R (F : A → ℝ≥0∞) : Option (Except Specimen.Exhaustion A) → ℝ≥0∞ := fun o => match o with
        | some (.ok _) => 0
        | some (.error e) => SPMF.expect (searchWith fuel rest (some (acc.elim e fun x => x ⊔ e))).run
            (succVal F)
        | none => SPMF.expect (searchWith fuel rest acc).run (succVal F)
      rw [SPMF.expect_bind, SPMF.expect_bind]
      refine le_of_eq_of_le (b := sexpect (g ()) F + SPMF.expect (g ()).run.run (R F)) ?_
        (le_of_le_of_eq (b := c * (sexpect (g ()) W + SPMF.expect (g ()).run.run (R W))) ?_ ?_)
      · rw [sexpect, ← SPMF.expect_add]
        congr 1; funext o
        rcases o with _ | _ | a <;> simp [R, SPMF.expect_pure, succVal]
      · rw [mul_add, ← SPMF.expect_mul_left]
        gcongr
        · exact hg
        · refine SPMF.expect_mono fun o => ?_
          rcases o with _ | _ | a
          · exact expect_searchWith_meanLeW F W c fuel rest acc hrest
          · exact expect_searchWith_meanLeW F W c fuel rest _ hrest
          · simp [R]
      · rw [sexpect, ← SPMF.expect_add]
        congr 2; funext o
        rcases o with _ | _ | a <;> simp [R, SPMF.expect_pure, succVal]

section MeanLeW
variable {A B : Type}

/-- **The search keeps the weighted mean.** -/
theorem meanLeW_backtrack {gs : List (Nat × (Unit → SGen A))} {F W : A → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ p ∈ gs, MeanLeW (p.2 ()) F W c) : MeanLeW (Specimen.Backtrack.backtrack gs) F W c :=
  expect_searchWith_meanLeW F W c gs.length gs none h

theorem meanLeW_bind_const {g : SGen A} {k : A → SGen B} {F W : B → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, MeanLeW (k a) F W c) : MeanLeW (g >>= k) F W c := by
  unfold MeanLeW at *
  rw [sexpect_bind, sexpect_bind, ← sexpect_mul_left]
  exact sexpect_mono g h

theorem sexpect_mono_support {g : SGen A} {f f' : A → ℝ≥0∞} (h : ∀ a, Produces g a → f a ≤ f' a) :
    sexpect g f ≤ sexpect g f' := by
  have : sexpect g f = sexpect g (fun a => min (f a) (f' a)) := by
    unfold sexpect
    exact SPMF.expect_congr_support fun o ho => by
      rcases o with _ | _ | a
      · rfl
      · rfl
      · exact (min_eq_left (h a ho)).symm
  rw [this]; exact sexpect_mono g fun a => min_le_right _ _

/-- A bind keeps the weighted mean where the continuation does on what the first part produces. -/
theorem meanLeW_bind_support {g : SGen A} {k : A → SGen B} {F W : B → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, Produces g a → MeanLeW (k a) F W c) : MeanLeW (g >>= k) F W c := by
  unfold MeanLeW at *
  rw [sexpect_bind, sexpect_bind, ← sexpect_mul_left]
  exact sexpect_mono_support h

/-- A continuation that keeps both functions, scaled alike. -/
theorem meanLeW_bind_tail {g : SGen A} {k : A → SGen B} {F W : A → ℝ≥0∞} {F' W' : B → ℝ≥0∞}
    {c q : ℝ≥0∞} (hg : MeanLeW g F W c) (hF : ∀ a, sexpect (k a) F' = q * F a)
    (hW : ∀ a, sexpect (k a) W' = q * W a) : MeanLeW (g >>= k) F' W' c := by
  unfold MeanLeW at *
  rw [sexpect_bind, sexpect_bind, sexpect_congr g hF, sexpect_congr g hW, sexpect_mul_left,
    sexpect_mul_left]
  calc q * sexpect g F ≤ q * (c * sexpect g W) := by gcongr
    _ = c * (q * sexpect g W) := by ring

theorem meanLeW_pure {a : A} {F W : A → ℝ≥0∞} {c : ℝ≥0∞} (h : F a ≤ c * W a) :
    MeanLeW (pure a : SGen A) F W c := by
  unfold MeanLeW; rw [sexpect_pure, sexpect_pure]; exact h

theorem meanLeW_of_meanLe_zero {g : SGen A} {F W : A → ℝ≥0∞} {c : ℝ≥0∞} (h : MeanLe g F 0) :
    MeanLeW g F W c := by
  unfold MeanLe MeanLeW at *; rw [zero_mul] at h; exact h.trans zero_le

theorem meanLeW_of_zero {g : SGen A} {F W : A → ℝ≥0∞} {c : ℝ≥0∞} (h : sexpect g F = 0) :
    MeanLeW g F W c := by
  unfold MeanLeW; rw [h]; exact zero_le

theorem sexpect_const' (g : SGen A) (a : ℝ≥0∞) : sexpect g (fun _ => a) = sok g * a := by
  rw [sok, mul_comm, ← sexpect_mul_left]; simp

end MeanLeW

/-! ## Ancestor statistics -/

/-- The standard entries' ancestor lists: their total length, and their number. -/
def ancStats : List (EntityType × EntitySchemaEntry) → ℕ × ℕ
  | [] => (0, 0)
  | (_, .standard e) :: rest => ((ancStats rest).1 + e.ancestors.elts.length, (ancStats rest).2 + 1)
  | (_, .enum _) :: rest => ancStats rest

/-- The mean number of ancestors of a standard entry; `0` without one. -/
noncomputable def meanAnc (entries : List (EntityType × EntitySchemaEntry)) : ℝ :=
  if (ancStats entries).2 = 0 then 0 else ((ancStats entries).1 : ℝ) / (ancStats entries).2

theorem meanAnc_eq (entries : List (EntityType × EntitySchemaEntry)) :
    meanAnc entries = ((ancStats entries).1 : ℝ) / (ancStats entries).2 := by
  unfold meanAnc; split <;> simp_all

/-! ## The potential -/

/-- The harmonic series from `m + 1` to `N`; empty past `N`. -/
noncomputable def htail (m N : ℕ) : ℝ := ∑ j ∈ Finset.Ioc m N, (1 : ℝ) / j

theorem htail_nonneg (m N : ℕ) : 0 ≤ htail m N := Finset.sum_nonneg fun _ _ => by positivity

theorem htail_succ (m N : ℕ) (h : m + 1 ≤ N) : htail m N = 1 / ((m : ℝ) + 1) + htail (m + 1) N := by
  unfold htail
  rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ m) h, Nat.Ioc_succ_singleton, Finset.sum_singleton]
  push_cast; ring

theorem htail_one (n : ℕ) : ENNReal.ofReal (htail 1 n) = ENNReal.ofReal ((harmonic n : ℝ) - 1) := by
  cases n with
  | zero =>
    rw [ENNReal.ofReal_of_nonpos (by simp [htail]), ENNReal.ofReal_of_nonpos (by simp [harmonic])]
  | succ n => rw [htail, harmonic_tail_one]

theorem harmonic_sub_one_le_log (n : ℕ) : (harmonic n : ℝ) - 1 ≤ Real.log n := by
  have := harmonic_le_one_add_log n; linarith

/-- The potential at `m` standard types with `L` ancestors in all: their mean, and what the types
still to come may add to it. -/
noncomputable def Ψ (L m N : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((L : ℝ) / m + htail (max m 1) N)

/-- The potential at the end of the entity list, from a built list `B`. -/
noncomputable def ancOut (B : List (EntityType × List EntityType)) (N : ℕ)
    (out : List EntityType × List (EntityType × EntitySchemaEntry)) : ℝ≥0∞ :=
  Ψ (closureLen B + (ancStats out.2).1) (B.length + (ancStats out.2).2) N

theorem sum_map_real (c d t : ℝ) : ∀ B : List (EntityType × List EntityType),
    (B.map fun q => ((q.2.length : ℝ) + c) / d + t).sum = ((closureLen B : ℝ) + B.length * c) / d + B.length * t
  | [] => by simp [closureLen]
  | q :: B => by
    rw [List.map_cons, List.sum_cons, sum_map_real c d t B, closureLen_cons, List.length_cons]
    push_cast; ring

/-- **The potential is a supermartingale under the sparse pick.** -/
theorem Ψ_pick (et : EntityType) (B : List (EntityType × List EntityType)) (N : ℕ) (h : B.length + 1 ≤ N) :
    (Ψ (closureLen ((et, []) :: B)) (B.length + 1) N +
        (B.map fun q => Ψ (closureLen ((et, q.1 :: q.2) :: B)) (B.length + 1) N).sum) /
      (B.length + 1 : ℕ) ≤ Ψ (closureLen B) B.length N := by
  rcases Nat.eq_zero_or_pos B.length with h0 | hm
  · rw [List.length_eq_zero_iff] at h0; subst h0; simp [Ψ, closureLen]
  · set m := B.length with hmdef
    set L := closureLen B with hL
    set T1 := htail (m + 1) N
    have hB : (B.map fun q => Ψ (closureLen ((et, q.1 :: q.2) :: B)) (m + 1) N) =
        B.map fun q => ENNReal.ofReal (((q.2.length : ℝ) + ((L : ℝ) + 1)) / ((m : ℝ) + 1) + T1) := by
      refine List.map_congr_left fun q _ => ?_
      simp only [Ψ, closureLen_cons, List.length_cons, max_eq_left (by omega : 1 ≤ m + 1), T1, ← hL]
      congr 2; push_cast; ring
    have h0 : Ψ (closureLen ((et, []) :: B)) (m + 1) N = ENNReal.ofReal ((L : ℝ) / ((m : ℝ) + 1) + T1) := by
      simp only [Ψ, closureLen_cons, List.length_nil, zero_add, max_eq_left (by omega : 1 ≤ m + 1), T1,
        ← hL]
      push_cast; rfl
    have hT : ∀ q : EntityType × List EntityType,
        0 ≤ ((q.2.length : ℝ) + ((L : ℝ) + 1)) / ((m : ℝ) + 1) + T1 :=
      fun q => add_nonneg (by positivity) (htail_nonneg _ _)
    rw [hB, h0, ofReal_list_sum _ hT, sum_map_real,
      ← ENNReal.ofReal_add (add_nonneg (by positivity) (htail_nonneg _ _))
        (add_nonneg (by positivity) (mul_nonneg (by positivity) (htail_nonneg _ _))),
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos (by positivity)]
    simp only [Ψ, max_eq_left (by omega : 1 ≤ m)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [htail_succ m N h]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have key : (L : ℝ) / m + (1 / ((m : ℝ) + 1) + T1) -
        (L / ((m : ℝ) + 1) + T1 + ((L + m * (L + 1)) / ((m : ℝ) + 1) + m * T1)) / ((m + 1 : ℕ) : ℝ) =
        (L + m) / (m * ((m : ℝ) + 1) ^ 2) := by
      push_cast
      field_simp
      ring
    have : 0 ≤ ((L : ℝ) + m) / (m * ((m : ℝ) + 1) ^ 2) := by positivity
    linarith

/-! ## The sparse entity list, from any built list -/

theorem entities_meanLe_anc (iS N : Nat) : ∀ (fuel size : Nat) (B : List (EntityType × List EntityType))
    (names : List EntityType), B.length + size ≤ N →
    MeanLe (WE fuel iS size .sparse B names) (ancOut B N) (Ψ (closureLen B) B.length N)
  | 0, _, _, _, _ => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_1]
    unfold MeanLe; rw [sexpect_outOfFuel]; exact zero_le
  | fuel + 1, size, B, names, hN => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_body]
    delta specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.body
    have hnil : ∀ B : List (EntityType × List EntityType), ancOut B N (names, []) = Ψ (closureLen B) B.length N :=
      fun B => by simp [ancOut, ancStats]
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
      · refine meanLe_bind_const fun et => meanLe_bind_const fun attrs => meanLe_bind_const fun tags => ?_
        refine meanLe_bind_uniform (c := fun anc => Ψ (closureLen ((et, anc) :: B)) (B.length + 1) N)
          (q := sok (WE fuel iS size' .sparse [] (et :: names))) (fun anc => ?_) (fun anc => ?_) ?_
        · refine meanLe_bind_uniform (q := 1)
            (c := ancOut ((et, anc) :: B) N) (fun ⟨d, rest⟩ => meanLe_pure ?_) (fun ⟨d, rest⟩ => by simp) ?_
          · simp only [ancOut, ancStats, closureLen_cons, List.length_cons]
            exact le_of_eq (congrArg₂ (Ψ · · N) (by simp only [Cedar.Data.Set.elts]; omega) (by omega))
          · exact entities_meanLe_anc iS N fuel size' _ _ (by simp only [List.length_cons]; omega)
        · rw [sok_bind, sexpect_congr _ (f' := fun _ => 1) (fun ⟨d, rest⟩ => by simp)]
          exact (entities_profile iS fuel size' _ [] _).1
        · unfold MeanLe
          rw [sok_ancGen, mul_one, sexpect_ancGen, sexpect_pickOne]
          exact Ψ_pick et B N (by omega)
      · refine meanLe_bind_const fun et => ?_
        refine meanLe_bind_uniform (c := ancOut B N)
          (q := sok (Basalt.ArbitrarySized.arbitrarySized iS : SGen (List String)))
          (fun ⟨d, rest⟩ => meanLe_bind_const fun eids =>
          meanLe_pure (le_of_eq (by simp [ancOut, ancStats]))) (fun ⟨d, rest⟩ => ?_)
          (entities_meanLe_anc iS N fuel size' B _ (by omega))
        rw [sok_bind]; simp only [sok_pure']; rfl

theorem meanAnc_le_ancOut (N : ℕ) (out : List EntityType × List (EntityType × EntitySchemaEntry)) :
    ENNReal.ofReal (meanAnc out.2) ≤ ancOut [] N out := by
  simp only [ancOut, Ψ, closureLen, List.map_nil, List.sum_nil, List.length_nil, zero_add, meanAnc_eq]
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (htail_nonneg _ _))

/-- **Claim 2, per type, for the sparse worker.** From no types, at size `n`, the mean number of
ancestors of a standard entity type is, over the successes, at most `H(n) - 1`. -/
theorem sparse_mean_ancestors (fuel iS size : ℕ) (names : List EntityType) :
    MeanLe (WE fuel iS size .sparse [] names)
      (fun out => ENNReal.ofReal (meanAnc out.2))
      (ENNReal.ofReal ((harmonic size : ℝ) - 1)) := by
  have h := entities_meanLe_anc iS size fuel size [] names (by simp)
  unfold MeanLe at *
  refine le_trans (sexpect_mono _ fun out => meanAnc_le_ancOut size out) (h.trans_eq ?_)
  simp [Ψ, closureLen, htail_one]

/-- …at most `ln n`. -/
theorem sparse_mean_ancestors_log (fuel iS size : ℕ) (names : List EntityType) :
    MeanLe (WE fuel iS size .sparse [] names)
      (fun out => ENNReal.ofReal (meanAnc out.2))
      (ENNReal.ofReal (Real.log size)) :=
  meanLe_mono (ENNReal.ofReal_le_ofReal (harmonic_sub_one_le_log size)) (sparse_mean_ancestors fuel iS size names)

/-! ## Given at least one standard type -/

theorem sexpect_zero_fun {A : Type} (g : SGen A) : sexpect g (fun _ => 0) = 0 := by
  simpa using sexpect_mul_left g 0 (fun _ => 1)

/-- A sparse standard type with no parent first, then the sparse worker: its mean over successes,
each of which has a standard type. -/
theorem std_step {C : Type} (iS N fuel size' : ℕ) (et : EntityType) (names : List EntityType)
    (k : List EntityType × List (EntityType × EntitySchemaEntry) → SGen C)
    (f : List EntityType → List (EntityType × EntitySchemaEntry) → C) (F W : C → ℝ≥0∞)
    (hk : ∀ d rest, k (d, rest) = pure (f d rest)) (h : 1 + size' ≤ N)
    (hF : ∀ d rest, F (f d rest) ≤ ancOut [(et, [])] N (d, rest)) (hW : ∀ d rest, W (f d rest) = 1) :
    MeanLeW (WE fuel iS size' .sparse [(et, [])] names >>= k) F W (ENNReal.ofReal (htail 1 N)) := by
  have hm := entities_meanLe_anc iS N fuel size' [(et, [])] names (by simp; omega)
  have hΨ : Ψ (closureLen [(et, ([] : List EntityType))]) [(et, ([] : List EntityType))].length N =
      ENNReal.ofReal (htail 1 N) := by
    simp [Ψ, closureLen]
  rw [hΨ] at hm
  have hbase : MeanLeW (WE fuel iS size' .sparse [(et, [])] names) (fun x => F (f x.1 x.2))
      (fun _ => 1) (ENNReal.ofReal (htail 1 N)) := by
    unfold MeanLeW
    unfold MeanLe at hm
    rw [sok] at hm
    have hF' : ∀ x : List EntityType × List (EntityType × EntitySchemaEntry),
        F (f x.1 x.2) ≤ ancOut [(et, [])] N x := fun x => hF x.1 x.2
    exact le_trans (sexpect_mono _ hF') hm
  refine meanLeW_bind_tail (q := 1) hbase ?_ ?_
  · intro x; obtain ⟨d, rest⟩ := x; rw [hk, sexpect_pure, one_mul]
  · intro x; obtain ⟨d, rest⟩ := x; rw [hk, sexpect_pure, one_mul, hW]

theorem meanAnc_std_le (N : ℕ) (et : EntityType) (attrs) (tags) (d : List EntityType)
    (rest : List (EntityType × EntitySchemaEntry)) :
    ENNReal.ofReal (meanAnc ((et, .standard (StandardSchemaEntry.mk (Cedar.Data.Set.mk []) attrs tags)) :: rest))
      ≤ ancOut [(et, [])] N (d, rest) := by
  simp only [ancOut, Ψ, meanAnc_eq, ancStats, closureLen, Cedar.Data.Set.elts, List.length_nil,
    List.length_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, zero_add]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Nat.add_comm 1]
  exact le_add_of_nonneg_right (htail_nonneg _ _)

theorem entities_meanLeW_anc (iS N : ℕ) : ∀ (fuel size : ℕ) (names : List EntityType), size ≤ N →
    MeanLeW (WE fuel iS size .sparse [] names) (fun out => ENNReal.ofReal (meanAnc out.2))
      (fun out => if 1 ≤ (ancStats out.2).2 then 1 else 0) (ENNReal.ofReal (htail 1 N))
  | 0, _, _, _ => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_1]
    exact meanLeW_of_zero (sexpect_outOfFuel _)
  | fuel + 1, size, names, hN => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_body]
    delta specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.body
    have hnil : MeanLeW (pure (names, []) : SGen (List EntityType × List (EntityType × EntitySchemaEntry)))
        (fun out => ENNReal.ofReal (meanAnc out.2)) (fun out => if 1 ≤ (ancStats out.2).2 then 1 else 0)
        (ENNReal.ofReal (htail 1 N)) := meanLeW_pure (by simp [meanAnc, ancStats])
    cases size with
    | zero =>
      refine meanLeW_backtrack fun p hp => ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact hnil
      · dsimp only; exact meanLeW_of_meanLe_zero meanLe_truncations
    | succ size' =>
      refine meanLeW_backtrack fun p hp => ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact hnil
      · refine meanLeW_bind_const fun et => meanLeW_bind_const fun attrs => meanLeW_bind_const fun tags => ?_
        unfold MeanLeW
        rw [sexpect_bind, sexpect_bind, sexpect_ancGen, sexpect_ancGen, sexpect_pickOne, sexpect_pickOne]
        simp only [List.length_nil, List.map_nil, List.sum_nil, add_zero, zero_add, Nat.cast_one, div_one]
        exact std_step iS N fuel size' et _ _ _ _ _ (fun _ _ => rfl) (by omega)
          (fun d rest => meanAnc_std_le N et _ _ d rest) (fun d rest => by simp [ancStats])
      · refine meanLeW_bind_const fun et => ?_
        refine meanLeW_bind_tail (q := sok (Basalt.ArbitrarySized.arbitrarySized iS : SGen (List String)))
          (entities_meanLeW_anc iS N fuel size' (et :: names) (by omega)) (fun ⟨d, rest⟩ => ?_)
          (fun ⟨d, rest⟩ => ?_)
        · rw [sexpect_bind]; simp only [sexpect_pure]
          exact sexpect_const' _ (ENNReal.ofReal (meanAnc rest))
        · rw [sexpect_bind]; simp only [sexpect_pure]
          exact sexpect_const' _ (if 1 ≤ (ancStats rest).2 then 1 else 0)

/-- **Claim 2, per type, given a standard type.** The sparse worker at size `n`, from no types: the
mean number of ancestors of a standard entity type, over its successes with at least one, is at most
`H(n) - 1`. -/
theorem sparse_mean_ancestors_cond (fuel iS size : ℕ) (names : List EntityType) :
    sexpect (WE fuel iS size .sparse [] names) (fun out => ENNReal.ofReal (meanAnc out.2)) ≤
      ENNReal.ofReal ((harmonic size : ℝ) - 1) *
        sprob (WE fuel iS size .sparse [] names) {out | 1 ≤ (ancStats out.2).2} := by
  have h := entities_meanLeW_anc iS size fuel size names le_rfl
  unfold MeanLeW at h
  rw [htail_one] at h
  refine h.trans_eq ?_
  unfold sprob
  congr 1
  exact sexpect_congr _ fun out => by simp [Set.indicator]

/-- …at most `ln n`. -/
theorem sparse_mean_ancestors_cond_log (fuel iS size : ℕ) (names : List EntityType) :
    sexpect (WE fuel iS size .sparse [] names) (fun out => ENNReal.ofReal (meanAnc out.2)) ≤
      ENNReal.ofReal (Real.log size) *
        sprob (WE fuel iS size .sparse [] names) {out | 1 ≤ (ancStats out.2).2} :=
  (sparse_mean_ancestors_cond fuel iS size names).trans
    (by gcongr; exact harmonic_sub_one_le_log size)

/-! ## The schema generator's entity part, as its instance runs it

The regime is drawn at the first standard type, by `Ancestors` on no built types (or, with none, at the
end of the list). Only the sparse runs count, on both sides. -/

local notation "WE0" => specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen (G := SGen)
local notation "WG1" => specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen (G := SGen)

/-- The mean number of ancestors, on the sparse runs. -/
noncomputable abbrev sparseMeanF : HierRegime × List EntityType × List (EntityType × EntitySchemaEntry) → ℝ≥0∞ :=
  fun o => if o.1 = .sparse then ENNReal.ofReal (meanAnc o.2.2) else 0

/-- The sparse runs with a standard type. -/
noncomputable abbrev sparseStdW : HierRegime × List EntityType × List (EntityType × EntitySchemaEntry) → ℝ≥0∞ :=
  fun o => if o.1 = .sparse ∧ 1 ≤ (ancStats o.2.2).2 then 1 else 0

theorem anc_sparse_nil {anc : List EntityType} (h : Ancestors .sparse [] anc) : anc = [] := by
  cases h with
  | sparse _ _ hp =>
    cases hp with
    | none => rfl
    | one _ _ hm => cases hm

theorem we0_meanLeW (iS N : ℕ) : ∀ (fuel sz : ℕ) (names : List EntityType), sz ≤ N →
    MeanLeW (WE0 fuel iS sz [] names) sparseMeanF sparseStdW (ENNReal.ofReal (htail 1 N))
  | 0, _, _, _ => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_1]
    exact meanLeW_of_zero (sexpect_outOfFuel _)
  | fuel + 1, sz, names, hN => by
    rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_body]
    delta specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.body
    cases sz with
    | zero =>
      refine meanLeW_backtrack fun p hp => ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact meanLeW_bind_const fun a => meanLeW_pure (by simp [meanAnc, ancStats])
      · dsimp only; exact meanLeW_of_meanLe_zero meanLe_truncations
    | succ sz' =>
      refine meanLeW_backtrack fun p hp => ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact meanLeW_bind_const fun a => meanLeW_pure (by simp [meanAnc, ancStats])
      · refine meanLeW_bind_const fun et => meanLeW_bind_const fun attrs => meanLeW_bind_const fun tags => ?_
        refine meanLeW_bind_support fun x hp => ?_
        obtain ⟨a, anc⟩ := x
        have ha := specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
          _ _ _ _ _ hp
        cases a with
        | sparse =>
          obtain rfl := anc_sparse_nil ha
          exact std_step iS N (sz' + 1) sz' et (et :: names) _
            (fun d rest => (HierRegime.sparse, d, (et, EntitySchemaEntry.standard
              { ancestors := Cedar.Data.Set.mk [], attrs := Cedar.Data.Map.mk attrs, tags := tags }) :: rest))
            _ _ (fun _ _ => rfl) (by omega)
            (fun d rest => by simp only [sparseMeanF, ↓reduceIte]; exact meanAnc_std_le N et _ _ d rest)
            (fun d rest => by simp [ancStats])
        | dense | flat =>
          refine meanLeW_of_zero ?_
          rw [sexpect_bind]
          refine (sexpect_congr _ fun y => ?_).trans (sexpect_zero_fun _)
          obtain ⟨d, rest⟩ := y
          simp [sexpect_pure]
      · refine meanLeW_bind_const fun et => ?_
        refine meanLeW_bind_tail (q := sok (Basalt.ArbitrarySized.arbitrarySized iS : SGen (List String)))
          (we0_meanLeW iS N fuel sz' (et :: names) (by omega)) ?_ ?_
        · intro x; obtain ⟨a, d, rest⟩ := x
          rw [sexpect_bind]; simp only [sexpect_pure]
          exact sexpect_const' _ (sparseMeanF (a, d, rest))
        · intro x; obtain ⟨a, d, rest⟩ := x
          rw [sexpect_bind]; simp only [sexpect_pure]
          exact sexpect_const' _ (sparseStdW (a, d, rest))

theorem e1_meanLeW (l : ℕ) :
    MeanLeW (WG1 (l + 1) l l [] []) sparseMeanF sparseStdW (ENNReal.ofReal (htail 1 (l + 1))) := by
  rw [specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_body]
  delta specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.body
  have hstd : ∀ (et : EntityType) attrs tags, MeanLeW
      (BacktrackGenFor.gen (P := fun x : HierRegime × List EntityType => Ancestors x.1 [] x.2) (G := SGen) l l >>=
        fun x => match x with
        | (a, ancestors) =>
          (BacktrackGenFor.gen (P := fun x : List EntityType × List (EntityType × EntitySchemaEntry) =>
              match x with | (d, rest) => WfEntitiesGoR a [(et, ancestors)] [et] d rest) (G := SGen) l l >>=
            fun x => match x with
            | (d, rest) => pure (a, d, (et, EntitySchemaEntry.standard
                { ancestors := Cedar.Data.Set.mk ancestors, attrs := Cedar.Data.Map.mk attrs, tags := tags }) :: rest)))
      sparseMeanF sparseStdW (ENNReal.ofReal (htail 1 (l + 1))) := by
    intro et attrs tags
    refine meanLeW_bind_support fun x hp => ?_
    obtain ⟨a, anc⟩ := x
    have ha := specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
      _ _ _ _ _ hp
    cases a with
    | sparse =>
      obtain rfl := anc_sparse_nil ha
      exact std_step l (l + 1) (l + 1) l et [et] _
        (fun d rest => (HierRegime.sparse, d, (et, EntitySchemaEntry.standard
          { ancestors := Cedar.Data.Set.mk [], attrs := Cedar.Data.Map.mk attrs, tags := tags }) :: rest))
        _ _ (fun _ _ => rfl) (by omega)
        (fun d rest => by simp only [sparseMeanF, ↓reduceIte]; exact meanAnc_std_le _ et _ _ d rest)
        (fun d rest => by simp [ancStats])
    | dense | flat =>
      refine meanLeW_of_zero ?_
      rw [sexpect_bind]
      refine (sexpect_congr _ fun y => ?_).trans (sexpect_zero_fun _)
      obtain ⟨d, rest⟩ := y
      simp [sexpect_pure]
  have henum : ∀ et : EntityType, MeanLeW
      (BacktrackGenFor.gen (P := fun x : HierRegime × List EntityType × List (EntityType × EntitySchemaEntry) =>
          match x with | (a, d, rest) => WfEntitiesGoR a [] [et] d rest) (G := SGen) l l >>=
        fun x => match x with
        | (a, d, rest) => (Basalt.ArbitrarySized.arbitrarySized l : SGen (List String)) >>=
          fun eids => pure (a, d, (et, EntitySchemaEntry.enum (Cedar.Data.Set.mk eids)) :: rest))
      sparseMeanF sparseStdW (ENNReal.ofReal (htail 1 (l + 1))) := by
    intro et
    refine meanLeW_bind_tail (q := sok (Basalt.ArbitrarySized.arbitrarySized l : SGen (List String)))
      (we0_meanLeW l (l + 1) (l + 1) l [et] (by omega)) ?_ ?_
    · intro x; obtain ⟨a, d, rest⟩ := x
      rw [sexpect_bind]; simp only [sexpect_pure]
      exact sexpect_const' _ (sparseMeanF (a, d, rest))
    · intro x; obtain ⟨a, d, rest⟩ := x
      rw [sexpect_bind]; simp only [sexpect_pure]
      exact sexpect_const' _ (sparseStdW (a, d, rest))
  cases l <;>
  · refine meanLeW_backtrack fun p hp => ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact meanLeW_bind_const fun et => meanLeW_bind_const fun attrs => meanLeW_bind_const fun tags =>
        hstd et attrs tags
    · exact meanLeW_bind_const fun et => henum et

/-- The schema generator's entity part, as `GenTypeEnvB`'s instance runs it at leaf size `l`:
the regime, the type names, the entries. -/
noncomputable abbrev E1 (l : ℕ) : SGen (HierRegime × List EntityType × List (EntityType × EntitySchemaEntry)) :=
  BacktrackGenFor.gen (P := fun x : HierRegime × List EntityType × List (EntityType × EntitySchemaEntry) =>
    match x with | (a, names, entries) => WfEntitiesGo1 a [] [] names entries) (G := SGen) l l

/-- **Claim 2, per type, for the schema generator's entities.** At leaf size `l`, over the sparse runs
with at least one standard type, the mean number of ancestors of a standard entity type is at most
`H(l + 1) - 1`. -/
theorem entities1_sparse_mean (l : ℕ) :
    sexpect (E1 l) (fun o => if o.1 = .sparse then ENNReal.ofReal (meanAnc o.2.2) else 0) ≤
      ENNReal.ofReal ((harmonic (l + 1) : ℝ) - 1) *
        sexpect (E1 l) (fun o => if o.1 = .sparse ∧ 1 ≤ (ancStats o.2.2).2 then 1 else 0) := by
  have h := e1_meanLeW l
  unfold MeanLeW at h
  rw [htail_one] at h
  exact h

/-- …at most `ln (l + 1)`. -/
theorem entities1_sparse_mean_log (l : ℕ) :
    sexpect (E1 l) (fun o => if o.1 = .sparse then ENNReal.ofReal (meanAnc o.2.2) else 0) ≤
      ENNReal.ofReal (Real.log (l + 1)) *
        sexpect (E1 l) (fun o => if o.1 = .sparse ∧ 1 ≤ (ancStats o.2.2).2 then 1 else 0) := by
  refine (entities1_sparse_mean l).trans ?_
  gcongr
  have := harmonic_sub_one_le_log (l + 1)
  push_cast at this
  exact this

end Cedar.Validation.Relational.SchemaGen.Sound

#print axioms Cedar.Validation.Relational.SchemaGen.Sound.sparse_mean_ancestors
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.sparse_mean_ancestors_log
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.sparse_mean_ancestors_cond
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.sparse_mean_ancestors_cond_log
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.entities1_sparse_mean
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.entities1_sparse_mean_log

import CedarGen.Relational.Depth.Facts

/-! The depth budget, and the statement each step of the fuel induction proves. -/

namespace Cedar.Validation.Relational.Depth

open Cedar.Spec Cedar.Validation Cedar.Data Specimen.Correctness
open Cedar.Validation.Relational.ExprGen.RequestVars

noncomputable abbrev W26 := @specimen_gen_Cedar_Validation_Relational_HasType_2_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _
noncomputable abbrev WE23 := @specimen_gen_Cedar_Validation_Relational_HasTypeExtCall_2_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _
noncomputable abbrev WL2 := @specimen_gen_Cedar_Validation_Relational_HasTypeList_2__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _
noncomputable abbrev WT3 := @specimen_gen_Cedar_Validation_Relational_RecordTypeOf_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _
noncomputable abbrev WF25 := @specimen_gen_Cedar_Validation_Relational_HasTypeFields_2_5__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _
noncomputable abbrev W256 := @specimen_gen_Cedar_Validation_Relational_HasType_2_5_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _
noncomputable abbrev WE236 := @specimen_gen_Cedar_Validation_Relational_HasTypeExtCall_2_3_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _
noncomputable abbrev WT36 := @specimen_gen_Cedar_Validation_Relational_RecordTypeOf_3_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _
noncomputable abbrev WR36 := @specimen_gen_Cedar_Validation_Relational_HasTypeRecord_3_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _
noncomputable abbrev WR3 := @specimen_gen_Cedar_Validation_Relational_HasTypeRecord_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars SGen _ _ _ _ _ _

/-- The depth budget at a size, `sz · (iS + 2)`. A size step adds a node over a call at the
    smaller size (two, for an action literal in a set of entity literals), or `1 + |as| ≤ iS + 1`
    for an `e has a.as` (`ExtHasIf` draws `as` at the leaf size), or a node over a skipped operand,
    which `anyExpr iS` draws, of depth at most `iS`. A split into halves (thirds) whose second
    call starts from capabilities the first earned, and so may copy its subexpressions, at most
    doubles: `2 · D iS (n / 2) + 1 ≤ D iS (n + 1)`. -/
def D (iS sz : Nat) : Nat := sz * (iS + 2)

theorem D_facts (iS n : Nat) :
    D iS (n + 1) = D iS n + (iS + 2) ∧ 2 * D iS (n / 2) ≤ D iS n ∧ 3 * D iS (n / 3) ≤ D iS n ∧
    D iS (n / 2) ≤ D iS n ∧ D iS (n / 3) ≤ D iS n := by
  have m2 : 2 * (n / 2 * (iS + 2)) ≤ n * (iS + 2) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_div_le n 2)
  have m3 : 3 * (n / 3 * (iS + 2)) ≤ n * (iS + 2) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_div_le n 3)
  have h1 : (n + 1) * (iS + 2) = n * (iS + 2) + (iS + 2) := by rw [Nat.add_mul, Nat.one_mul]
  have h2 : n / 2 * (iS + 2) ≤ n * (iS + 2) := Nat.mul_le_mul_right _ (Nat.div_le_self n 2)
  have h3 : n / 3 * (iS + 2) ≤ n * (iS + 2) := Nat.mul_le_mul_right _ (Nat.div_le_self n 3)
  simp only [D]
  omega

theorem D_zero (iS : Nat) : D iS 0 = 0 := by simp [D]

def S_W26 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env ty, succObs.spec (W26 fuel iS sz decl syn c env ty) (fun v => exprDepth v.1 ≤ D iS sz + capsDepth c)

def S_WE23 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env ty, succObs.spec (WE23 fuel iS sz decl syn c env ty) (fun v => listDepth v.2 ≤ D iS sz + capsDepth c)

def S_WL2 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env tys, succObs.spec (WL2 fuel iS sz decl syn c env tys) (fun v => listDepth v ≤ D iS sz + capsDepth c)

def S_WT3 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn b c env rty, succObs.spec (WT3 fuel iS sz decl syn b c env rty) (fun v => recDepth v ≤ D iS sz + capsDepth c)

def S_WF25 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env, succObs.spec (WF25 fuel iS sz decl syn c env) (fun v => recDepth v.1 ≤ D iS sz + capsDepth c)

def S_W256 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env, succObs.spec (W256 fuel iS sz decl syn c env) (fun v => exprDepth v.1 ≤ D iS sz + capsDepth c)

def S_WE236 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn c env, succObs.spec (WE236 fuel iS sz decl syn c env) (fun v => listDepth v.2.1 ≤ D iS sz + capsDepth c)

def S_WT36 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn b c env, succObs.spec (WT36 fuel iS sz decl syn b c env) (fun v => recDepth v.1 ≤ D iS sz + capsDepth c)

def S_WR36 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn lb c env, succObs.spec (WR36 fuel iS sz decl syn lb c env) (fun v => recDepth v.1 ≤ D iS sz + capsDepth c)

def S_WR3 (fuel : Nat) : Prop :=
  ∀ iS sz decl syn lb c env atys, succObs.spec (WR3 fuel iS sz decl syn lb c env atys) (fun v => recDepth v ≤ D iS sz + capsDepth c)

/-- The depth bound at one fuel level, for every worker of the expression-producing block. -/
def Bound (fuel : Nat) : Prop :=
  S_W26 fuel ∧
  S_WE23 fuel ∧
  S_WL2 fuel ∧
  S_WT3 fuel ∧
  S_WF25 fuel ∧
  S_W256 fuel ∧
  S_WE236 fuel ∧
  S_WT36 fuel ∧
  S_WR36 fuel ∧
  S_WR3 fuel

theorem caps26 (fuel iS sz decl syn c env ty) :
    succObs.spec (W26 fuel iS sz decl syn c env ty) (fun v => capsDepth v.2 ≤ max (exprDepth v.1) (capsDepth c)) :=
  succ_mono (specimen_gen_Cedar_Validation_Relational_HasType_2_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.sound fuel iS sz decl syn c env ty) fun _ h => HasType.capsDepth_le h

theorem caps256 (fuel iS sz decl syn c env) :
    succObs.spec (W256 fuel iS sz decl syn c env) (fun v => capsDepth v.2.2 ≤ max (exprDepth v.1) (capsDepth c)) :=
  succ_mono (specimen_gen_Cedar_Validation_Relational_HasType_2_5_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.sound fuel iS sz decl syn c env) fun _ h => HasType.capsDepth_le h

theorem succ_and {α : Type} {g : SGen α} {P Q : α → Prop} (h₁ : succObs.spec g P) (h₂ : succObs.spec g Q) :
    succObs.spec g (fun v => P v ∧ Q v) := fun v hv => ⟨h₁ v hv, h₂ v hv⟩

/-- Close a walk's leaf: unfold the depths, add the budget's arithmetic, and `omega`. -/
macro "depth_leaf" i:term:max n:term:max : tactic => `(tactic| (
  try simp only [listDepth, recDepth, exprDepth, capsDepth, keyDepth, List.length_cons,
    List.length_nil, nat_div_eq_div] at *
  have := D_facts $i $n
  have := D_zero $i
  first
  | omega
  | (simp_all only [listDepth, recDepth, exprDepth, capsDepth, keyDepth]; omega)
  | (casesm* _ × _
     simp only [listDepth, recDepth, exprDepth, capsDepth, keyDepth] at *
     omega)))

end Cedar.Validation.Relational.Depth

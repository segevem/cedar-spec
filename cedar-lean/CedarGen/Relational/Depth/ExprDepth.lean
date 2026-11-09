import CedarGen.Relational.Depth.Step_W26
import CedarGen.Relational.Depth.Step_WE23
import CedarGen.Relational.Depth.Step_WL2
import CedarGen.Relational.Depth.Step_WT3
import CedarGen.Relational.Depth.Step_WF25
import CedarGen.Relational.Depth.Step_W256
import CedarGen.Relational.Depth.Step_WE236
import CedarGen.Relational.Depth.Step_WT36
import CedarGen.Relational.Depth.Step_WR36
import CedarGen.Relational.Depth.Step_WR3

/-! # Linearly bounded depth of the derived expression generator

An expression the derived `HasType` generator produces is at most `D iS sz` deeper than the
capabilities it starts from: linear in the size `sz` for a fixed leaf size `iS`. -/

namespace Cedar.Validation.Relational.Depth

open Cedar.Spec Cedar.Validation Cedar.Data Specimen.Correctness
open Cedar.Validation.Relational.ExprGen.RequestVars

/-- At fuel `0` the workers produce nothing. -/
theorem bound_zero : Bound 0 :=
  ⟨fun iS sz decl syn c env ty => by simp only [W26]; rw [specimen_gen_Cedar_Validation_Relational_HasType_2_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk,
    fun iS sz decl syn c env ty => by simp only [WE23]; rw [specimen_gen_Cedar_Validation_Relational_HasTypeExtCall_2_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk,
    fun iS sz decl syn c env tys => by simp only [WL2]; rw [specimen_gen_Cedar_Validation_Relational_HasTypeList_2__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk,
    fun iS sz decl syn b c env rty => by simp only [WT3]; rw [specimen_gen_Cedar_Validation_Relational_RecordTypeOf_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk,
    fun iS sz decl syn c env => by simp only [WF25]; rw [specimen_gen_Cedar_Validation_Relational_HasTypeFields_2_5__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk,
    fun iS sz decl syn c env => by simp only [W256]; rw [specimen_gen_Cedar_Validation_Relational_HasType_2_5_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk,
    fun iS sz decl syn c env => by simp only [WE236]; rw [specimen_gen_Cedar_Validation_Relational_HasTypeExtCall_2_3_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk,
    fun iS sz decl syn b c env => by simp only [WT36]; rw [specimen_gen_Cedar_Validation_Relational_RecordTypeOf_3_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk,
    fun iS sz decl syn lb c env => by simp only [WR36]; rw [specimen_gen_Cedar_Validation_Relational_HasTypeRecord_3_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk,
    fun iS sz decl syn lb c env atys => by simp only [WR3]; rw [specimen_gen_Cedar_Validation_Relational_HasTypeRecord_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_zero]; walk⟩

theorem bound_all : ∀ fuel, Bound fuel
  | 0 => bound_zero
  | fuel + 1 => have ih := bound_all fuel
    ⟨step_W26 fuel ih,
     step_WE23 fuel ih,
     step_WL2 fuel ih,
     step_WT3 fuel ih,
     step_WF25 fuel ih,
     step_W256 fuel ih,
     step_WE236 fuel ih,
     step_WT36 fuel ih,
     step_WR36 fuel ih,
     step_WR3 fuel ih⟩

/-- **Linearly bounded expression depth.** An expression the derived `HasType` generator produces
    (at any fuel, size `sz` and leaf size `iS`, from the capabilities `c`) is at most
    `D iS sz = sz · (iS + 2)` deeper than `c`, and so are the capabilities it earns. -/
theorem hasType_gen_depth {fuel iS sz : Nat} {decl syn : Bool} {c : Capabilities} {env : TypeEnv}
    {ty : CedarType} {x : Expr} {cout : Capabilities}
    (h : Produces (specimen_gen_Cedar_Validation_Relational_HasType_2_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars (G := SGen) fuel iS sz decl syn c env ty) (x, cout)) :
    exprDepth x ≤ D iS sz + capsDepth c ∧ capsDepth cout ≤ D iS sz + capsDepth c := by
  have h₁ := (bound_all fuel).1 iS sz decl syn c env ty (x, cout) h
  have h₂ := caps26 fuel iS sz decl syn c env ty (x, cout) h
  simp only at h₁ h₂
  omega

/-- From no capabilities (a policy condition), the depth is at most `D iS sz`. -/
theorem hasType_gen_depth_nil {fuel iS sz : Nat} {decl syn : Bool} {env : TypeEnv} {ty : CedarType}
    {x : Expr} {cout : Capabilities}
    (h : Produces (specimen_gen_Cedar_Validation_Relational_HasType_2_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars (G := SGen) fuel iS sz decl syn [] env ty) (x, cout)) :
    exprDepth x ≤ D iS sz := by
  simpa [capsDepth] using (hasType_gen_depth h).1

/-- The same, for the generator as an instance: `BacktrackGenFor.gen s l` runs the worker at size
    `s` and leaf size `l`. -/
theorem hasType_instance_gen_depth {decl syn : Bool} {c : Capabilities} {env : TypeEnv}
    {ty : CedarType} {s l : Nat} {x : Expr} {cout : Capabilities}
    (h : Produces (BacktrackGenFor.gen (P := fun (p : Expr × Capabilities) => match p with
        | (x, cout) => HasType decl syn x c env ty cout) (G := SGen) s l) (x, cout)) :
    exprDepth x ≤ D l s + capsDepth c :=
  (hasType_gen_depth h).1

theorem D_eq (iS sz : Nat) : D iS sz = sz * (iS + 2) := rfl

#print axioms hasType_gen_depth
#print axioms hasType_gen_depth_nil
#print axioms hasType_instance_gen_depth

end Cedar.Validation.Relational.Depth

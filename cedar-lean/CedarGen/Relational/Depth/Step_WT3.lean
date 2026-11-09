import CedarGen.Relational.Depth.Bound

namespace Cedar.Validation.Relational.Depth

open Cedar.Spec Cedar.Validation Cedar.Data Specimen.Correctness
open Cedar.Validation.Relational.ExprGen.RequestVars

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option maxHeartbeats 0 in
theorem step_WT3 (f : Nat) (ih : Bound f) : S_WT3 (f + 1) := by
  obtain ⟨iW26, iWE23, iWL2, iWT3, iWF25, iW256, iWE236, iWT36, iWR36, iWR3⟩ := ih
  have o26 := fun iS sz decl syn c env ty =>
    succ_and (iW26 iS sz decl syn c env ty) (caps26 f iS sz decl syn c env ty)
  have o256 := fun iS sz decl syn c env =>
    succ_and (iW256 iS sz decl syn c env) (caps256 f iS sz decl syn c env)
  clear iW26 iW256
  simp only [S_W26, S_WE23, S_WL2, S_WT3, S_WF25, S_W256, S_WE236, S_WT36, S_WR36, S_WR3, W26, WE23, WL2, WT3, WF25, W256, WE236, WT36, WR36, WR3] at *
  intro iS sz decl syn b c env rty
  cases sz with
  | zero =>
    rw [specimen_gen_Cedar_Validation_Relational_RecordTypeOf_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_body]
    delta specimen_gen_Cedar_Validation_Relational_RecordTypeOf_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.body
    add_trivial_succ_facts "RequestVars.specimen_gen_"
    unfold_gen_instances
    walk [o26, iWE23, iWL2, iWT3, iWF25, o256, iWE236, iWT36, iWR36, iWR3, @ctm01_depth, @cm2_depth, @chain7_depth, @chain67_depth, @hair26_depth, @hair256_depth, @extHasIf_depth, @capIntersect_depth, @isActionLitMemSet_depth, @sortsTo_depth, @deadOperand_depth, @validDecimal_gen, @validIP_gen, @validDatetime_gen, @validDuration_gen]
    clear_trivial_gen_facts
    all_goals depth_leaf iS 0
  | succ n =>
    rw [specimen_gen_Cedar_Validation_Relational_RecordTypeOf_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_body]
    delta specimen_gen_Cedar_Validation_Relational_RecordTypeOf_3__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.body
    add_trivial_succ_facts "RequestVars.specimen_gen_"
    unfold_gen_instances
    walk [o26, iWE23, iWL2, iWT3, iWF25, o256, iWE236, iWT36, iWR36, iWR3, @ctm01_depth, @cm2_depth, @chain7_depth, @chain67_depth, @hair26_depth, @hair256_depth, @extHasIf_depth, @capIntersect_depth, @isActionLitMemSet_depth, @sortsTo_depth, @deadOperand_depth, @validDecimal_gen, @validIP_gen, @validDatetime_gen, @validDuration_gen]
    clear_trivial_gen_facts
    all_goals depth_leaf iS n

end Cedar.Validation.Relational.Depth

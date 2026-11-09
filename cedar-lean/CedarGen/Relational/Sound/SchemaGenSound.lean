import CedarGen.Relational.SchemaGen

/-! The derived schema generator only produces what its relation allows. Its workers' laws `W.sound`
come with the derivation (`specimen.emitSound`); here, what they give for whole environments. -/

namespace Cedar.Validation.Relational.SchemaGen.Sound
open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Specimen.Correctness Basalt

/-- **Claim 4, for the generator.** Every environment the derived schema generator produces, at any
fuel, size and leaf size, is well formed and has at most `budget` request environments. -/
theorem genTypeEnvB_generated (fuel iS sz budget : Nat) (r : HierRegime) (env : TypeEnv)
    (h : Produces (specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen
      fuel iS sz budget : SGen _) (r, env)) :
    WfTypeEnv env ∧ env.schema.environments.length ≤ budget :=
  genTypeEnvB_iff.mp ⟨r, specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
    fuel iS sz budget (r, env) h⟩

/-- …and so is every environment of the generator as its instance runs it. -/
theorem genTypeEnvB_instance_generated (budget s l : Nat) (r : HierRegime) (env : TypeEnv)
    (h : Produces (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2)
      (G := SGen) s l) (r, env)) :
    WfTypeEnv env ∧ env.schema.environments.length ≤ budget :=
  genTypeEnvB_generated _ _ _ budget r env h

/-- **Complete as well.** Every well-formed environment with at most `budget` request environments is
generated, in some regime, at every large enough size and leaf size. -/
theorem genTypeEnvB_instance_complete (budget : Nat) (env : TypeEnv)
    (h : WfTypeEnv env ∧ env.schema.environments.length ≤ budget) :
    ∃ r n, ∀ s l, n ≤ s → n ≤ l →
      Produces (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) (r, env) := by
  obtain ⟨r, hr⟩ := genTypeEnvB_iff.mpr h
  exact ⟨r, BacktrackGenForComplete.complete (r, env) hr⟩

end Cedar.Validation.Relational.SchemaGen.Sound

#print axioms Cedar.Validation.Relational.SchemaGen.Sound.genTypeEnvB_instance_complete
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.genTypeEnvB_generated
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.genTypeEnvB_instance_generated

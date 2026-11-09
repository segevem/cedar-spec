import CedarGen.Relational.Sound.SchemaGenSound

/-! **Claim 2, hard part.** In the sparse regime the generated entity hierarchy is a forest: every
standard type's ancestors are none, or one parent followed by that parent's own ancestors. In the flat
regime there are no ancestors at all. Stated on the relation, then on the derived generator's outputs
through its soundness. -/

namespace Cedar.Validation.Relational.SchemaGen.Sound

open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Cedar.Data Specimen.Correctness

/-- The standard types of an entity list, each with its ancestor list. -/
def standardPairs : List (EntityType × EntitySchemaEntry) → List (EntityType × List EntityType)
  | [] => []
  | (et, .standard e) :: rest => (et, e.ancestors.elts) :: standardPairs rest
  | (_, .enum _) :: rest => standardPairs rest

/-- One parent and its ancestors, or none: a node of a forest over `pairs`. -/
def ForestNode (pairs : List (EntityType × List EntityType)) (a : List EntityType) : Prop :=
  a = [] ∨ ∃ p pa, a = p :: pa ∧ (p, pa) ∈ pairs

theorem wfEntitiesGoR_sparse {built names allNames rest}
    (h : WfEntitiesGoR .sparse built names allNames rest) :
    ∀ x ∈ standardPairs rest, ForestNode (built ++ standardPairs rest) x.2 := by
  induction h with
  | nil => simp [standardPairs]
  | standard built names et ancestors attrs tags allNames rest _ hanc _ _ _ ih =>
    intro x hx
    simp only [standardPairs] at hx ⊢
    have hmem : ∀ y, y ∈ (et, ancestors) :: built ++ standardPairs rest →
        y ∈ built ++ (et, ancestors) :: standardPairs rest := by
      intro y hy; simp only [List.mem_append, List.mem_cons] at hy ⊢; tauto
    have lift : ∀ a, ForestNode ((et, ancestors) :: built ++ standardPairs rest) a →
        ForestNode (built ++ (et, ancestors) :: standardPairs rest) a := by
      rintro a (h | ⟨p, pa, rfl, hp⟩)
      · exact .inl h
      · exact .inr ⟨p, pa, rfl, hmem _ hp⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · cases hanc with
      | sparse _ _ hpick =>
        cases hpick with
        | none => exact .inl rfl
        | one p pset hp => exact .inr ⟨p, pset, rfl, List.mem_append_left _ hp⟩
    · exact lift _ (ih x hx)
  | enum _ _ _ _ _ _ _ _ ih => simpa [standardPairs] using ih

theorem WfEntitiesGo1.toR {r built names allNames rest}
    (h : WfEntitiesGo1 r built names allNames rest) : WfEntitiesGoR r built names allNames rest := by
  cases h <;> constructor <;> assumption

theorem wfEntitiesGoR_flat {built names allNames rest}
    (h : WfEntitiesGoR .flat built names allNames rest) : ∀ x ∈ standardPairs rest, x.2 = [] := by
  induction h with
  | nil => simp [standardPairs]
  | standard _ _ _ _ _ _ _ _ _ hanc _ _ _ ih =>
    intro x hx
    simp only [standardPairs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · cases hanc; rfl
    · exact ih x hx
  | enum _ _ _ _ _ _ _ _ ih => simpa [standardPairs] using ih

/-- **Claim 2 (sparse), for the generator.** A schema the derived generator produces in the sparse
regime has a forest for its entity hierarchy: each standard type's ancestors are none, or one parent
followed by the parent's own ancestors. -/
theorem generated_sparse_forest (fuel iS sz budget : Nat) (ets : List (EntityType × EntitySchemaEntry))
    (acts reqty)
    (h : Produces (specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen
      fuel iS sz budget : SGen _) (.sparse, TypeEnv.mk (Map.mk ets) acts reqty)) :
    ∀ x ∈ standardPairs ets, ForestNode (standardPairs ets) x.2 := by
  have hs := specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
    fuel iS sz budget _ h
  cases hs with
  | mk _ _ _ _ hents _ => simpa using wfEntitiesGoR_sparse (WfEntitiesGo1.toR hents)

/-- **Claim 2 (flat), for the generator.** In the flat regime no type has an ancestor. -/
theorem generated_flat_none (fuel iS sz budget : Nat) (ets : List (EntityType × EntitySchemaEntry))
    (acts reqty)
    (h : Produces (specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen
      fuel iS sz budget : SGen _) (.flat, TypeEnv.mk (Map.mk ets) acts reqty)) :
    ∀ x ∈ standardPairs ets, x.2 = [] := by
  have hs := specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
    fuel iS sz budget _ h
  cases hs with
  | mk _ _ _ _ hents _ => exact wfEntitiesGoR_flat (WfEntitiesGo1.toR hents)

end Cedar.Validation.Relational.SchemaGen.Sound

#print axioms Cedar.Validation.Relational.SchemaGen.Sound.generated_sparse_forest
#print axioms Cedar.Validation.Relational.SchemaGen.Sound.generated_flat_none

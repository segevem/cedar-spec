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

import CedarGen.Relational.Sound.RequestVariety
import CedarGen.Relational.Sound.SchemaGenSound
import CedarGen.Relational.SchemaGenProb
import Specimen.Enum.Laws.BacktrackWithWeight

/-! # The schema generator never fails

Proved of the derived code at `SGen`. Every derived worker the schema generator runs, and every
hand-written instance and leaf it draws from, loses no mass (`Tot`: it succeeds or fails, surely);
then a search succeeds surely where one of its branches does (`sok_backtrack_of_sure`). The entity
list's `nil` always succeeds, so the entity schema never fails (`sok_we1`); the request's action,
placed first from the full name pool with no actions before it, always succeeds, so the actions never
fail once the budget allows one environment (`sok_wa_top`). Hence `genTypeEnvB_instance_sok`. -/

namespace Cedar.Validation.Relational.SchemaGen.Sure
open Specimen.Correctness Specimen.Backtrack Cedar.Spec
open Specimen.Correctness Basalt ENNReal

variable {A B : Type}

/-- `g` loses no mass: it succeeds or fails, surely. -/
abbrev Tot (g : SGen A) : Prop := sok g + sfail g = 1

theorem tot_eq_mass (g : SGen A) : sok g + sfail g = g.run.run.mass := by
  unfold sok sexpect sfail
  rw [← SPMF.expect_add]
  calc _ = SPMF.expect g.run.run (fun _ => 1) := by
        congr 1; funext o; rcases o with _ | _ | a <;> simp [succVal, failVal]
    _ = g.run.run.mass := SPMF.expect_one _

theorem tot_backtrack {gs : List (Nat × (Unit → SGen A))} (h : ∀ p ∈ gs, Tot (p.2 ())) :
    Tot (Specimen.Backtrack.backtrack gs) := by
  unfold Tot; rw [tot_eq_mass]
  exact Specimen.Backtrack.mass_searchWith gs.length gs none fun p hp _ => by
    rw [← tot_eq_mass]; exact h p hp

theorem tot_backtrack_filterMap {os : List (Option (Nat × (Unit → SGen A)))}
    (h : ∀ q ∈ os, ∀ p, q = some p → Tot (p.2 ())) :
    Tot (Specimen.Backtrack.backtrack (os.filterMap fun o => o)) :=
  tot_backtrack fun p hp => by
    obtain ⟨q, hq, hqp⟩ := List.mem_filterMap.mp hp
    exact h q hq p hqp

theorem tot_pure (a : A) : Tot (pure a : SGen A) := total_of_sok (sok_pure a)
theorem tot_bind {g : SGen A} {k : A → SGen B} (hg : Tot g) (hk : ∀ a, Tot (k a)) : Tot (g >>= k) :=
  Variety.total_bind hg hk
theorem tot_refute : Tot (Specimen.refute : SGen A) := Variety.total_refute
theorem tot_fail : Tot (Specimen.Fail.fail : SGen A) := Variety.total_refute
theorem tot_failWith (e : Specimen.Exhaustion) : Tot (Specimen.FailWith.failWith e : SGen A) := total_failWith e
theorem tot_truncations (ls : List (Specimen.Label A)) : Tot (Specimen.truncations ls : SGen A) := total_truncations ls
theorem tot_outOfFuel : Tot (Specimen.outOfFuel : SGen A) := total_failWith _
theorem tot_inconclusive : Tot (Specimen.inconclusive : SGen A) := total_failWith _
theorem tot_of_sok {g : SGen A} (h : sok g = 1) : Tot g := total_of_sok h


/-! ## Leaves -/

theorem sok_choose (lo hi : Nat) (h : lo ≤ hi) : sok (RandomChoice.choose lo hi h : SGen _) = 1 := by
  rw [sok, sexpect_choose, SPMF.expect_one]; exact SPMF.mass_choose _ _ _

theorem sok_elements {α : Type} (xs : List α) (h : xs ≠ []) : sok (elements xs h : SGen α) = 1 := by
  unfold elements
  exact sok_bind_one (sok_map_one _ (sok_choose _ _ _)) fun _ => sok_pure _

theorem sok_oneOf {α : Type} (gs : List (Unit → SGen α)) (h : gs ≠ []) (hall : ∀ g ∈ gs, sok (g ()) = 1) :
    sok (oneOf gs h : SGen α) = 1 := by
  unfold oneOf
  exact sok_bind_one (sok_choose _ _ _) fun i => hall _ (List.getElem_mem _)

theorem sok_arbString (n : Nat) : sok (ArbitrarySized.arbitrarySized n : SGen String) = 1 := by
  show sok (frequency [(6, fun _ => elements namePool (by simp [namePool])), (3, fun _ => printString n),
    (1, fun _ => anyString n)] _ : SGen String) = 1
  refine sok_frequency _ fun p hp _ => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact sok_elements _ (by simp [namePool])
  · exact sok_bind_one (sok_chooseNat _ _ _) fun _ =>
      sok_bind_one (sok_vectorOf (sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_pure _) _) fun _ => sok_pure _
  · refine sok_bind_one (sok_chooseNat _ _ _) fun _ =>
      sok_bind_one (sok_vectorOf (sok_frequency _ fun p hp _ => ?_) _) fun _ => sok_pure _
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> exact sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_pure _

theorem sok_arbListString (n : Nat) : sok (ArbitrarySized.arbitrarySized n : SGen (List String)) = 1 :=
  sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_vectorOf (sok_arbString n) _

theorem sok_arbName (n : Nat) : sok (ArbitrarySized.arbitrarySized n : SGen Name) = 1 := by
  show sok (do
    let id ← (ArbitrarySized.arbitrarySized n : SGen String)
    let path ← frequency [(9, fun _ => pure []), (1, fun _ => (ArbitrarySized.arbitrarySized n : SGen (List String)))]
    pure (Name.mk id path) : SGen Name) = 1
  refine sok_bind_one (sok_arbString n) fun _ => sok_bind_one (sok_frequency _ fun p hp _ => ?_) fun _ => sok_pure _
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact sok_pure _
  · exact sok_arbListString n

theorem sok_arbRegime (n : Nat) : sok (ArbitrarySized.arbitrarySized n : SGen HierRegime) = 1 := by
  show sok (Cedar.Validation.Relational.SchemaGen.Cedar.Validation.Relational.SchemaGen.HierRegime.basaltArbitrarySized n : SGen HierRegime) = 1
  unfold Cedar.Validation.Relational.SchemaGen.Cedar.Validation.Relational.SchemaGen.HierRegime.basaltArbitrarySized
  cases n <;> exact sok_oneOf _ _ (by simp)


/-! ## Hand-written instances -/

theorem tot_defined (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun et => Cedar.Validation.Relational.Schema.DefinedEntityType ets et) (G := SGen) s l) := by
  show Tot (do
    if ets.isEmpty then Specimen.Fail.fail else
    let i ← chooseNat 0 (ets.length - 1)
    match ets[i]? with
    | some et => pure et
    | none => Specimen.Fail.fail : SGen EntityType)
  split
  · exact tot_fail
  · refine tot_bind (tot_of_sok (sok_chooseNat _ _ _)) fun i => ?_
    split
    · exact tot_pure _
    · exact tot_fail

theorem sok_pickOneAction (built : List (EntityUID × List EntityUID)) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun a => PickOneActionAncestor built a) (G := SGen) s l) = 1 := by
  show sok (do
    let i ← chooseNat 0 built.length
    if i = 0 then pure [] else
    match built[i - 1]? with
    | some (p, pset) => pure (p :: pset)
    | none => Specimen.Fail.fail : SGen (List EntityUID)) = 1
  refine sok_bind_one_of_support (sok_chooseNat _ _ _) fun i hi => ?_
  have := (chooseNat_range hi).2
  split
  · exact sok_pure _
  · rw [List.getElem?_eq_getElem (by omega)]
    exact sok_pure _

theorem sok_pickOneE (built : List (EntityType × List EntityType)) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun a => PickOneAncestor built a) (G := SGen) s l) = 1 := by
  show sok (do
    let i ← chooseNat 0 built.length
    if i = 0 then pure [] else
    match built[i - 1]? with
    | some (p, pset) => pure (p :: pset)
    | none => Specimen.Fail.fail : SGen (List EntityType)) = 1
  refine sok_bind_one_of_support (sok_chooseNat _ _ _) fun i hi => ?_
  have := (chooseNat_range hi).2
  split
  · exact sok_pure _
  · rw [List.getElem?_eq_getElem (by omega)]
    exact sok_pure _

theorem sok_attrAbove (b : Attr) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun a => b < a) (G := SGen) s l) = 1 := by
  show sok (frequency [
    (3, fun _ => do
      let n ← chooseNat 1 (s + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    (1, fun _ => do
      let a ← anyString s
      return if b < a then a else b ++ String.ofList (List.replicate 1 'a'))] : SGen Attr) = 1
  refine sok_frequency _ fun p hp _ => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_pure _
  · refine sok_bind_one ?_ fun _ => sok_pure _
    refine sok_bind_one (sok_chooseNat _ _ _) fun _ =>
      sok_bind_one (sok_vectorOf (sok_frequency _ fun p hp _ => ?_) _) fun _ => sok_pure _
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> exact sok_bind_one (sok_chooseNat _ _ _) fun _ => sok_pure _

/-! ## Derived workers -/

noncomputable abbrev NotIn := @specimen_gen_Cedar_Validation_Relational_Schema_NotInET_0__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev KeyAb := @specimen_gen_Cedar_Validation_Relational_Schema_KeyAbove_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev Attrs := @specimen_gen_Cedar_Validation_Relational_Schema_WfAttrs_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev CTy := @specimen_gen_Cedar_Validation_Relational_Schema_WfCedarType_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev Tags := @specimen_gen_Cedar_Validation_Relational_Schema_WfTags_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

theorem tot_notIn : ∀ (fuel iS sz : Nat) (names : List EntityType), Tot (NotIn fuel iS sz names)
  | 0, _, _, _ => by rw [NotIn, specimen_gen_Cedar_Validation_Relational_Schema_NotInET_0__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, names => by
    rw [NotIn, specimen_gen_Cedar_Validation_Relational_Schema_NotInET_0__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases names with _ | ⟨x, rest⟩ <;>
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte] <;>
      refine tot_backtrack ?_ <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
    · exact tot_bind (tot_of_sok (sok_arbName _)) fun _ => tot_pure _
    · exact tot_truncations _
    · exact tot_bind (tot_of_sok (sok_arbName _)) fun _ => tot_pure _
    · refine tot_bind (tot_notIn f iS s rest) fun a => ?_
      split
      · exact tot_pure _
      · exact tot_refute
      · exact tot_inconclusive

theorem sok_notIn_nil (f iS sz : Nat) : sok (NotIn (f + 1) iS sz []) = 1 := by
  rw [NotIn, specimen_gen_Cedar_Validation_Relational_Schema_NotInET_0__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases sz with _ | s <;>
    simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte] <;>
    exact sok_backtrack_one _ (by simp [sumWeights]) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      exact sok_bind_one (sok_arbName _) fun _ => sok_pure _)

theorem sok_keyAb (f iS sz : Nat) (a : Option Attr) : sok (KeyAb (f + 1) iS sz a) = 1 := by
  rw [KeyAb, specimen_gen_Cedar_Validation_Relational_Schema_KeyAbove_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases a with _ | b
  · have h : sok (Basalt.ArbitrarySized.arbitrarySized iS >>= fun b => pure b : SGen Attr) = 1 :=
      sok_bind_one (sok_arbString _) fun _ => sok_pure _
    rcases sz with _ | s <;>
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte] <;>
      exact sok_backtrack_one _ (by simp [sumWeights]) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]; exact h)
  · have h : sok (BacktrackGenFor.gen (P := fun a => b < a) (G := SGen) iS iS >>= fun b => pure b) = 1 :=
      sok_bind_one (sok_attrAbove _ _ _) fun _ => sok_pure _
    rcases sz with _ | s <;>
      simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte] <;>
      exact sok_backtrack_one _ (by simp [sumWeights]) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]; exact h)

theorem tot_keyAb : ∀ (fuel iS sz : Nat) (a : Option Attr), Tot (KeyAb fuel iS sz a)
  | 0, _, _, _ => by rw [KeyAb, specimen_gen_Cedar_Validation_Relational_Schema_KeyAbove_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, a => tot_of_sok (sok_keyAb f iS sz a)

theorem tot_attrs_cty : ∀ (fuel : Nat), (∀ iS sz a ets, Tot (Attrs fuel iS sz a ets)) ∧ (∀ iS sz ets, Tot (CTy fuel iS sz ets))
  | 0 => ⟨fun _ _ _ _ => by rw [Attrs, specimen_gen_Cedar_Validation_Relational_Schema_WfAttrs_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel,
          fun _ _ _ => by rw [CTy, specimen_gen_Cedar_Validation_Relational_Schema_WfCedarType_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel⟩
  | f + 1 => by
    obtain ⟨ihA, ihC⟩ := tot_attrs_cty f
    refine ⟨fun iS sz a ets => ?_, fun iS sz ets => ?_⟩
    · rw [Attrs, specimen_gen_Cedar_Validation_Relational_Schema_WfAttrs_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
      rcases sz with _ | s <;> refine tot_backtrack ?_ <;>
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      · exact ⟨tot_pure _, tot_truncations _⟩
      · exact ⟨tot_pure _,
          tot_bind (tot_keyAb _ _ _ _) fun _ => tot_bind (ihA _ _ _ _) fun _ => tot_bind (ihC _ _ _) fun _ => tot_pure _,
          tot_bind (tot_keyAb _ _ _ _) fun _ => tot_bind (ihA _ _ _ _) fun _ => tot_bind (ihC _ _ _) fun _ => tot_pure _⟩
    · rw [CTy, specimen_gen_Cedar_Validation_Relational_Schema_WfCedarType_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
      rcases sz with _ | s <;> refine tot_backtrack ?_ <;>
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      · exact ⟨tot_pure _, tot_pure _, tot_pure _, tot_bind (tot_defined _ _ _) fun _ => tot_pure _,
          tot_pure _, tot_pure _, tot_pure _, tot_pure _, tot_truncations _⟩
      · exact ⟨tot_pure _, tot_pure _, tot_pure _, tot_bind (tot_defined _ _ _) fun _ => tot_pure _,
          tot_pure _, tot_pure _, tot_pure _, tot_pure _,
          tot_bind (ihA _ _ _ _) fun _ => tot_pure _, tot_bind (ihC _ _ _) fun _ => tot_pure _⟩

theorem tot_attrs (fuel iS sz : Nat) (a : Option Attr) (ets : List EntityType) : Tot (Attrs fuel iS sz a ets) :=
  (tot_attrs_cty fuel).1 iS sz a ets

theorem tot_cty (fuel iS sz : Nat) (ets : List EntityType) : Tot (CTy fuel iS sz ets) :=
  (tot_attrs_cty fuel).2 iS sz ets

theorem sok_attrs (f iS sz : Nat) (a : Option Attr) (ets : List EntityType) : sok (Attrs (f + 1) iS sz a ets) = 1 := by
  rw [Attrs, specimen_gen_Cedar_Validation_Relational_Schema_WfAttrs_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  have h := tot_attrs_cty f
  rcases sz with _ | s <;> refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, sok_pure _⟩ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  · exact ⟨tot_pure _, tot_truncations _⟩
  · exact ⟨tot_pure _,
      tot_bind (tot_keyAb _ _ _ _) fun _ => tot_bind (h.1 _ _ _ _) fun _ => tot_bind (h.2 _ _ _) fun _ => tot_pure _,
      tot_bind (tot_keyAb _ _ _ _) fun _ => tot_bind (h.1 _ _ _ _) fun _ => tot_bind (h.2 _ _ _) fun _ => tot_pure _⟩

theorem sok_tags (f iS sz : Nat) (ets : List EntityType) : sok (Tags (f + 1) iS sz ets) = 1 := by
  rw [Tags, specimen_gen_Cedar_Validation_Relational_Schema_WfTags_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases sz with _ | s <;> refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, sok_pure _⟩ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
    exact ⟨tot_pure _, tot_bind (tot_cty _ _ _ _) fun _ => tot_pure _⟩


/-! ## A tactic for totality -/

syntax "tot_step" : tactic
macro_rules
  | `(tactic| tot_step) => `(tactic| first
      | with_reducible exact tot_pure _
      | with_reducible exact tot_refute
      | with_reducible exact tot_fail
      | with_reducible exact tot_truncations _
      | with_reducible exact tot_failWith _
      | with_reducible exact tot_outOfFuel
      | with_reducible exact tot_inconclusive
      | (with_reducible refine ⟨?_, ?_⟩)
      | (with_reducible refine tot_bind ?_ fun _ => ?_)
      | split)

syntax "tot_close" (" [" term,* "]")? : tactic
macro_rules
  | `(tactic| tot_close) => `(tactic| repeat' tot_step)
  | `(tactic| tot_close [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| tot_step)
    for t in ts.getElems do
      tac ← `(tactic| first | (with_reducible_and_instances apply $t) | ($tac:tactic))
    `(tactic| repeat' ($tac:tactic))

/-- Unfold a derived worker at `fuel + 1` and open its search. -/
macro "tot_open" : tactic => `(tactic|
  (simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte, Bool.or_self]
   refine tot_backtrack ?_
   simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.not_mem_nil,
     false_imp_iff, imp_true_iff, implies_true]))

theorem tot_gen_defined (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun et => Cedar.Validation.Relational.Schema.DefinedEntityType ets et) (G := SGen) s l) :=
  tot_defined ets s l

theorem tot_gen_attrs (a : Option Attr) (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.WfAttrs a ets x) (G := SGen) s l) :=
  tot_attrs _ _ _ _ _

theorem sok_gen_attrs (a : Option Attr) (ets : List EntityType) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.WfAttrs a ets x) (G := SGen) s l) = 1 :=
  sok_attrs _ _ _ _ _

theorem sok_gen_tags (ets : List EntityType) (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.WfTags ets x) (G := SGen) s l) = 1 :=
  sok_tags _ _ _ _

theorem tot_gen_tags (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.WfTags ets x) (G := SGen) s l) :=
  tot_of_sok (sok_gen_tags _ _ _)

theorem tot_gen_notIn (ets : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.NotInET x ets) (G := SGen) s l) :=
  tot_notIn _ _ _ _

theorem sok_gen_notIn_nil (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun x => Cedar.Validation.Relational.Schema.NotInET x []) (G := SGen) s l) = 1 :=
  sok_notIn_nil _ _ _

noncomputable abbrev SelRem := @specimen_gen_Cedar_Validation_Relational_Schema_SelectRemove_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev AppE := @specimen_gen_Cedar_Validation_Relational_Schema_AppendET_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev AppU := @specimen_gen_Cedar_Validation_Relational_Schema_AppendUID_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev PickE := @specimen_gen_Cedar_Validation_Relational_Schema_PickClosedAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev PickA := @specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

theorem tot_selRem : ∀ (fuel iS sz : Nat) (α : Type) (xs : List α), Tot (SelRem fuel iS sz α xs)
  | 0, _, _, _, _ => by rw [SelRem, specimen_gen_Cedar_Validation_Relational_Schema_SelectRemove_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, α, xs => by
    rw [SelRem, specimen_gen_Cedar_Validation_Relational_Schema_SelectRemove_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases xs with _ | ⟨x, xs⟩ <;> tot_open <;> tot_close [tot_selRem]

theorem sok_selRem (f iS sz : Nat) (α : Type) (xs : List α) (h : xs ≠ []) : sok (SelRem (f + 1) iS sz α xs) = 1 := by
  rw [SelRem, specimen_gen_Cedar_Validation_Relational_Schema_SelectRemove_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  rcases sz with _ | s <;>
    simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte] <;>
    refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, sok_pure _⟩ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
    tot_close [tot_selRem]

theorem tot_appE : ∀ (fuel iS sz : Nat) (xs ys : List EntityType), Tot (AppE fuel iS sz xs ys)
  | 0, _, _, _, _ => by rw [AppE, specimen_gen_Cedar_Validation_Relational_Schema_AppendET_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, xs, ys => by
    rw [AppE, specimen_gen_Cedar_Validation_Relational_Schema_AppendET_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases xs with _ | ⟨x, xs⟩ <;> tot_open <;> tot_close [tot_appE]

theorem tot_appU : ∀ (fuel iS sz : Nat) (xs ys : List EntityUID), Tot (AppU fuel iS sz xs ys)
  | 0, _, _, _, _ => by rw [AppU, specimen_gen_Cedar_Validation_Relational_Schema_AppendUID_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, xs, ys => by
    rw [AppU, specimen_gen_Cedar_Validation_Relational_Schema_AppendUID_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases xs with _ | ⟨x, xs⟩ <;> tot_open <;> tot_close [tot_appU]

theorem tot_gen_appE (xs ys : List EntityType) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun m => Cedar.Validation.Relational.Schema.AppendET xs ys m) (G := SGen) s l) :=
  tot_appE _ _ _ _ _

theorem tot_gen_appU (xs ys : List EntityUID) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun m => Cedar.Validation.Relational.Schema.AppendUID xs ys m) (G := SGen) s l) :=
  tot_appU _ _ _ _ _

theorem tot_pickE : ∀ (fuel iS sz : Nat) (b : List (EntityType × List EntityType)), Tot (PickE fuel iS sz b)
  | 0, _, _, _ => by rw [PickE, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, b => by
    rw [PickE, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases b with _ | ⟨⟨p, ps⟩, b⟩ <;> tot_open <;> tot_close [tot_pickE, tot_gen_appE]

theorem tot_pickA : ∀ (fuel iS sz : Nat) (b : List (EntityUID × List EntityUID)), Tot (PickA fuel iS sz b)
  | 0, _, _, _ => by rw [PickA, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, b => by
    rw [PickA, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases b with _ | ⟨⟨p, ps⟩, b⟩ <;> tot_open <;> tot_close [tot_pickA, tot_gen_appU]

theorem sok_pickA_nil (f iS sz : Nat) : sok (PickA (f + 1) iS sz []) = 1 := by
  rw [PickA, specimen_gen_Cedar_Validation_Relational_Schema_PickClosedActionAncestors_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  cases sz <;> simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte,
      Bool.or_self] <;>
    exact sok_backtrack_one _ (by simp [sumWeights]) (by simp)

theorem tot_gen_pickE (b : List (EntityType × List EntityType)) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun c => Cedar.Validation.Relational.Schema.PickClosedAncestors b c) (G := SGen) s l) :=
  tot_pickE _ _ _ _

theorem tot_gen_pickA (b : List (EntityUID × List EntityUID)) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun c => Cedar.Validation.Relational.Schema.PickClosedActionAncestors b c) (G := SGen) s l) :=
  tot_pickA _ _ _ _

theorem tot_gen_pickOneE (b : List (EntityType × List EntityType)) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun c => PickOneAncestor b c) (G := SGen) s l) :=
  tot_of_sok (sok_pickOneE _ _ _)

theorem tot_gen_pickOneA (b : List (EntityUID × List EntityUID)) (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun c => PickOneActionAncestor b c) (G := SGen) s l) :=
  tot_of_sok (sok_pickOneAction _ _ _)


/-! ## The entity workers -/

noncomputable abbrev Anc := @specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev Anc02 := @specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev WE := @specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev WE0 := @specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev WE1 := @specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

theorem tot_anc : ∀ (fuel iS sz : Nat) (r : HierRegime) (b : List (EntityType × List EntityType)), Tot (Anc fuel iS sz r b)
  | 0, _, _, _, _ => by rw [Anc, specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, r, b => by
    rw [Anc, specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases r <;> tot_open <;> tot_close [tot_gen_pickE, tot_gen_pickOneE]

theorem sok_anc02 (f iS sz : Nat) (b : List (EntityType × List EntityType)) : sok (Anc02 (f + 1) iS sz b) = 1 := by
  rw [Anc02, specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases sz with _ | s <;>
    refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      by norm_num, sok_pure _⟩ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
    tot_close [tot_gen_pickE, tot_gen_pickOneE]

theorem tot_anc02 : ∀ (fuel iS sz : Nat) (b : List (EntityType × List EntityType)), Tot (Anc02 fuel iS sz b)
  | 0, _, _, _ => by rw [Anc02, specimen_gen_Cedar_Validation_Relational_SchemaGen_Ancestors_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, b => tot_of_sok (sok_anc02 f iS sz b)

theorem tot_listString (n : Nat) : Tot (ArbitrarySized.arbitrarySized n : SGen (List String)) :=
  tot_of_sok (sok_arbListString n)

theorem tot_regime (n : Nat) : Tot (ArbitrarySized.arbitrarySized n : SGen HierRegime) :=
  tot_of_sok (sok_arbRegime n)

theorem tot_we : ∀ (fuel iS sz : Nat) (r : HierRegime) (b : List (EntityType × List EntityType)) (names : List EntityType),
    Tot (WE fuel iS sz r b names)
  | 0, _, _, _, _, _ => by rw [WE, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, r, b, names => by
    rw [WE, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> tot_open <;>
      tot_close [tot_we, tot_notIn, tot_attrs, tot_gen_tags, tot_anc, tot_listString]

theorem sok_we (f iS sz : Nat) (r : HierRegime) (b : List (EntityType × List EntityType)) (names : List EntityType) :
    sok (WE (f + 1) iS sz r b names) = 1 := by
  rw [WE, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases sz with _ | s <;>
    refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, sok_pure _⟩ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
    tot_close [tot_we, tot_notIn, tot_attrs, tot_gen_tags, tot_anc, tot_listString]

theorem tot_we0 : ∀ (fuel iS sz : Nat) (b : List (EntityType × List EntityType)) (names : List EntityType),
    Tot (WE0 fuel iS sz b names)
  | 0, _, _, _, _ => by rw [WE0, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, b, names => by
    rw [WE0, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> tot_open <;>
      tot_close [tot_we0, tot_we, tot_notIn, tot_attrs, tot_gen_tags, tot_anc02, tot_listString, tot_regime]

theorem sok_we0 (f iS sz : Nat) (b : List (EntityType × List EntityType)) (names : List EntityType) :
    sok (WE0 (f + 1) iS sz b names) = 1 := by
  rw [WE0, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases sz with _ | s <;>
    refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num,
      sok_bind_one (sok_arbRegime _) fun _ => sok_pure _⟩ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
    tot_close [tot_we0, tot_we, tot_notIn, tot_attrs, tot_gen_tags, tot_anc02, tot_listString, tot_regime]

/-- **The entity schema never fails.** -/
theorem sok_we1 (f iS sz : Nat) : sok (WE1 (f + 1) iS sz [] []) = 1 := by
  rw [WE1, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  have hstd : ∀ (iS : Nat), sok (do
      let et ← BacktrackGenFor.gen (P := fun et => Cedar.Validation.Relational.Schema.NotInET et []) (G := SGen) iS iS
      let attrs ← BacktrackGenFor.gen (P := fun attrs => Cedar.Validation.Relational.Schema.WfAttrs none [et] attrs) (G := SGen) iS iS
      let tags ← BacktrackGenFor.gen (P := fun tags => Cedar.Validation.Relational.Schema.WfTags [et] tags) (G := SGen) iS iS
      let p ← Anc02 (iS + 1) iS iS []
      let q ← WE (iS + 1) iS iS p.1 [(et, p.2)] [et]
      pure (p.1, q.1, (et, EntitySchemaEntry.standard
        { ancestors := Data.Set.mk p.2, attrs := Data.Map.mk attrs, tags := tags }) :: q.2)) = 1 := fun iS =>
    sok_bind_one (sok_gen_notIn_nil _ _) fun _ => sok_bind_one (sok_gen_attrs _ _ _ _) fun _ =>
      sok_bind_one (sok_gen_tags _ _ _) fun _ => sok_bind_one (sok_anc02 _ _ _ _) fun _ =>
        sok_bind_one (sok_we _ _ _ _ _ _) fun _ => sok_pure _
  rcases sz with _ | s <;>
    refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, hstd iS⟩ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
    tot_close [tot_we0, tot_we, tot_notIn, tot_attrs, tot_gen_tags, tot_anc02, tot_listString, tot_regime]


/-! ## The action workers -/

noncomputable abbrev WPT := @specimen_gen_Cedar_Validation_Relational_Schema_WfPrincipalTypes_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev WRT := @specimen_gen_Cedar_Validation_Relational_Schema_WfResourceTypes_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev RW := @specimen_gen_Cedar_Validation_Relational_SchemaGen_ResourcesWithin_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev ActAnc := @specimen_gen_Cedar_Validation_Relational_SchemaGen_ActAncestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev WB := @specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoB_5__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev WA := @specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoR_5_6__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _
noncomputable abbrev GT := @specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen SGen _ _ _ _ _ _

theorem sok_gen_eqAct (s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun x : EntityType => x = Cedar.Validation.Relational.Schema.actionEntityType) (G := SGen) s l) = 1 :=
  sok_pure _

theorem tot_gen_eqAct (s l : Nat) :
    Tot (BacktrackGenFor.gen (P := fun x : EntityType => x = Cedar.Validation.Relational.Schema.actionEntityType) (G := SGen) s l) :=
  tot_pure _

theorem tot_wpt : ∀ (fuel iS sz : Nat) (ets : List EntityType), Tot (WPT fuel iS sz ets)
  | 0, _, _, _ => by rw [WPT, specimen_gen_Cedar_Validation_Relational_Schema_WfPrincipalTypes_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, ets => by
    rw [WPT, specimen_gen_Cedar_Validation_Relational_Schema_WfPrincipalTypes_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> tot_open <;> tot_close [tot_wpt, tot_gen_defined]

theorem tot_wrt : ∀ (fuel iS sz : Nat) (ets : List EntityType), Tot (WRT fuel iS sz ets)
  | 0, _, _, _ => by rw [WRT, specimen_gen_Cedar_Validation_Relational_Schema_WfResourceTypes_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, ets => by
    rw [WRT, specimen_gen_Cedar_Validation_Relational_Schema_WfResourceTypes_1__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> tot_open <;> tot_close [tot_wrt, tot_gen_defined]

theorem tot_bt : ∀ (fuel iS sz : Nat) (ets : List EntityType) (b : Nat), Tot (Variety.BT fuel iS sz ets b)
  | 0, _, _, _, _ => by rw [Variety.BT, specimen_gen_Cedar_Validation_Relational_SchemaGen_BoundedTypes_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, ets, b => by
    rw [Variety.BT, specimen_gen_Cedar_Validation_Relational_SchemaGen_BoundedTypes_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases b with _ | b <;> tot_open <;> tot_close [tot_bt, tot_gen_defined]

theorem tot_cb : ∀ (fuel iS sz : Nat) (ets : List EntityType) (b : Nat), Tot (Variety.CB fuel iS sz ets b)
  | 0, _, _, _, _ => by rw [Variety.CB, specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, ets, b => by
    rw [Variety.CB, specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases b with _ | b <;> tot_open <;> tot_close [tot_cb, tot_bt, tot_gen_defined]

theorem tot_rw : ∀ (fuel iS sz : Nat) (ets : List EntityType) (b : Nat) (ps : List EntityType), Tot (RW fuel iS sz ets b ps)
  | 0, _, _, _, _, _ => by rw [RW, specimen_gen_Cedar_Validation_Relational_SchemaGen_ResourcesWithin_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, ets, b, ps => by
    rw [RW, specimen_gen_Cedar_Validation_Relational_SchemaGen_ResourcesWithin_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases ps with _ | ⟨p, ps⟩ <;> tot_open <;> tot_close [tot_wrt, tot_bt]

theorem tot_actAnc : ∀ (fuel iS sz : Nat) (r : HierRegime) (b : List (EntityUID × List EntityUID)), Tot (ActAnc fuel iS sz r b)
  | 0, _, _, _, _ => by rw [ActAnc, specimen_gen_Cedar_Validation_Relational_SchemaGen_ActAncestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, r, b => by
    rw [ActAnc, specimen_gen_Cedar_Validation_Relational_SchemaGen_ActAncestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> rcases r <;> tot_open <;> tot_close [tot_gen_pickA, tot_gen_pickOneA]

/-- With no actions before it, an action's ancestors are drawn surely, in every regime. -/
theorem sok_actAnc_nil (f iS sz : Nat) (r : HierRegime) : sok (ActAnc (f + 1) iS sz r []) = 1 := by
  rw [ActAnc, specimen_gen_Cedar_Validation_Relational_SchemaGen_ActAncestors_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases sz with _ | s <;> rcases r <;>
    simp only [List.filterMap_cons, List.filterMap_nil, Bool.false_eq_true, ↓reduceIte] <;>
    exact sok_backtrack_one _ (by simp [sumWeights]) (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq]
      first
        | exact sok_bind_one (sok_pickA_nil _ _ _) fun _ => sok_pure _
        | exact sok_bind_one (sok_pickOneAction _ _ _) fun _ => sok_pure _
        | exact sok_pure _)

theorem tot_wb : ∀ (fuel iS sz : Nat) (r : HierRegime) (ets : List EntityType) (built : List (EntityUID × List EntityUID))
    (avail : List String) (b : Nat), Tot (WB fuel iS sz r ets built avail b)
  | 0, _, _, _, _, _, _, _ => by rw [WB, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoB_5__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, r, ets, built, avail, b => by
    rw [WB, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoB_5__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> tot_open <;> tot_close [tot_gen_eqAct, tot_wb, tot_wpt, tot_attrs, tot_rw, tot_selRem, tot_actAnc]

theorem sok_wb (f iS sz : Nat) (r : HierRegime) (ets : List EntityType) (built : List (EntityUID × List EntityUID))
    (avail : List String) (b : Nat) : sok (WB (f + 1) iS sz r ets built avail b) = 1 := by
  rw [WB, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoB_5__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases sz with _ | s <;>
    refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, sok_pure _⟩ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] <;>
    tot_close [tot_gen_eqAct, tot_wb, tot_wpt, tot_attrs, tot_rw, tot_selRem, tot_actAnc]

theorem tot_wa : ∀ (fuel iS sz : Nat) (r : HierRegime) (ets : List EntityType) (built : List (EntityUID × List EntityUID))
    (avail : List String) (b : Nat), Tot (WA fuel iS sz r ets built avail b)
  | 0, _, _, _, _, _, _, _ => by rw [WA, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoR_5_6__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]; exact tot_outOfFuel
  | f + 1, iS, sz, r, ets, built, avail, b => by
    rw [WA, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoR_5_6__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s <;> tot_open <;>
      tot_close [tot_gen_eqAct, tot_wa, tot_wb, tot_wpt, tot_attrs, tot_rw, tot_selRem, tot_actAnc, tot_cb]


/-! ## The whole generator -/

theorem wfEntitiesGoR_names_sub {r built names allNames rest}
    (h : WfEntitiesGoR r built names allNames rest) : ∀ x ∈ names, x ∈ allNames := by
  induction h with
  | nil => exact fun _ hx => hx
  | standard => rename_i ih; exact fun x hx => ih x (List.mem_cons_of_mem _ hx)
  | enum => rename_i ih; exact fun x hx => ih x (List.mem_cons_of_mem _ hx)

theorem wfEntitiesGo1_names_ne_nil {r names entries}
    (h : WfEntitiesGo1 r [] [] names entries) : names ≠ [] := by
  cases h <;> rename_i h <;> exact List.ne_nil_of_mem (wfEntitiesGoR_names_sub h _ List.mem_cons_self)

/-- **The actions never fail** from no actions, a nonempty pool of names, some entity type and a budget
of at least one environment: the request's action is placed first surely, and every other try only
retries. -/
theorem sok_wa_top (f iS sz : Nat) (r : HierRegime) (ets : List EntityType) (avail : List String) (b : Nat)
    (hets : ets ≠ []) (havail : avail ≠ []) (hb : 1 ≤ b) : sok (WA (f + 1) iS sz r ets [] avail b) = 1 := by
  rw [WA, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoR_5_6__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases sz with _ | s <;>
    refine sok_backtrack_of_sure ?_ ⟨_, List.mem_cons_self, by norm_num, ?_⟩
  all_goals first
    | (simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
       tot_close [tot_gen_eqAct, tot_wa, tot_wb, tot_wpt, tot_attrs, tot_rw, tot_selRem, tot_actAnc, tot_cb]
       done)
    | (refine sok_bind_one (sok_gen_eqAct _ _) fun _ => ?_
       refine sok_bind_one (sok_gen_eqAct _ _) fun _ => ?_
       refine sok_bind_one (sok_gen_attrs _ _ _ _) fun _ => ?_
       refine sok_bind_one_of_support (Variety.cb_sok iS (iS + 1) iS ets b hets hb (by omega)) fun x hp => ?_
       obtain ⟨p, ps⟩ := x
       have hcb := specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
         (iS + 1) iS iS ets b (p, ps) hp
       have hlen := hcb.boundedTypes.length_le
       have hpos : 0 < ps.length := List.length_pos_iff.mpr hcb.definedEntityType.ne_nil
       refine sok_bind_one (Variety.cb_sok iS (iS + 1) iS ets _ hets (Nat.div_pos hlen hpos) (by omega)) fun _ => ?_
       refine sok_bind_one (sok_selRem iS iS iS String avail havail) fun _ => ?_
       refine sok_bind_one (sok_actAnc_nil _ _ _ _) fun _ => ?_
       exact sok_bind_one (sok_wb _ _ _ _ _ _ _ _) fun _ => sok_pure _)

theorem sok_gt (s l budget : Nat) (hb : 1 ≤ budget) : sok (GT (s + 1) l s budget) = 1 := by
  rw [GT, specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases s with _ | s <;>
    refine sok_backtrack_one _ (by simp [sumWeights]) ?_ <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq] <;>
    refine sok_bind_one_of_support (sok_we1 l l l) fun ⟨r, names, entries⟩ => fun hp => ?_ <;>
    have hne := (specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
      (l + 1) l l [] [] _ hp) |> wfEntitiesGo1_names_ne_nil <;>
    exact sok_bind_one (sok_wa_top l l l r names Cedar.Validation.Relational.Schema.actionEidPool budget hne
      (by simp [Cedar.Validation.Relational.Schema.actionEidPool]) hb) fun _ => sok_pure _


theorem envCount_pos_of_wf {env : TypeEnv} (h : Cedar.Validation.Relational.Schema.WfTypeEnv env) :
    0 < env.schema.environments.length := by
  rw [environments_length]
  cases h with
  | mk _ _ _ _ _ _ hreq => exact hreq.envCount_pos

/-- **Claim 7 (i): the schema generator, as its instance runs it, never fails when its budget allows one
request environment, and never succeeds otherwise.** Its action names are drawn without replacement
from the fixed pool `actionEidPool` (eleven names), but running out of names never makes it fail: the
search backtracks to placing the request's action earlier, and the first action, from the full pool,
is placed surely. -/
theorem genTypeEnvB_instance_sok (budget s l : Nat) :
    sok (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l) =
      if 1 ≤ budget then 1 else 0 := by
  split
  · exact sok_gt s l budget ‹_›
  · refine sok_eq_zero fun ⟨r, env⟩ h => ?_
    have := Sound.genTypeEnvB_instance_generated budget s l r env h
    have := envCount_pos_of_wf this.1
    omega

end Cedar.Validation.Relational.SchemaGen.Sure

#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_sok

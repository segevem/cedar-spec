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

import CedarGen.Relational.Sound.SchemaSure
import CedarGen.Relational.Sound.SparseAncestors

/-! # The schema generator's distribution, as its instance runs it

Proved of the derived code at `SGen`, for `BacktrackGenFor.gen (P := fun p => GenTypeEnvB p.1 b p.2) s l`:

* `genTypeEnvB_instance_varied` (Claim 7, distribution): with a budget `b ≥ 2`, the probability that
  a schema has two distinct request environments, given that it has at least two entity types, is at
  least `5/18` (the generator never fails, `genTypeEnvB_instance_sok`, so this is also given
  success); `genTypeEnvB_instance_varied_length`: so at least two request environments.
* `genTypeEnvB_instance_sparse_mean(_log)` (Claim 6, distribution): over the schemas produced in the
  sparse regime with a standard entity type, the mean ancestor closure of a uniformly chosen standard
  entity type is at most `H(l + 1) - 1 ≤ ln (l + 1)`, `l` the leaf size.

Lower bounds on a mean over successes (`MeanGe`) survive the search as upper ones do: they are
`MeanLeW` with the constant and the event swapped. -/

namespace Cedar.Validation.Relational.SchemaGen.Sure

open Cedar.Spec Cedar.Validation Cedar.Validation.Relational Cedar.Validation.Relational.Schema
open Specimen.Correctness Specimen.Backtrack Basalt ENNReal Sound

variable {A B : Type}

/-! ## Lower bounds on the mean over successes -/

/-- `g`'s mean of `f` over its successes is at least `c`. -/
def MeanGe (g : SGen A) (f : A → ℝ≥0∞) (c : ℝ≥0∞) : Prop := c * sok g ≤ sexpect g f

theorem meanGe_iff {g : SGen A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} : MeanGe g f c ↔ MeanLeW g (fun _ => c) f 1 := by
  unfold MeanGe MeanLeW; rw [sexpect_const', one_mul, mul_comm]

/-- **The search keeps a lower bound on the mean**, as it keeps an upper one. -/
theorem meanGe_backtrack {gs : List (Nat × (Unit → SGen A))} {f : A → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ p ∈ gs, MeanGe (p.2 ()) f c) : MeanGe (Specimen.Backtrack.backtrack gs) f c :=
  meanGe_iff.mpr (meanLeW_backtrack fun p hp => meanGe_iff.mp (h p hp))

theorem meanGe_bind_support {g : SGen A} {k : A → SGen B} {f : B → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, Produces g a → MeanGe (k a) f c) : MeanGe (g >>= k) f c :=
  meanGe_iff.mpr (meanLeW_bind_support fun a ha => meanGe_iff.mp (h a ha))

theorem meanGe_bind_const {g : SGen A} {k : A → SGen B} {f : B → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ a, MeanGe (k a) f c) : MeanGe (g >>= k) f c :=
  meanGe_bind_support fun a _ => h a

theorem meanGe_of_sok_zero {g : SGen A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} (h : sok g = 0) : MeanGe g f c := by
  unfold MeanGe; rw [h, mul_zero]; exact zero_le

theorem sok_truncations (ls : List (Specimen.Label A)) : sok (Specimen.truncations ls : SGen A) = 0 := by
  unfold Specimen.truncations; split <;> simp [sok]

/-- Where every success is in the event, the mean is at least any `c ≤ 1`. -/
theorem meanGe_of_all {g : SGen A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≤ 1)
    (h : ∀ a, Produces g a → 1 ≤ f a) : MeanGe g f c := by
  unfold MeanGe
  calc c * sok g ≤ 1 * sok g := by gcongr
    _ = sexpect g (fun _ => 1) := by rw [one_mul, sok]
    _ ≤ sexpect g f := sexpect_mono_support h

/-- A sure continuation that keeps the event. -/
theorem meanGe_bind_tail {g : SGen A} {k : A → SGen B} {f' : A → ℝ≥0∞} {f : B → ℝ≥0∞} {c : ℝ≥0∞}
    (hg : MeanGe g f' c) (hk : ∀ a, sok (k a) = 1) (hf : ∀ a, f' a ≤ sexpect (k a) f) :
    MeanGe (g >>= k) f c := by
  unfold MeanGe at *
  rw [sok_bind, sexpect_congr g hk, ← sok, sexpect_bind]
  exact hg.trans (sexpect_mono g hf)

theorem sok_bind_eq_support {g : SGen A} {k : A → SGen B} {q : ℝ≥0∞}
    (h : ∀ a, Produces g a → sok (k a) = q) : sok (g >>= k) = sok g * q := by
  rw [sok_bind, ← sexpect_const']
  exact le_antisymm (sexpect_mono_support fun a ha => (h a ha).le)
    (sexpect_mono_support fun a ha => (h a ha).ge)

theorem sok_bind_eq {g : SGen A} {k : A → SGen B} {q : ℝ≥0∞} (h : ∀ a, sok (k a) = q) :
    sok (g >>= k) = sok g * q :=
  sok_bind_eq_support fun a _ => h a

/-- **A draw with a chance of an event, then a continuation that succeeds equally often after any draw
and, after one in the event, only into `f`.** -/
theorem meanGe_bind_event {g : SGen A} {k : A → SGen B} {f : B → ℝ≥0∞} {V : Set A} {c q : ℝ≥0∞}
    (hg : sok g = 1) (hV : c ≤ sprob g V) (hq : ∀ a, Produces g a → sok (k a) = q)
    (hk : ∀ a, Produces g a → a ∈ V → q ≤ sexpect (k a) f) : MeanGe (g >>= k) f c := by
  unfold MeanGe
  rw [sok_bind_eq_support hq, hg, one_mul, sexpect_bind]
  calc c * q ≤ sprob g V * q := by gcongr
    _ = sexpect g (fun a => V.indicator 1 a * q) := by
        unfold sprob; rw [mul_comm, ← sexpect_mul_left]; exact sexpect_congr g fun a => mul_comm _ _
    _ ≤ sexpect g (fun a => sexpect (k a) f) := sexpect_mono_support fun a ha => by
        by_cases hv : a ∈ V
        · simpa [Set.indicator, hv] using hk a ha hv
        · simp [Set.indicator, hv]

/-! ## Combinations -/

/-- The (principal, action, resource) combinations the actions declare: a schema's request
environments, up to the context, which is the action's. -/
def combos (acts : List (EntityUID × ActionSchemaEntry)) : List (EntityType × EntityUID × EntityType) :=
  acts.flatMap fun x => (x.2.appliesToPrincipal.toList.product x.2.appliesToResource.toList).map
    fun pr => (pr.1, x.1, pr.2)

/-- At least two distinct combinations. -/
def Varied (acts : List (EntityUID × ActionSchemaEntry)) : Prop :=
  ∃ x ∈ combos acts, ∃ y ∈ combos acts, x ≠ y

theorem mem_product {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} {b : β} (ha : a ∈ l₁) (hb : b ∈ l₂) :
    (a, b) ∈ l₁.product l₂ := by
  simp only [List.product, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_combos_head {a : EntityUID} {e : ActionSchemaEntry} {acts} {p r : EntityType}
    (hp : p ∈ e.appliesToPrincipal.toList) (hr : r ∈ e.appliesToResource.toList) :
    (p, a, r) ∈ combos ((a, e) :: acts) := by
  simp only [combos, List.flatMap_cons, List.mem_append, List.mem_map]
  exact .inl ⟨(p, r), mem_product hp hr, rfl⟩

theorem mem_combos_tail {x : EntityUID × ActionSchemaEntry} {acts} {c} (h : c ∈ combos acts) :
    c ∈ combos (x :: acts) := by
  simp only [combos, List.flatMap_cons, List.mem_append] at h ⊢
  exact .inr h

theorem combos_action {acts : List (EntityUID × ActionSchemaEntry)} {c} (h : c ∈ combos acts) :
    ∃ x ∈ acts, c.2.1 = x.1 := by
  simp only [combos, List.mem_flatMap, List.mem_map] at h
  obtain ⟨x, hx, pr, -, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

theorem varied_cons {x : EntityUID × ActionSchemaEntry} {acts} (h : Varied acts) : Varied (x :: acts) := by
  obtain ⟨c, hc, d, hd, hne⟩ := h
  exact ⟨c, mem_combos_tail hc, d, mem_combos_tail hd, hne⟩

theorem requestFromAction_combos {ets acts reqty} (h : RequestFromAction ets acts reqty) :
    (reqty.principal, reqty.action, reqty.resource) ∈ combos acts := by
  induction h with
  | here _ _ _ _ _ _ _ _ hp hr => exact mem_combos_head (mem_of_definedEntityType hp) (mem_of_definedEntityType hr)
  | there _ _ _ _ ih => exact mem_combos_tail ih

theorem selectRemove_facts {α : Type} {xs : List α} {y : α} {ys : List α} (h : SelectRemove xs y ys) :
    y ∈ xs ∧ (∀ z ∈ ys, z ∈ xs) ∧ (xs.Nodup → y ∉ ys ∧ ys.Nodup) := by
  induction h with
  | here x xs => exact ⟨List.mem_cons_self, fun z hz => List.mem_cons_of_mem _ hz,
      fun hd => ⟨(List.nodup_cons.mp hd).1, (List.nodup_cons.mp hd).2⟩⟩
  | there x xs y ys _ ih =>
    refine ⟨List.mem_cons_of_mem _ ih.1, fun z hz => ?_, fun hd => ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih.2.1 z hz)
    · obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hd
      obtain ⟨hy, hys⟩ := ih.2.2 hxs
      refine ⟨fun hm => ?_, List.nodup_cons.mpr ⟨fun hx' => hx (ih.2.1 x hx'), hys⟩⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hx ih.1
      · exact hy hm

theorem wfActionsGo_eids {ets built avail acts} (h : WfActionsGo ets built avail acts) :
    ∀ x ∈ acts, x.1.eid ∈ avail := by
  induction h with
  | nil => simp
  | cons _ _ _ _ _ _ _ _ _ hsel _ _ _ _ _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (selectRemove_facts hsel).1
    · exact (selectRemove_facts hsel).2.1 _ (ih x hx)

/-- The request's action is among the actions, its name from the pool. -/
theorem wfActionsGoR_request {r ets built avail b acts reqty} (h : WfActionsGoR r ets built avail b acts reqty) :
    (reqty.principal, reqty.action, reqty.resource) ∈ combos acts ∧ reqty.action.eid ∈ avail := by
  have hw := h.wfActionsGo
  have hc := requestFromAction_combos hw.2
  obtain ⟨x, hx, hxa⟩ := combos_action hc
  have : reqty.action = x.1 := hxa
  exact ⟨hc, this ▸ wfActionsGo_eids hw.1 x hx⟩

theorem five_eighteenths (n : ℕ) (hn : 2 ≤ n) :
    (5 : ℝ≥0∞) / 18 ≤ 5 * ((((n - 1 : ℕ) : ℝ≥0∞) * 1) / (n : ℝ≥0∞)) / 9 := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hhalf : (1 : ℝ≥0∞) / 2 ≤ ((n - 1 : ℕ) : ℝ≥0∞) * 1 / n := by
    rw [mul_one, ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))]
    have h2 : (n : ℝ≥0∞) ≤ 2 * ((n - 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast (show n ≤ 2 * (n - 1) by omega)
    calc 1 / 2 * (n : ℝ≥0∞) ≤ 1 / 2 * (2 * ((n - 1 : ℕ) : ℝ≥0∞)) := by gcongr
      _ = ((n - 1 : ℕ) : ℝ≥0∞) := by
        rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  calc (5 : ℝ≥0∞) / 18 = 5 * (1 / 2) / 9 := by
        have h : (18 : ℝ≥0∞) = 2 * 9 := by norm_num
        rw [h, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp), mul_one_div,
          div_eq_mul_inv, mul_assoc]
    _ ≤ _ := by gcongr

/-- A draw with a chance of an event, then a continuation that succeeds equally often after any draw
and, after one in the event, only into `f`. -/
theorem meanGe_bind_event' {g : SGen A} {k : A → SGen B} {f : B → ℝ≥0∞} {V : Set A} {c q : ℝ≥0∞}
    (hg : sok g = 1) (hV : c ≤ sprob g V) (hq : ∀ a, Produces g a → sok (k a) = q)
    (hk : ∀ a, Produces g a → a ∈ V → ∀ o, Produces (k a) o → 1 ≤ f o) : MeanGe (g >>= k) f c :=
  meanGe_bind_event hg hV hq fun a ha hv => by
    rw [← hq a ha, sok]; exact sexpect_mono_support (hk a ha hv)

/-- Whether the actions declare two combinations. -/
noncomputable def evVar : (List (EntityUID × ActionSchemaEntry) × RequestType) → ℝ≥0∞ :=
  Set.indicator {o | Varied o.1} 1

theorem one_le_evVar {o : List (EntityUID × ActionSchemaEntry) × RequestType} (h : Varied o.1) :
    1 ≤ evVar o := by
  simp [evVar, Set.indicator, h]

set_option hygiene false in
/-- The request's branch. -/
local macro "req_varied" : tactic => `(tactic| (
       refine meanGe_bind_const fun unk => meanGe_bind_const fun _ => meanGe_bind_const fun ctx => ?_
       refine meanGe_bind_event' (V := {x | ∃ z ∈ x.2, z ≠ x.1})
         (q := sok (SelRem (iS + 1) iS iS String avail) * sok (ActAnc (iS + 1) iS iS r built))
         (Variety.cb_sok iS (iS + 1) iS ets b hne (by omega) (by omega))
         ((five_eighteenths _ hn).trans (Variety.cb_variety iS (iS + 1) iS ets b hd hne hb hiS (by omega)))
         ?_ ?_
       · rintro ⟨p, ps⟩ hp
         have hcb := specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
           (iS + 1) iS iS ets b (p, ps) hp
         have hpos : 0 < ps.length := List.length_pos_iff.mpr hcb.definedEntityType.ne_nil
         dsimp only
         refine (sok_bind_eq (q := sok (SelRem (iS + 1) iS iS String avail) * sok (ActAnc (iS + 1) iS iS r built))
           fun y => ?_).trans ?_
         · obtain ⟨res, rs⟩ := y
           dsimp only
           refine (sok_bind_eq (q := sok (ActAnc (iS + 1) iS iS r built)) fun z => ?_).trans rfl
           obtain ⟨eid, av'⟩ := z
           dsimp only
           exact (sok_bind_eq (q := 1) fun anc => sok_bind_one (sok_wb _ _ _ _ _ _ _ _) fun _ => sok_pure _).trans
             (mul_one _)
         · exact (congrArg (· * _) (Variety.cb_sok iS (iS + 1) iS ets (b / ps.length) hne
             (Nat.div_pos hcb.boundedTypes.length_le hpos) (by omega))).trans (one_mul _)
       · rintro ⟨p, ps⟩ hp ⟨z, hz, hzp⟩ o ho
         have hcb := specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
           (iS + 1) iS iS ets b (p, ps) hp
         simp only [produces_bind_iff, produces_pure_iff, Prod.exists] at ho
         obtain ⟨res, rs, hres, eid, av', -, anc, -, rest, -, rfl⟩ := ho
         have hcr := specimen_gen_Cedar_Validation_Relational_SchemaGen_ContainsBounded_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
           (iS + 1) iS iS ets _ (res, rs) hres
         apply one_le_evVar
         exact ⟨_, mem_combos_head (mem_of_definedEntityType hcb.definedEntityType)
             (mem_of_definedEntityType hcr.definedEntityType),
           _, mem_combos_head hz (mem_of_definedEntityType hcr.definedEntityType),
           fun h => hzp (congrArg Prod.fst h).symm⟩))

/-- **The actions are varied.** With at least two distinct entity types, a budget of at least two
environments, distinct names to draw from and a leaf size of at least one, the actions, over their
successes, declare two distinct combinations with probability at least `5/18`: the request's action,
drawn first, has a second principal with probability at least `5/9 · (1 - 1/n) ≥ 5/18`; an action
drawn before it either declares a combination of its own, distinct from the request's by its name,
or leaves the budget whole. -/
theorem wa_varied (iS : Nat) (hiS : 1 ≤ iS) (r : HierRegime) (ets : List EntityType) (hd : ets.Nodup)
    (hn : 2 ≤ ets.length) : ∀ (fuel sz : Nat) (built : List (EntityUID × List EntityUID))
    (avail : List String) (b : Nat), avail.Nodup → 2 ≤ b →
    MeanGe (WA fuel iS sz r ets built avail b) evVar (5 / 18)
  | 0, _, _, _, _, _, _ => by
    rw [WA, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoR_5_6__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    exact meanGe_of_sok_zero (by simp [sok])
  | f + 1, sz, built, avail, b, hav, hb => by
    have hne : ets ≠ [] := List.ne_nil_of_length_pos (by omega)
    rw [WA, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoR_5_6__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    rcases sz with _ | s
    · refine meanGe_backtrack ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by req_varied, meanGe_of_sok_zero (sok_truncations _)⟩
    · refine meanGe_backtrack ?_
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨by req_varied, ?_⟩
      refine meanGe_bind_const fun unk => meanGe_bind_const fun ps => meanGe_bind_const fun _ =>
        meanGe_bind_const fun rs => ?_
      refine meanGe_bind_support fun z hz => ?_
      obtain ⟨eid, av'⟩ := z
      have hsel := specimen_gen_Cedar_Validation_Relational_Schema_SelectRemove_2_3__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
        (iS + 1) iS iS String avail (eid, av') hz
      obtain ⟨heid, hav'⟩ := (selectRemove_facts hsel).2.2 hav
      refine meanGe_bind_const fun anc => ?_
      by_cases h0 : ps.length * rs.length = 0
      · refine meanGe_bind_tail (wa_varied iS hiS r ets hd hn f s _ av' _ hav' (by rw [h0]; omega))
          (fun _ => sok_pure _) fun ⟨rest, g5⟩ => ?_
        rw [sexpect_pure]
        by_cases hv : Varied rest
        · exact (by simp [evVar, Set.indicator, hv] : evVar (rest, g5) ≤ 1).trans
            (one_le_evVar (varied_cons hv))
        · simp [evVar, Set.indicator, hv]
      · refine meanGe_of_all (ENNReal.div_le_of_le_mul (by norm_num)) fun o ho => ?_
        simp only [produces_bind_iff, produces_pure_iff, Prod.exists] at ho
        obtain ⟨rest, g5, hrest, rfl⟩ := ho
        have hw := wfActionsGoR_request
          (specimen_gen_Cedar_Validation_Relational_SchemaGen_WfActionsGoR_5_6__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
            _ _ _ _ _ _ _ _ (rest, g5) hrest)
        obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil ps (by rintro rfl; simp at h0)
        obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil rs (by rintro rfl; simp at h0)
        apply one_le_evVar
        refine ⟨_, mem_combos_head hp0 hr0, _, mem_combos_tail hw.1, fun h => heid ?_⟩
        have : (⟨unk, eid⟩ : EntityUID) = g5.action := congrArg (fun x => x.2.1) h
        rw [show eid = g5.action.eid from congrArg EntityUID.eid this]
        exact hw.2


/-! ## The whole generator -/

theorem notInET_not_mem {et : EntityType} {names : List EntityType} (h : NotInET et names) : et ∉ names := by
  induction h with
  | nil => simp
  | cons _ _ hne _ ih => simp only [List.mem_cons, not_or]; exact ⟨hne, ih⟩

theorem wfEntitiesGoR_names {r built names allNames rest} (h : WfEntitiesGoR r built names allNames rest) :
    names.Nodup → allNames.Nodup ∧ allNames.length = names.length + rest.length := by
  induction h with
  | nil => intro hd; exact ⟨hd, by simp⟩
  | standard _ _ _ _ _ _ _ _ hnot _ _ _ _ ih =>
    intro hd
    obtain ⟨h1, h2⟩ := ih (List.nodup_cons.mpr ⟨notInET_not_mem hnot, hd⟩)
    exact ⟨h1, by simp only [List.length_cons] at h2 ⊢; omega⟩
  | enum _ _ _ _ _ _ hnot _ ih =>
    intro hd
    obtain ⟨h1, h2⟩ := ih (List.nodup_cons.mpr ⟨notInET_not_mem hnot, hd⟩)
    exact ⟨h1, by simp only [List.length_cons] at h2 ⊢; omega⟩

/-- The entity schema's names are distinct, one per entry. -/
theorem wfEntitiesGo1_names {r names entries} (h : WfEntitiesGo1 r [] [] names entries) :
    names.Nodup ∧ names.length = entries.length := by
  cases h <;> rename_i h <;>
    obtain ⟨h1, h2⟩ := wfEntitiesGoR_names h (List.nodup_singleton _) <;>
    exact ⟨h1, by simp only [List.length_cons, List.length_nil] at h2 ⊢; omega⟩

/-- A combination is a request environment's. -/
theorem mem_environments {ets : EntitySchema} {acts : List (EntityUID × ActionSchemaEntry)} {reqty : RequestType}
    {c : EntityType × EntityUID × EntityType} (h : c ∈ combos acts) :
    ∃ e ∈ (TypeEnv.mk ets (Cedar.Data.Map.mk acts) reqty).schema.environments,
      (e.reqty.principal, e.reqty.action, e.reqty.resource) = c := by
  simp only [combos, List.mem_flatMap, List.mem_map] at h
  obtain ⟨⟨a, e⟩, hae, ⟨p, r⟩, hpr, rfl⟩ := h
  refine ⟨⟨ets, Cedar.Data.Map.mk acts, ⟨p, a, r, e.context⟩⟩, ?_, rfl⟩
  show _ ∈ List.map _ (List.flatMap _ acts)
  refine List.mem_map.mpr ⟨⟨p, a, r, e.context⟩, List.mem_flatMap.mpr ⟨(a, e), hae, ?_⟩, rfl⟩
  show _ ∈ List.map _ (List.product _ _)
  exact List.mem_map.mpr ⟨(p, r), hpr, rfl⟩

/-- Two distinct combinations, two distinct request environments. -/
theorem varied_environments {ets : EntitySchema} {acts : List (EntityUID × ActionSchemaEntry)} {reqty : RequestType}
    (h : Varied acts) :
    ∃ e₁ ∈ (TypeEnv.mk ets (Cedar.Data.Map.mk acts) reqty).schema.environments,
      ∃ e₂ ∈ (TypeEnv.mk ets (Cedar.Data.Map.mk acts) reqty).schema.environments, e₁ ≠ e₂ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  obtain ⟨e₁, h₁, rfl⟩ := mem_environments (ets := ets) (reqty := reqty) hx
  obtain ⟨e₂, h₂, rfl⟩ := mem_environments (ets := ets) (reqty := reqty) hy
  exact ⟨e₁, h₁, e₂, h₂, fun h => hxy (h ▸ rfl)⟩

/-- At leaf size `0` the entity schema declares one type. -/
theorem we_size0 {f iS : Nat} {r : HierRegime} {b : List (EntityType × List EntityType)} {names : List EntityType}
    {out : List EntityType × List (EntityType × EntitySchemaEntry)} (h : Produces (WE (f + 1) iS 0 r b names) out) :
    out.2 = [] := by
  rw [WE, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def] at h
  simp only [produces_backtrack_iff, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
    exists_eq_left, produces_truncations_iff] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [produces_pure_iff] at h; rw [h]
  · exact h.elim

theorem we0_size0 {f iS : Nat} {b : List (EntityType × List EntityType)} {names : List EntityType}
    {out : HierRegime × List EntityType × List (EntityType × EntitySchemaEntry)} (h : Produces (WE0 (f + 1) iS 0 b names) out) :
    out.2.2 = [] := by
  rw [WE0, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGoR_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def] at h
  simp only [produces_backtrack_iff, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
    exists_eq_left, produces_truncations_iff] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [produces_bind_iff, produces_pure_iff] at h
    obtain ⟨_, -, rfl⟩ := h; rfl
  · exact h.elim

theorem we1_size0 {f : Nat} {out : HierRegime × List EntityType × List (EntityType × EntitySchemaEntry)}
    (h : Produces (WE1 (f + 1) 0 0 [] []) out) : out.2.2.length = 1 := by
  rw [WE1, specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def] at h
  simp only [produces_backtrack_iff, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
    exists_eq_left] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [produces_bind_iff, produces_pure_iff, Prod.exists] at h
    obtain ⟨_, -, _, -, _, -, _, _, -, _, _, hwe, rfl⟩ := h
    have h0 := we_size0 (f := 0) (iS := 0) hwe
    simp only at h0
    simp [h0]
  · simp only [produces_bind_iff, produces_pure_iff, Prod.exists] at h
    obtain ⟨_, -, _, _, _, hwe, _, -, rfl⟩ := h
    have h0 := we0_size0 (f := 0) (iS := 0) hwe
    simp only at h0
    simp [h0]


theorem single_branch_le {b : Unit → SGen A} {E F : Set A} {c : ℝ≥0∞} (hb : sok (b ()) = 1)
    (h : c * sprob (b ()) E ≤ sprob (b ()) F) :
    c * sprob (Specimen.Backtrack.backtrack [(1, b)]) E ≤ sprob (Specimen.Backtrack.backtrack [(1, b)]) F := by
  unfold sprob at *
  rw [sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by simpa using hb),
    sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by simpa using hb)]
  simpa [sumWeights] using h

theorem actionEidPool_nodup : actionEidPool.Nodup := by decide

/-- **Claim 7 (ii): schemas are varied.** As its instance runs it, with a budget of at least two
request environments, the schema generator (which never fails, `genTypeEnvB_instance_sok`) produces
a schema with two distinct request environments, given that it has at least two entity types, with
probability at least `5/18`. -/
theorem genTypeEnvB_instance_varied (budget s l : Nat) (hb : 2 ≤ budget) :
    5 / 18 * sprob (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) {p | 2 ≤ p.2.ets.toList.length} ≤
      sprob (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l)
        {p | 2 ≤ p.2.ets.toList.length ∧
          ∃ e₁ ∈ p.2.schema.environments, ∃ e₂ ∈ p.2.schema.environments, e₁ ≠ e₂} := by
  show 5 / 18 * sprob (GT (s + 1) l s budget) _ ≤ sprob (GT (s + 1) l s budget) _
  rw [GT, specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
  rcases s with _ | s <;> refine single_branch_le ?_ ?_
  all_goals first
    | (refine sok_bind_one_of_support (sok_we1 l l l) fun ⟨r, names, entries⟩ => fun hp => ?_
       have hne := wfEntitiesGo1_names_ne_nil
         (specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
           (l + 1) l l [] [] _ hp)
       exact sok_bind_one (sok_wa_top l l l r names actionEidPool budget hne
         (by simp [actionEidPool]) (by omega)) fun _ => sok_pure _)
    | (unfold sprob
       rw [sexpect_bind, sexpect_bind, ← sexpect_mul_left]
       refine sexpect_mono_support fun o ho => ?_
       obtain ⟨r, names, entries⟩ := o
       have hw := specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
         (l + 1) l l [] [] _ ho
       obtain ⟨hnd, hlen⟩ := wfEntitiesGo1_names hw
       dsimp only
       rw [sexpect_bind, sexpect_bind]
       by_cases h2 : 2 ≤ entries.length
       · have hl : 1 ≤ l := by
           rcases Nat.eq_zero_or_pos l with rfl | h
           · have := we1_size0 (f := 0) ho; simp only at this; omega
           · exact h
         have hva := wa_varied l hl r names hnd (hlen ▸ h2) (l + 1) l [] actionEidPool budget
           actionEidPool_nodup hb
         unfold MeanGe at hva
         calc _ = 5 / 18 * sok (WA (l + 1) l l r names [] actionEidPool budget) := by
                congr 1; unfold sok
                exact sexpect_congr _ fun x => by
                  obtain ⟨acts, reqty⟩ := x
                  simp [sexpect_pure, Set.indicator, Cedar.Data.Map.toList, h2]
           _ ≤ sexpect (WA (l + 1) l l r names [] actionEidPool budget) evVar := hva
           _ ≤ _ := sexpect_mono _ fun x => by
                obtain ⟨acts, reqty⟩ := x
                rw [sexpect_pure]
                by_cases hv : Varied acts
                · refine (by simp [evVar, Set.indicator, hv] : evVar (acts, reqty) ≤ 1).trans (le_of_eq ?_)
                  have := varied_environments (ets := Cedar.Data.Map.mk entries) (reqty := reqty) hv
                  exact (Set.indicator_of_mem (show _ ∈ {p : HierRegime × TypeEnv | 2 ≤ p.2.ets.toList.length ∧
                    ∃ e₁ ∈ p.2.schema.environments, ∃ e₂ ∈ p.2.schema.environments, e₁ ≠ e₂} from
                    ⟨by simpa [Cedar.Data.Map.toList] using h2, this⟩) 1).symm
                · simp [evVar, Set.indicator, hv]
       · refine le_of_eq_of_le ?_ zero_le
         rw [mul_eq_zero]; right
         refine (sexpect_congr _ fun x => ?_).trans (sexpect_zero_fun _)
         obtain ⟨acts, reqty⟩ := x
         simp [sexpect_pure, Set.indicator, Cedar.Data.Map.toList, h2])



theorem two_le_length_of_ne {α : Type} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    2 ≤ l.length := by
  match l, ha, hb with
  | [], ha, _ => simp at ha
  | [x], ha, hb => exact absurd ((List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm) hne
  | _ :: _ :: _, _, _ => simp

theorem sexpect_congr_support {g : SGen A} {f f' : A → ℝ≥0∞} (h : ∀ a, Produces g a → f a = f' a) :
    sexpect g f = sexpect g f' :=
  le_antisymm (sexpect_mono_support fun a ha => (h a ha).le) (sexpect_mono_support fun a ha => (h a ha).ge)

/-- Two distinct request environments: at least two. -/
theorem genTypeEnvB_instance_varied_length (budget s l : Nat) (hb : 2 ≤ budget) :
    5 / 18 * sprob (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) {p | 2 ≤ p.2.ets.toList.length} ≤
      sprob (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) {p | 2 ≤ p.2.ets.toList.length ∧ 2 ≤ p.2.schema.environments.length} := by
  refine (genTypeEnvB_instance_varied budget s l hb).trans (sexpect_mono _ fun p => ?_)
  refine Set.indicator_le_indicator_of_subset ?_ (fun _ => zero_le) p
  rintro p ⟨h2, e₁, h₁, e₂, h₂, hne⟩
  exact ⟨h2, two_le_length_of_ne h₁ h₂ hne⟩

/-! ## Claim 6, for the whole generator -/

theorem single_branch_eq {b : Unit → SGen A} (hb : sok (b ()) = 1) (f : A → ℝ≥0∞) :
    sexpect (Specimen.Backtrack.backtrack [(1, b)]) f = sexpect (b ()) f := by
  rw [sexpect_backtrack_eq _ _ (by simp [sumWeights]) (by simpa using hb)]
  simp [sumWeights]

theorem sexpect_const_eq {g : SGen A} {f : A → ℝ≥0∞} {c : ℝ≥0∞} (hg : sok g = 1) (h : ∀ x, f x = c) :
    sexpect g f = c := by
  rw [sexpect_congr g h, sexpect_const', hg, one_mul]

/-- **Claim 6, for the schema generator as its instance runs it.** At leaf size `l`, over the schemas
it produces in the sparse regime with at least one standard entity type, the mean number of ancestors
of a uniformly chosen standard entity type (the size of its ancestor closure, itself not counted) is
at most `H(l + 1) - 1`. The size `s` plays no part: every part is drawn at the leaf size. -/
theorem genTypeEnvB_instance_sparse_mean (budget s l : Nat) :
    sexpect (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l)
        (fun p => if p.1 = .sparse then ENNReal.ofReal (meanAnc p.2.ets.toList) else 0) ≤
      ENNReal.ofReal ((harmonic (l + 1) : ℝ) - 1) *
        sprob (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l)
          {p | p.1 = .sparse ∧ 1 ≤ (ancStats p.2.ets.toList).2} := by
  by_cases hb : 1 ≤ budget
  · show sexpect (GT (s + 1) l s budget) _ ≤ _ * sprob (GT (s + 1) l s budget) _
    rw [GT, specimen_gen_Cedar_Validation_Relational_SchemaGen_GenTypeEnvB_0_2__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.eq_def]
    have hE := entities1_sparse_mean l
    rcases s with _ | s <;> unfold sprob <;> rw [single_branch_eq ?_, single_branch_eq ?_]
    all_goals first
      | (refine sok_bind_one_of_support (sok_we1 l l l) fun ⟨r, names, entries⟩ => fun hp => ?_
         have hne := wfEntitiesGo1_names_ne_nil
           (specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
             (l + 1) l l [] [] _ hp)
         exact sok_bind_one (sok_wa_top l l l r names actionEidPool budget hne
           (by simp [actionEidPool]) hb) fun _ => sok_pure _)
      | (rw [sexpect_bind, sexpect_bind]
         refine le_of_eq_of_le (sexpect_congr_support ?_) (hE.trans_eq (congrArg _ (sexpect_congr_support ?_)))
         all_goals
           rintro ⟨r, names, entries⟩ hp
           have hne := wfEntitiesGo1_names_ne_nil
             (specimen_gen_Cedar_Validation_Relational_SchemaGen_WfEntitiesGo1_0_3_4__CedarGen_Relational_SchemaGen_Cedar_Validation_Relational_SchemaGen.sound
               (l + 1) l l [] [] _ hp)
           have hwa := sok_wa_top l l l r names actionEidPool budget hne (by simp [actionEidPool]) hb
           dsimp only
           rw [sexpect_bind]
           first
             | (refine sexpect_const_eq hwa fun x => ?_
                obtain ⟨acts, reqty⟩ := x
                simp [sexpect_pure, Set.indicator, Cedar.Data.Map.toList])
             | (refine (sexpect_const_eq hwa fun x => ?_).symm
                obtain ⟨acts, reqty⟩ := x
                simp [sexpect_pure, Set.indicator, Cedar.Data.Map.toList]))
  · have h0 : ∀ x, ¬ Produces (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2)
        (G := SGen) s l) x := fun ⟨r, env⟩ h => by
      have := Sound.genTypeEnvB_instance_generated budget s l r env h
      have := envCount_pos_of_wf this.1
      omega
    refine le_of_eq_of_le ?_ zero_le
    exact le_antisymm ((sexpect_mono_support fun x hx => (h0 x hx).elim).trans_eq (sexpect_zero_fun _)) zero_le

/-- …at most `ln (l + 1)`. -/
theorem genTypeEnvB_instance_sparse_mean_log (budget s l : Nat) :
    sexpect (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l)
        (fun p => if p.1 = .sparse then ENNReal.ofReal (meanAnc p.2.ets.toList) else 0) ≤
      ENNReal.ofReal (Real.log (l + 1)) *
        sprob (BacktrackGenFor.gen (P := fun p : HierRegime × TypeEnv => GenTypeEnvB p.1 budget p.2) (G := SGen) s l)
          {p | p.1 = .sparse ∧ 1 ≤ (ancStats p.2.ets.toList).2} := by
  refine (genTypeEnvB_instance_sparse_mean budget s l).trans ?_
  gcongr
  have := harmonic_sub_one_le_log (l + 1)
  push_cast at this
  exact this

end Cedar.Validation.Relational.SchemaGen.Sure

#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_sparse_mean_log
#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_varied
#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_varied_length
#print axioms Cedar.Validation.Relational.SchemaGen.Sure.genTypeEnvB_instance_sparse_mean

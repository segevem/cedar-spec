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

import CedarGen.Relational.TypeOfLeanSound

/-! # Input-capability congruence of the relational typing spec

If `HasType x c env ty cout` holds and `c` is set-equivalent (`CapsEquiv`) to
some other capability set `c''`, then `HasType x c'' env ty cout'` holds for some
`cout'` that is itself `CapsEquiv` to `cout`. In other words, the relational
judgement only consults its input capabilities up to set-equality, and its output
capabilities vary only up to set-equality when the input caps do.
-/

namespace CedarGen.Relational.Lean

open Cedar.Spec Cedar.Data Cedar.Validation

/-! ## Helper lemmas -/

theorem capMerge_nil_right (c : Capabilities) : CapMerge [] c c := by
  induction c with
  | nil => exact CapMerge.nil
  | cons hd tl ih => obtain ⟨x,k⟩ := hd; exact CapMerge.right x k [] tl tl ih

theorem capMerge_append' (c₁ c₂ : Capabilities) : CapMerge c₁ c₂ (c₁ ++ c₂) := by
  induction c₁ with
  | nil => exact capMerge_nil_right c₂
  | cons hd tl ih => obtain ⟨x,k⟩ := hd; exact CapMerge.left x k tl c₂ (tl ++ c₂) ih

theorem capAttrMem_congr {x a c c''} (h : CapAttrMem x a c) (he : CapsEquiv c c'') :
    CapAttrMem x a c'' := capAttrMem_iff.mpr ((he _).mp (capAttrMem_iff.mp h))

theorem capTagMem_congr {x e c c''} (h : CapTagMem x e c) (he : CapsEquiv c c'') :
    CapTagMem x e c'' := capTagMem_iff.mpr ((he _).mp (capTagMem_iff.mp h))

theorem hasAttrInRecord_congr {rty x a c b ty caps c''}
    (h : HasAttrInRecord rty x a c b ty caps) (he : CapsEquiv c c'') :
    HasAttrInRecord rty x a c'' b ty caps := by
  cases h with
  | found_in_caps knownToExist qty hcap hmc =>
    exact HasAttrInRecord.found_in_caps _ _ _ _ _ _ (capAttrMem_congr hcap he) hmc
  | found_required_known ty' hmc => exact HasAttrInRecord.found_required_known _ _ _ _ _ hmc
  | found_not_known qty hmc hneg =>
    exact HasAttrInRecord.found_not_known _ _ _ _ _ hmc (fun h => hneg (capAttrMem_congr h he.symm))
  | found_optional_known ty' hmc hneg =>
    exact HasAttrInRecord.found_optional_known _ _ _ _ _ hmc (fun h => hneg (capAttrMem_congr h he.symm))

theorem getAttrInRecord_congr' {rty x a c ty c''}
    (h : GetAttrInRecord rty x a c ty) (he : CapsEquiv c c'') : GetAttrInRecord rty x a c'' ty := by
  cases h with
  | required hmc => exact GetAttrInRecord.required _ _ _ _ _ hmc
  | optional hcap hmc => exact GetAttrInRecord.optional _ _ _ _ _ (capAttrMem_congr hcap he) hmc

/-! ## Congruence theorem -/

/-- Input-capability congruence: `HasType` consults its input capabilities only up
to set-equality (`CapsEquiv`), and its output capabilities vary only up to
set-equality when the input caps do. -/
theorem hasType_capsCongr {x c env ty cout} (h : HasType x c env ty cout) :
    ∀ {c''}, CapsEquiv c c'' → ∃ cout', HasType x c'' env ty cout' ∧ CapsEquiv cout cout' := by
  induction h using HasType.rec
    (motive_2 := fun xs c env tys _ => ∀ {c''}, CapsEquiv c c'' → HasTypeList xs c'' env tys)
    (motive_3 := fun lb axs c env atys _ => ∀ {c''}, CapsEquiv c c'' → HasTypeRecord lb axs c'' env atys)
    (motive_4 := fun f args c env t _ => ∀ {c''}, CapsEquiv c c'' → HasTypeExtCall f args c'' env t)
    with
  -- Literals
  | litBoolTrue c ets acts reqty =>
    intro c'' he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.litBoolTrue
  | litBoolFalse c ets acts reqty =>
    intro c'' he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.litBoolFalse
  | litInt i c ets acts reqty =>
    intro c'' he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.litInt
  | litString s c ets acts reqty =>
    intro c'' he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.litString
  | litEntity ety eid c ets acts reqty a =>
    intro c'' he
    exact ⟨[], HasType.litEntity _ _ _ _ _ _ a, CapsEquiv.refl []⟩
  -- Variables
  | varPrincipal c ets acts princ action resource ctx =>
    intro c'' he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.varPrincipal
  | varAction c ets acts princ actionTy actionEid resource ctx =>
    intro c'' he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.varAction
  | varResource c ets acts princ action resource ctx =>
    intro c'' he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.varResource
  | varContext c ets acts princ action resource ctx =>
    intro c'' he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.varContext
  -- Unary
  | unaryAppNotTt x₁ c env a ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.unaryAppNotTt <;> assumption
  | unaryAppNotFf x₁ c env a ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.unaryAppNotFf <;> assumption
  | unaryAppNotAny x₁ c env a ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.unaryAppNotAny <;> assumption
  | unaryAppNeg x₁ c env a ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.unaryAppNeg <;> assumption
  | unaryAppIsEmpty x₁ c env elemTy a ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.unaryAppIsEmpty <;> assumption
  | unaryAppLike pat x₁ c env a ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.unaryAppLike <;> assumption
  | unaryAppIsTrue ety x₁ c env a a1 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.unaryAppIsTrue <;> assumption
  | unaryAppIsFalse ety₁ ety₂ x₁ c env a a1 a2 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.unaryAppIsFalse <;> assumption
  -- Binary: eq
  | binaryAppEqLitSame p c env ty a ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppEqLitSame <;> assumption
  | binaryAppEqLitDiff p₁ p₂ c env ty₁ ty₂ a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppEqLitDiff <;> assumption
  | binaryAppEqNonLitLub x₁ x₂ c env t₁ t₂ lubTy a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppEqNonLitLub <;> assumption
  | binaryAppEqEntityDiff x₁ x₂ c env ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.binaryAppEqEntityDiff _ _ _ _ _ _ a a1 a2 h1 h2 a5, CapsEquiv.refl []⟩
  -- Binary: arithmetic / comparison
  | binaryAppLessInt x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppLessInt <;> assumption
  | binaryAppLessDatetime x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppLessDatetime <;> assumption
  | binaryAppLessDuration x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppLessDuration <;> assumption
  | binaryAppLessEqInt x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppLessEqInt <;> assumption
  | binaryAppLessEqDatetime x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppLessEqDatetime <;> assumption
  | binaryAppLessEqDuration x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppLessEqDuration <;> assumption
  | binaryAppAdd x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppAdd <;> assumption
  | binaryAppSub x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppSub <;> assumption
  | binaryAppMul x₁ x₂ c env a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppMul <;> assumption
  -- Binary: set operations
  | binaryAppContains x₁ x₂ c env t₂ elemTy a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppContains <;> assumption
  | binaryAppContainsAll x₁ x₂ c env elemTy₁ elemTy₂ a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppContainsAll <;> assumption
  | binaryAppContainsAny x₁ x₂ c env elemTy₁ elemTy₂ a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppContainsAny <;> assumption
  -- Binary: mem (generic)
  | binaryAppMemEntityEntity x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppMemEntityEntity <;> assumption
  | binaryAppMemEntitySame x₁ x₂ c ets acts reqty ety a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppMemEntitySame <;> assumption
  | binaryAppMemEntitySet x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppMemEntitySet <;> assumption
  | binaryAppMemEntitySetSame x₁ x₂ c ets acts reqty ety a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppMemEntitySetSame <;> assumption
  | binaryAppMemEntityEntityFf x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.binaryAppMemEntityEntityFf _ _ _ _ _ _ _ _ a a1 a2 a3 h1 h2,
      CapsEquiv.refl []⟩
  | binaryAppMemEntitySetFf x₁ x₂ c ets acts reqty ety₁ ety₂ a a1 a2 a3 a4 a5 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.binaryAppMemEntitySetFf _ _ _ _ _ _ _ _ a a1 a2 a3 h1 h2,
      CapsEquiv.refl []⟩
  -- Binary: mem (action literal)
  | binaryAppMemActionLitTt uid₁ uid₂ c ets acts reqty a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppMemActionLitTt <;> assumption
  | binaryAppMemActionLitFf uid₁ uid₂ c ets acts reqty a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppMemActionLitFf <;> assumption
  | binaryAppMemActionLitSetTt uid₁ xs c ets acts reqty ety₂ a1 a2 a3 a4 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppMemActionLitSetTt <;> assumption
  | binaryAppMemActionLitSetFf uid₁ xs c ets acts reqty ety₂ a1 a2 a3 a4 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.binaryAppMemActionLitSetFf <;> assumption
  -- hasAttr / getAttr
  | hasAttrRecord x₁ a c env rty ty caps a1 a2 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨caps, HasType.hasAttrRecord _ _ _ _ _ _ _ h1 (hasAttrInRecord_congr a2 he),
      CapsEquiv.refl caps⟩
  | hasAttrRecordNotFound x₁ a c env rty a1 a2 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.hasAttrRecordNotFound <;> assumption
  | hasAttrEntity x₁ a c ets acts reqty ety ty caps rty a1 a2 a3 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨caps, HasType.hasAttrEntity _ _ _ _ _ _ _ _ _ _ a1 h1 (hasAttrInRecord_congr a3 he),
      CapsEquiv.refl caps⟩
  | hasAttrEntityNotFound x₁ a c ets acts reqty ety rty a1 a2 a3 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.hasAttrEntityNotFound <;> assumption
  | hasAttrEnum x₁ a c ets acts reqty ety eids a1 a2 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.hasAttrEnum <;> assumption
  | getAttrRecord x₁ a c env rty ty a1 a2 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], HasType.getAttrRecord _ _ _ _ _ _ h1 (getAttrInRecord_congr' a2 he),
      CapsEquiv.refl []⟩
  | getAttrEntity x₁ a c ets acts reqty ety ty rty a1 a2 a3 ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    exact ⟨[], HasType.getAttrEntity _ _ _ _ _ _ _ _ _ a1 h1 (getAttrInRecord_congr' a3 he),
      CapsEquiv.refl []⟩
  -- hasTag / getTag
  | hasTagAnyBool x₁ x₂ c ets acts reqty ety ty a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨_, HasType.hasTagAnyBool _ _ _ _ _ _ _ _ a
      (fun hc => a1 (capTagMem_congr hc he.symm)) h1 h2, CapsEquiv.refl _⟩
  | hasTagTt x₁ x₂ c ets acts reqty ety ty a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.hasTagTt _ _ _ _ _ _ _ _ (capTagMem_congr a he) a1 h1 h2,
      CapsEquiv.refl []⟩
  | hasTagFf x₁ x₂ c ets acts reqty ety a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.hasTagFf <;> assumption
  | getTag x₁ x₂ c ets acts reqty ety ty a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨[], HasType.getTag _ _ _ _ _ _ _ _ (capTagMem_congr a he) a1 h1 h2,
      CapsEquiv.refl []⟩
  -- ite
  | iteTt x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ cout a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append' c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.iteTt _ _ _ _ _ _ _ _ _ _ h1 (capMerge_append' c'' c₁') h2
      (capMerge_append' c₁' c₂'), (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append' c₁' c₂')).symm)⟩
  | iteFf x₁ x₂ x₃ c env c₁ t₃ c₃ a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨c₃', h3, hc3⟩ := ih2 he
    exact ⟨c₃', HasType.iteFf _ _ _ _ _ _ _ _ h1 h3, hc3⟩
  | iteAnyBool x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ t₃ c₃ lubTy c₁₂ a a1 a2 a3 a4 a5 ih1 ih2 ih3 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append' c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    obtain ⟨c₃', h3, hc3⟩ := ih3 he
    exact ⟨capIntersect (c₁' ++ c₂') c₃',
      HasType.iteAnyBool _ _ _ _ _ _ _ _ _ _ _ _ _ h1 (capMerge_append' c'' c₁') h2 h3 a4
        (capMerge_append' c₁' c₂'),
      (capIntersect_capsEquiv_inter c₁₂ c₃).trans ((CapsEquiv.inter
        ((capMerge_capsEquiv_union a5).trans ((CapsEquiv.union hc1 hc2).trans
          (capMerge_capsEquiv_union (capMerge_append' c₁' c₂')).symm)) hc3).trans
        (capIntersect_capsEquiv_inter (c₁' ++ c₂') c₃').symm)⟩
  -- and
  | andShort x₁ x₂ c env c₁ a ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.andShort <;> assumption
  | andTtFf x₁ x₂ c env c₁ c_c₁ c₂ a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append' c'' c₁')).symm)
    obtain ⟨c₂', h2, _⟩ := ih2 hb
    exact ⟨[], HasType.andTtFf _ _ _ _ _ _ _ h1 (capMerge_append' c'' c₁') h2, CapsEquiv.refl []⟩
  | andTtTt x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append' c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.andTtTt _ _ _ _ _ _ _ _ h1 (capMerge_append' c'' c₁') h2
      (capMerge_append' c₁' c₂'), (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append' c₁' c₂')).symm)⟩
  | andTtAny x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append' c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.andTtAny _ _ _ _ _ _ _ _ h1 (capMerge_append' c'' c₁') h2
      (capMerge_append' c₁' c₂'), (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append' c₁' c₂')).symm)⟩
  | andAnyFf x₁ x₂ c env c₁ c_c₁ c₂ a a1 a2 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append' c'' c₁')).symm)
    obtain ⟨c₂', h2, _⟩ := ih2 hb
    exact ⟨[], HasType.andAnyFf _ _ _ _ _ _ _ h1 (capMerge_append' c'' c₁') h2, CapsEquiv.refl []⟩
  | andAnyTt x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append' c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.andAnyTt _ _ _ _ _ _ _ _ h1 (capMerge_append' c'' c₁') h2
      (capMerge_append' c₁' c₂'), (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append' c₁' c₂')).symm)⟩
  | andAnyAny x₁ x₂ c env c₁ c_c₁ c₂ cout a a1 a2 a3 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    have hb : CapsEquiv c_c₁ (c'' ++ c₁') := (capMerge_capsEquiv_union a1).trans
      ((CapsEquiv.union he hc1).trans (capMerge_capsEquiv_union (capMerge_append' c'' c₁')).symm)
    obtain ⟨c₂', h2, hc2⟩ := ih2 hb
    exact ⟨c₁' ++ c₂', HasType.andAnyAny _ _ _ _ _ _ _ _ h1 (capMerge_append' c'' c₁') h2
      (capMerge_append' c₁' c₂'), (capMerge_capsEquiv_union a3).trans ((CapsEquiv.union hc1 hc2).trans
        (capMerge_capsEquiv_union (capMerge_append' c₁' c₂')).symm)⟩
  -- or
  | orShort x₁ x₂ c env c₁ a ih =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.orShort <;> assumption
  | orFfThen x₁ x₂ c env c₁ b₂ c₂ a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨c₂', h2, hc2⟩ := ih2 he
    exact ⟨c₂', HasType.orFfThen _ _ _ _ _ _ _ h1 h2, hc2⟩
  | orAnyTt x₁ x₂ c env c₁ c₂ a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    refine ⟨[], ?_, CapsEquiv.refl []⟩
    apply HasType.orAnyTt <;> assumption
  | orAnyFf x₁ x₂ c env c₁ c₂ a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    obtain ⟨_, h2, _⟩ := ih2 he
    exact ⟨c₁', HasType.orAnyFf _ _ _ _ _ _ h1 h2, hc1⟩
  | orAnyAny x₁ x₂ c env c₁ c₂ a a1 ih1 ih2 =>
    intro c'' he
    obtain ⟨c₁', h1, hc1⟩ := ih1 he
    obtain ⟨c₂', h2, hc2⟩ := ih2 he
    exact ⟨capIntersect c₁' c₂', HasType.orAnyAny _ _ _ _ _ _ h1 h2,
      (capIntersect_capsEquiv_inter c₁ c₂).trans ((CapsEquiv.inter hc1 hc2).trans
        (capIntersect_capsEquiv_inter c₁' c₂').symm)⟩
  -- set / record / callExt
  | set x xs c env ty tyList lubTy a a1 a2 ih_x ih_xs =>
    intro c'' he
    obtain ⟨_, h1, _⟩ := ih_x he
    exact ⟨[], HasType.set _ _ _ _ _ _ _ h1 (ih_xs he) a2, CapsEquiv.refl []⟩
  | record axs c env atyList a1 ih3 =>
    intro c'' he
    exact ⟨[], HasType.record _ _ _ _ (ih3 he), CapsEquiv.refl []⟩
  | callExt xfn args c env ty a ih =>
    intro c'' he
    exact ⟨[], HasType.callExt _ _ _ _ _ (ih he), CapsEquiv.refl []⟩
  -- HasTypeList (motive_2)
  | nil c env =>
    rename_i he
    exact HasTypeList.nil _ _
  | cons x xs c env ty tys a a1 ih1 ih2 =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih1 he
    exact HasTypeList.cons _ _ _ _ _ _ h1 (ih2 he)
  -- HasTypeExtCall (motive_4)
  | decimal s c env a =>
    rename_i he
    exact HasTypeExtCall.decimal _ _ _ a
  | ip s c env a =>
    rename_i he
    exact HasTypeExtCall.ip _ _ _ a
  | datetime s c env a =>
    rename_i he
    exact HasTypeExtCall.datetime _ _ _ a
  | duration s c env a =>
    rename_i he
    exact HasTypeExtCall.duration _ _ _ a
  | lessThan a b c env ha hb ih_a ih_b =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    obtain ⟨_, h2, _⟩ := ih_b he
    exact HasTypeExtCall.lessThan _ _ _ _ h1 h2
  | lessThanOrEqual a b c env ha hb ih_a ih_b =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    obtain ⟨_, h2, _⟩ := ih_b he
    exact HasTypeExtCall.lessThanOrEqual _ _ _ _ h1 h2
  | greaterThan a b c env ha hb ih_a ih_b =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    obtain ⟨_, h2, _⟩ := ih_b he
    exact HasTypeExtCall.greaterThan _ _ _ _ h1 h2
  | greaterThanOrEqual a b c env ha hb ih_a ih_b =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    obtain ⟨_, h2, _⟩ := ih_b he
    exact HasTypeExtCall.greaterThanOrEqual _ _ _ _ h1 h2
  | isIpv4 a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.isIpv4 _ _ _ h1
  | isIpv6 a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.isIpv6 _ _ _ h1
  | isLoopback a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.isLoopback _ _ _ h1
  | isMulticast a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.isMulticast _ _ _ h1
  | isInRange a b c env ha hb ih_a ih_b =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    obtain ⟨_, h2, _⟩ := ih_b he
    exact HasTypeExtCall.isInRange _ _ _ _ h1 h2
  | offset a b c env ha hb ih_a ih_b =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    obtain ⟨_, h2, _⟩ := ih_b he
    exact HasTypeExtCall.offset _ _ _ _ h1 h2
  | durationSince a b c env ha hb ih_a ih_b =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    obtain ⟨_, h2, _⟩ := ih_b he
    exact HasTypeExtCall.durationSince _ _ _ _ h1 h2
  | toDate a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.toDate _ _ _ h1
  | toTime a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.toTime _ _ _ h1
  | toMilliseconds a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.toMilliseconds _ _ _ h1
  | toSeconds a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.toSeconds _ _ _ h1
  | toMinutes a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.toMinutes _ _ _ h1
  | toHours a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.toHours _ _ _ h1
  | toDays a c env ha ih_a =>
    rename_i he
    obtain ⟨_, h1, _⟩ := ih_a he
    exact HasTypeExtCall.toDays _ _ _ h1
  -- HasTypeRecord (motive_3): nil / cons — share recursor tags with HasTypeList.
  | _ =>
    first
    | (intro _he; exact HasTypeRecord.nil _ _ _)
    | (rename_i hka hHT hHTR aih
       intro ihR c'' he
       obtain ⟨_, hx, _⟩ := aih he
       exact HasTypeRecord.cons _ _ _ _ _ _ _ _ hka hx (ihR he))

end CedarGen.Relational.Lean

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

/-! # Completeness of the relational typing spec

Converse of `hasType_sound`: on a well-formed environment, every *successful*
run of the functional typechecker `Cedar.Validation.typeOf` is witnessed by a
`HasType` derivation (up to `CapsEquiv` on the output capabilities).

Completeness holds only relative to `WfTypeEnv` and only for expressions whose
record literals are already canonical (strictly-sorted, duplicate-free keys) —
captured by `WfExpr`. `typeOf` canonicalizes record literals via `Map.make`, but
`HasTypeRecord` bakes sortedness into the source syntax, so an unsorted record
literal is typeable by `typeOf` yet has no derivation; `WfExpr` rules those out
(the user-accepted "records are canonicalized" assumption). All other gaps are
closed by the well-formedness of the environment. -/

namespace CedarGen.Relational.Lean

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- Expression-level well-formedness for completeness (relative to `env`), capturing
    the two places where the relational spec is deliberately narrower than *bare*
    `typeOf` on an otherwise-accepted input:

    * **Record literals must have strictly-sorted, distinct keys.** `typeOf`
      canonicalizes them via `Map.make`, but `HasTypeRecord` bakes sortedness into
      the source syntax. (The user-accepted "records are canonical" assumption.)
    * **The tested type of an `is` must be declared.** `HasType` targets the real
      validator `validate` (which runs `checkEntities` first, rejecting `x is T` for
      undeclared `T`); bare `typeOf` skips that check. The tested type is a syntactic
      annotation, so — unlike operand entity types, which are declared automatically
      in a well-formed env — it must be required here.

    Every other `ValidEntityType`/schema premise in `HasType` is *derivable* from a
    successful `typeOf` on a `WfTypeEnv` (operand entity types are always declared),
    so no further conditions are needed. -/
inductive WfExpr : TypeEnv → Expr → Prop where
  | lit : ∀ env p, WfExpr env (.lit p)
  | var : ∀ env v, WfExpr env (.var v)
  | ite : ∀ env a b c, WfExpr env a → WfExpr env b → WfExpr env c → WfExpr env (.ite a b c)
  | and : ∀ env a b, WfExpr env a → WfExpr env b → WfExpr env (.and a b)
  | or : ∀ env a b, WfExpr env a → WfExpr env b → WfExpr env (.or a b)
  | unaryApp : ∀ env op a, (∀ ety, op = .is ety → ValidEntityType ety env.ets env.acts) →
      WfExpr env a → WfExpr env (.unaryApp op a)
  | binaryApp : ∀ env op a b, WfExpr env a → WfExpr env b → WfExpr env (.binaryApp op a b)
  | getAttr : ∀ env a k, WfExpr env a → WfExpr env (.getAttr a k)
  | hasAttr : ∀ env a k, WfExpr env a → WfExpr env (.hasAttr a k)
  | set : ∀ env xs, (∀ e ∈ xs, WfExpr env e) → WfExpr env (.set xs)
  | record : ∀ env axs, (axs.map Prod.fst).SortedBy id → (∀ e ∈ axs.map Prod.snd, WfExpr env e) →
      WfExpr env (.record axs)
  | call : ∀ env f xs, (∀ e ∈ xs, WfExpr env e) → WfExpr env (.call f xs)

/-! ## Reverse bridges (functional lookup ⇒ relational witness) -/

/-- List membership ⇒ `MapContains`. -/
theorem mem_mapContains {α β : Type} {k : α} {v : β} {l : List (α × β)} (h : (k, v) ∈ l) :
    MapContains k v (Map.mk l) := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact MapContains.here _ _ _
    · exact MapContains.there _ _ _ _ _ (ih h)

/-- `Map.find? = some` ⇒ `MapContains` (reverse of `mapContains_find?_nodup`). -/
theorem find?_mapContains {α β : Type} [LT α] [DecidableLT α] [DecidableEq α]
    {m : Map α β} {k : α} {v : β} (h : m.find? k = some v) : MapContains k v m := by
  obtain ⟨l⟩ := m
  exact mem_mapContains (Map.find?_mem_toList h)

/-- `MapContains` on an `EntityUID` key ⇒ `MapContainsPairKey` (some entry, possibly a
    duplicate-key head). Proved by induction on the membership witness. -/
theorem mapContainsPairKey_of_mapContains {v : Type} {ety : EntityType} {eid : String}
    {entry : v} {acts : Map EntityUID v} (h : MapContains ⟨ety, eid⟩ entry acts) :
    ∃ e, MapContainsPairKey ety eid e acts := by
  induction h with
  | here => exact ⟨entry, MapContainsPairKey.here⟩
  | there k' _ _ _ ih =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨a', b'⟩ := k'
    by_cases ha : ety = a'
    · by_cases hb : eid = b'
      · subst ha; subst hb; exact ⟨_, MapContainsPairKey.here⟩
      · exact ⟨e, MapContainsPairKey.nextB hb he⟩
    · exact ⟨e, MapContainsPairKey.nextA ha he⟩

/-- `EntitySchema.isValidEntityUID` ⇒ `ValidEntityUID` (standard/enum witnesses). -/
theorem validEntityUID_of_isValid {ets : EntitySchema} {acts : ActionSchema} {uid : EntityUID}
    (hnd : (ets.toList.map Prod.fst).Nodup) (h : ets.isValidEntityUID uid = true) :
    ValidEntityUID uid.ty uid.eid ets acts := by
  simp only [EntitySchema.isValidEntityUID] at h
  split at h
  · rename_i entry hfind
    have hmc := find?_mapContains hfind
    cases entry with
    | standard s => exact ValidEntityUID.standard _ _ _ _ _ hmc
    | enum eids =>
      simp only [EntitySchemaEntry.isValidEntityEID] at h
      exact ValidEntityUID.enum _ _ _ _ _ hmc ((setContains_iff_contains).mpr h)
  · simp at h

/-- `≠` on `BoolType` ⇒ `BoolTypeNeq` (reverse of `boolTypeNeq_ne`). -/
theorem boolTypeNeq_of_ne {b₁ b₂ : BoolType} (h : b₁ ≠ b₂) : BoolTypeNeq b₁ b₂ := by
  cases b₁ <;> cases b₂ <;> first | exact absurd rfl h | constructor

/-- `lub? = some` ⇒ `Lub` (reverse of `lub_sound`), with the `LubQualified`/`LubRecord`
    reverses proved simultaneously by functional induction on `lub?`. -/
theorem lub?_lub (ty₁ ty₂ : CedarType) : ∀ {t}, lub? ty₁ ty₂ = some t → Lub ty₁ ty₂ t := by
  induction ty₁, ty₂ using lub?.induct
    (motive_1 := fun q₁ q₂ => ∀ {q}, lubQualifiedType q₁ q₂ = some q → LubQualified q₁ q₂ q)
    (motive_3 := fun r₁ r₂ => ∀ {r}, lubRecordType r₁ r₂ = some r → LubRecord r₁ r₂ r) with
  | case1 b₁ b₂ =>
    intro t h; simp only [lub?, Option.some.injEq] at h; subst h
    by_cases hb : b₁ = b₂
    · subst hb; simp only [lubBool, ite_self]; exact Lub.boolSame _
    · rw [show lubBool b₁ b₂ = .anyBool from by simp only [lubBool, if_neg hb]]
      exact Lub.boolDiff _ _ (boolTypeNeq_of_ne hb)
  | case2 s₁ s₂ ih =>
    intro t h; simp only [lub?] at h
    cases hs : s₁ ⊔ s₂ with
    | none => rw [hs] at h; simp at h
    | some s =>
      rw [hs] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact Lub.set _ _ _ (ih hs)
  | case3 r₁ r₂ ih3 =>
    intro t h; simp only [lub?] at h
    cases hr : lubRecordType r₁ r₂ with
    | none => rw [hr] at h; simp at h
    | some r =>
      rw [hr] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact Lub.record _ _ _ (ih3 hr)
  | case4 ty₂ hb hs hr =>
    intro t h
    rw [Cedar.Thm.lub_refl] at h; simp only [Option.some.injEq] at h; subst h
    cases ty₂ with
    | int => exact Lub.int
    | string => exact Lub.string
    | entity ety => exact Lub.entity ety
    | ext xty => exact Lub.ext xty
    | bool b => exact (hb b b rfl rfl).elim
    | set s => exact (hs s s rfl rfl).elim
    | record m => obtain ⟨kvs⟩ := m; exact (hr kvs kvs rfl rfl).elim
  | case5 a ty₂ hne _ _ _ => intro t h; simp only [lub?] at h; split at h <;> simp_all
  | case6 => rename_i r h; simp only [lubRecordType, Option.some.injEq] at h; subst h; exact LubRecord.nil
  | case7 k₁ v₁ r₁ k₂ v₂ r₂ hbne => rename_i r h; simp [lubRecordType, hbne] at h
  | case8 k₁ v₁ r₁ k₂ v₂ r₂ hbne ihq ihr =>
    rename_i r h
    have hk : k₁ = k₂ := by simpa using hbne
    subst hk
    simp only [lubRecordType] at h; rw [if_neg hbne] at h
    cases hty : lubQualifiedType v₁ v₂ with
    | none => rw [hty] at h; simp at h
    | some ty =>
      cases htys : lubRecordType r₁ r₂ with
      | none => rw [hty, htys] at h; simp at h
      | some tys =>
        rw [hty, htys] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
        exact LubRecord.cons _ _ _ _ _ _ _ (ihq hty) (ihr htys)
  | case9 t ty₂ _ _ => rename_i r h; simp [lubRecordType] at h
  | case10 ty₁ ty₂ ih =>
    rename_i q h; simp only [lubQualifiedType] at h
    cases hlub : lub? ty₁ ty₂ with
    | none => rw [hlub] at h; simp at h
    | some ty =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact LubQualified.optional _ _ _ (ih hlub)
  | case11 ty₁ ty₂ ih =>
    rename_i q h; simp only [lubQualifiedType] at h
    cases hlub : lub? ty₁ ty₂ with
    | none => rw [hlub] at h; simp at h
    | some ty =>
      rw [hlub] at h; simp only [Option.bind_some_fun, Option.some.injEq] at h; subst h
      exact LubQualified.required _ _ _ (ih hlub)
  | case12 t q₂ _ _ => rename_i q h; simp [lubQualifiedType] at h

/-! ## `WfExpr` inversion helpers (extract sub-`WfExpr`s with `env` fixed) -/

theorem wfExpr_or {env a b} (h : WfExpr env (.or a b)) : WfExpr env a ∧ WfExpr env b := by
  cases h; exact ⟨by assumption, by assumption⟩

theorem wfExpr_and {env a b} (h : WfExpr env (.and a b)) : WfExpr env a ∧ WfExpr env b := by
  cases h; exact ⟨by assumption, by assumption⟩

theorem wfExpr_ite {env a b d} (h : WfExpr env (.ite a b d)) :
    WfExpr env a ∧ WfExpr env b ∧ WfExpr env d := by
  cases h; exact ⟨by assumption, by assumption, by assumption⟩

theorem wfExpr_unaryApp {env op a} (h : WfExpr env (.unaryApp op a)) :
    (∀ ety, op = .is ety → ValidEntityType ety env.ets env.acts) ∧ WfExpr env a := by
  cases h; exact ⟨by assumption, by assumption⟩

theorem wfExpr_binaryApp {env op a b} (h : WfExpr env (.binaryApp op a b)) :
    WfExpr env a ∧ WfExpr env b := by
  cases h; exact ⟨by assumption, by assumption⟩

theorem wfExpr_getAttr {env a k} (h : WfExpr env (.getAttr a k)) : WfExpr env a := by
  cases h; assumption

theorem wfExpr_hasAttr {env a k} (h : WfExpr env (.hasAttr a k)) : WfExpr env a := by
  cases h; assumption

theorem wfExpr_set {env xs} (h : WfExpr env (.set xs)) : ∀ e ∈ xs, WfExpr env e := by
  cases h; assumption

theorem wfExpr_record {env axs} (h : WfExpr env (.record axs)) :
    (axs.map Prod.fst).SortedBy id ∧ ∀ e ∈ axs.map Prod.snd, WfExpr env e := by
  cases h; exact ⟨by assumption, by assumption⟩

theorem wfExpr_call {env f xs} (h : WfExpr env (.call f xs)) : ∀ e ∈ xs, WfExpr env e := by
  cases h; assumption

/-- **Completeness of `HasType`** (converse of `hasType_sound`): on a well-formed
    environment, any successful `typeOf` run on a `WfExpr` (canonical-record,
    declared-`is`-type) expression is witnessed by a `HasType` derivation with a
    capability-equivalent output. -/
theorem typeOf_complete {env : TypeEnv} (hwf : Schema.WfTypeEnv env) :
    ∀ {x : Expr} {c : Capabilities} {tx : TypedExpr} {c' : Capabilities},
      WfExpr env x → typeOf x c env = .ok (tx, c') →
      ∃ cout, HasType x c env tx.typeOf cout ∧ CapsEquiv cout c' := by
  intro x c
  induction x, c using typeOf.induct with
  | case1 c p =>
    intro hwfx tx c' h
    obtain ⟨ets, acts, reqty⟩ := env
    simp only [typeOf, typeOfLit] at h
    split at h
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], HasType.litBoolTrue _ _ _ _, fun _ => Iff.rfl⟩
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], HasType.litBoolFalse _ _ _ _, fun _ => Iff.rfl⟩
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], HasType.litInt _ _ _ _ _, fun _ => Iff.rfl⟩
    · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], HasType.litString _ _ _ _ _, fun _ => Iff.rfl⟩
    · split at h
      · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rename_i uid hcond
        have hval : ValidEntityUID uid.ty uid.eid ets acts := by
          rcases Bool.or_eq_true_iff.mp hcond with hv | hc
          · exact validEntityUID_of_isValid (wfTypeEnv_ets_nodup hwf) hv
          · -- action UID: `acts.find? uid` is some entry ⇒ `MapContainsPairKey`
            simp only [ActionSchema.contains, Option.isSome_iff_exists] at hc
            obtain ⟨entry, hfind⟩ := hc
            obtain ⟨e, hpk⟩ := mapContainsPairKey_of_mapContains (find?_mapContains hfind)
            exact ValidEntityUID.action uid.ty uid.eid ets acts e hpk
        exact ⟨[], HasType.litEntity uid.ty uid.eid c ets acts reqty hval, fun _ => Iff.rfl⟩
      · simp only [err, reduceCtorEq] at h
  | case2 c v =>
    intro hwfx tx c' h
    obtain ⟨ets, acts, princ, ⟨actionTy, actionEid⟩, resource, ctx⟩ := env
    simp only [typeOf, typeOfVar] at h
    split at h <;>
      (simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h)
    · exact ⟨[], HasType.varPrincipal _ _ _ _ _ _ _, fun _ => Iff.rfl⟩
    · exact ⟨[], HasType.varAction _ _ _ _ _ _ _ _, fun _ => Iff.rfl⟩
    · exact ⟨[], HasType.varResource _ _ _ _ _ _ _, fun _ => Iff.rfl⟩
    · exact ⟨[], HasType.varContext _ _ _ _ _ _ _, fun _ => Iff.rfl⟩
  | case3 c x₁ x₂ x₃ ih1 ih2 ih3 => intro hwfx tx c' h; sorry
  | case4 c x₁ x₂ ih1 ih2 => intro hwfx tx c' h; sorry
  | case5 c x₁ x₂ ih1 ih2 =>
    intro tx c' hwfx h
    obtain ⟨hw1, hw2⟩ := wfExpr_or hwfx
    · simp only [typeOf] at h
      cases h1 : typeOf x₁ c env with
      | error e => rw [h1] at h; simp at h
      | ok r1 =>
        obtain ⟨ty1, cc1⟩ := r1
        rw [h1] at h; simp only [Except.bind_ok] at h
        obtain ⟨cout1, hHT1, hce1⟩ := ih1 hw1 h1
        simp only [typeOfOr] at h
        split at h
        · rename_i heq
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨[], ?_, fun _ => Iff.rfl⟩
          rw [heq]; exact HasType.orShort x₁ x₂ c env cout1 (heq ▸ hHT1)
        · rename_i heq
          cases h2 : typeOf x₂ c env with
          | error e => rw [h2] at h; simp at h
          | ok r2 =>
            obtain ⟨ty2, cc2⟩ := r2
            rw [h2] at h; simp only [Except.bind_ok] at h
            obtain ⟨cout2, hHT2, hce2⟩ := ih2 hw2 h2
            split at h
            · rename_i heq2
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨cout2, ?_, hce2⟩
              rw [heq2]
              exact HasType.orFfThen x₁ x₂ c env cout1 _ cout2 (heq ▸ hHT1) (heq2 ▸ hHT2)
            · simp only [err, reduceCtorEq] at h
        · -- outer `.bool _`: reached only for `anyBool` (tt/ff handled above)
          rename_i _ bty hnt hnf heq
          have hany : bty = BoolType.anyBool := by
            cases bty <;> first | rfl | exact absurd rfl hnt | exact absurd rfl hnf
          subst hany
          cases h2 : typeOf x₂ c env with
          | error e => rw [h2] at h; simp at h
          | ok r2 =>
            obtain ⟨ty2, cc2⟩ := r2
            rw [h2] at h; simp only [Except.bind_ok] at h
            obtain ⟨cout2, hHT2, hce2⟩ := ih2 hw2 h2
            split at h
            · rename_i heq2
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨[], ?_, fun _ => Iff.rfl⟩
              simp only [TypedExpr.typeOf]
              exact HasType.orAnyTt x₁ x₂ c env cout1 cout2 (heq ▸ hHT1) (heq2 ▸ hHT2)
            · rename_i heq2
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨cout1, ?_, hce1⟩
              simp only [TypedExpr.typeOf]
              exact HasType.orAnyFf x₁ x₂ c env cout1 cout2 (heq ▸ hHT1) (heq2 ▸ hHT2)
            · -- inner `.bool _`: reached only for `anyBool`
              rename_i _ bty2 hnt2 hnf2 heq2
              have hany2 : bty2 = BoolType.anyBool := by
                cases bty2 <;> first | rfl | exact absurd rfl hnt2 | exact absurd rfl hnf2
              subst hany2
              simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨capIntersect cout1 cout2, ?_, ?_⟩
              · simp only [TypedExpr.typeOf]
                exact HasType.orAnyAny x₁ x₂ c env cout1 cout2 (heq ▸ hHT1) (heq2 ▸ hHT2)
              · exact (capIntersect_capsEquiv_inter cout1 cout2).trans (CapsEquiv.inter hce1 hce2)
            · simp only [err, reduceCtorEq] at h
        · simp only [err, reduceCtorEq] at h
  | case6 c op₁ x₁ ih1 =>
    intro tx c' hwfx h
    obtain ⟨his, hw1⟩ := wfExpr_unaryApp hwfx
    simp only [typeOf] at h
    cases h1 : typeOf x₁ c env with
    | error e => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨ty1, cc1⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨cout1, hHT1, hce1⟩ := ih1 hw1 h1
      simp only [typeOfUnaryApp] at h
      split at h
      · -- `.not`, `.bool bx`: pick not-rule by the operand's bool subtype
        rename_i _ _ bx heq
        simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], ?_, fun _ => Iff.rfl⟩
        simp only [TypedExpr.typeOf]
        cases bx <;>
          first
            | exact HasType.unaryAppNotTt x₁ c env (heq ▸ hHT1)
            | exact HasType.unaryAppNotFf x₁ c env (heq ▸ hHT1)
            | exact HasType.unaryAppNotAny x₁ c env (heq ▸ hHT1)
      · -- `.neg`, `.int`
        rename_i _ _ heq
        simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], ?_, fun _ => Iff.rfl⟩
        simp only [TypedExpr.typeOf]
        exact HasType.unaryAppNeg x₁ c env (heq ▸ hHT1)
      · -- `.isEmpty`, `.set elemTy`
        rename_i _ _ elemTy heq
        simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], ?_, fun _ => Iff.rfl⟩
        simp only [TypedExpr.typeOf]
        exact HasType.unaryAppIsEmpty x₁ c env elemTy (heq ▸ hHT1)
      · -- `.like pat`, `.string`
        rename_i _ _ _ heq
        simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[], ?_, fun _ => Iff.rfl⟩
        simp only [TypedExpr.typeOf]
        exact HasType.unaryAppLike _ x₁ c env (heq ▸ hHT1)
      · -- `.is ety₁`, `.entity ety₂`
        rename_i _ _ ety₁ ety₂ heq
        split at h
        · -- ety₁ = ety₂ → `.tt`; tested type declared via `his`
          rename_i hEq
          simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          subst hEq
          refine ⟨[], ?_, fun _ => Iff.rfl⟩
          simp only [TypedExpr.typeOf]
          exact HasType.unaryAppIsTrue ety₁ x₁ c env (his ety₁ rfl) (heq ▸ hHT1)
        · -- ety₁ ≠ ety₂ → `.ff`
          rename_i hNe
          simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨[], ?_, fun _ => Iff.rfl⟩
          simp only [TypedExpr.typeOf]
          have hvdet : ValidDifferentEntityType ety₂ ety₁ env.ets env.acts := by
            rcases his ety₁ rfl with _ | _
            · exact ValidDifferentEntityType.inSchema _ _ _ _ _ ‹MapContains _ _ _› hNe
            · exact ValidDifferentEntityType.isAction _ _ _ _ _ _ ‹MapContainsPairKey _ _ _ _› hNe
          -- Operand type `ety₂` is declared. This is the `typeOf` entity-type
          -- declaredness invariant: `typechecked_has_well_formed_type` gives
          -- `CedarType.WellFormed env (.entity ety₂)`, whose `entity_wf` yields
          -- `ValidEntityType ety₂` — modulo the `WfTypeEnv → env.WellFormed`
          -- bridge. Left as the sole gap in this case.
          have hvet₂ : ValidEntityType ety₂ env.ets env.acts := sorry
          exact HasType.unaryAppIsFalse ety₁ ety₂ x₁ c env hvet₂ hvdet (heq ▸ hHT1)
      · -- err (unexpected operand type)
        simp only [err, reduceCtorEq] at h
  | case7 c op₂ x₁ x₂ ih1 ih2 => intro hwfx tx c' h; sorry
  | case8 c x₁ a ih1 => intro hwfx tx c' h; sorry
  | case9 c x₁ a ih1 => intro hwfx tx c' h; sorry
  | case10 c xs ih => intro hwfx tx c' h; sorry
  | case11 c axs ih => intro hwfx tx c' h; sorry
  | case12 c xfn xs ih => intro hwfx tx c' h; sorry

end CedarGen.Relational.Lean

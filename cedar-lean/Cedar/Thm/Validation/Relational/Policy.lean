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

import Cedar.Validation.Relational.Policy
import Cedar.Thm.Validation.Relational.WellFormed
import Cedar.Thm.Validation.SubstituteAction
import Cedar.Thm.Data.List

/-! # `ValidPolicy` characterizes `validate`

Each relation in `Cedar.Validation.Relational.Policy` agrees with the validator function it
mirrors, and together they give `validate_iff`. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Policy expressions -/

theorem scopeExpr_toExpr (s : Scope) (v : Var) : ScopeExpr s v (s.toExpr v) := by
  cases s <;> simp only [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType] <;>
    constructor

theorem ScopeExpr.eq_toExpr {s v x} (h : ScopeExpr s v x) : x = s.toExpr v := by
  cases h <;> simp only [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType]

theorem entityUIDLits_map (uids : List EntityUID) :
    EntityUIDLits uids (uids.map fun e => .lit (.entityUID e)) := by
  induction uids with
  | nil => exact .nil
  | cons u us ih => exact .cons _ _ _ ih

theorem EntityUIDLits.eq_map {uids xs} (h : EntityUIDLits uids xs) :
    xs = uids.map fun e => .lit (.entityUID e) := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simp [ih]

theorem actionScopeExpr_toExpr (s : ActionScope) : ActionScopeExpr s s.toExpr := by
  cases s with
  | actionScope s => exact .scope _ _ (scopeExpr_toExpr s .action)
  | actionInAny uids => simp only [ActionScope.toExpr]; exact .inAny _ _ (entityUIDLits_map uids)

theorem ActionScopeExpr.eq_toExpr {s x} (h : ActionScopeExpr s x) : x = s.toExpr := by
  cases h with
  | scope s x hs => simp only [ActionScope.toExpr]; exact hs.eq_toExpr
  | inAny uids xs hl => simp only [ActionScope.toExpr, hl.eq_map]

theorem conditionExpr_toExpr (c : Condition) : ConditionExpr c c.toExpr := by
  obtain ⟨k, b⟩ := c
  cases k <;> simp only [Condition.toExpr] <;> constructor

theorem ConditionExpr.eq_toExpr {c x} (h : ConditionExpr c x) : x = c.toExpr := by
  cases h <;> simp only [Condition.toExpr]

theorem conditions_toExpr_cons_cons (c c' : Condition) (cs : Conditions) :
    Conditions.toExpr (c :: c' :: cs) = .and c.toExpr (Conditions.toExpr (c' :: cs)) := by
  unfold Conditions.toExpr
  rw [List.reverse_cons (a := c)]
  cases h : (c' :: cs).reverse with
  | nil => simp at h
  | cons d ds => simp [List.foldl_append]

theorem conditionsExpr_toExpr : ∀ cs : Conditions, ConditionsExpr cs (Conditions.toExpr cs)
  | [] => by simp only [Conditions.toExpr, List.reverse_nil]; exact .nil
  | [c] => by
    simp only [Conditions.toExpr, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.foldl_nil]
    exact .one _ _ (conditionExpr_toExpr c)
  | c :: c' :: cs => by
    rw [conditions_toExpr_cons_cons]
    exact .cons _ _ _ _ _ (conditionExpr_toExpr c) (conditionsExpr_toExpr (c' :: cs))

theorem ConditionsExpr.eq_toExpr {cs x} (h : ConditionsExpr cs x) : x = Conditions.toExpr cs := by
  induction h with
  | nil => simp [Conditions.toExpr]
  | one c x hc =>
    simp only [Conditions.toExpr, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.foldl_nil]
    exact hc.eq_toExpr
  | cons c c' cs x rest hc _ ih => rw [conditions_toExpr_cons_cons, hc.eq_toExpr, ih]

theorem policyExpr_toExpr (p : Policy) : PolicyExpr p p.toExpr := by
  obtain ⟨id, eff, ⟨ps⟩, acs, ⟨rs⟩, cs⟩ := p
  exact .mk _ _ _ _ _ _ _ _ _ _ (scopeExpr_toExpr ps .principal) (actionScopeExpr_toExpr acs)
    (scopeExpr_toExpr rs .resource) (conditionsExpr_toExpr cs)

theorem PolicyExpr.eq_toExpr {p x} (h : PolicyExpr p x) : x = p.toExpr := by
  cases h with
  | mk id eff ps acs rs cs xp xa xr xc hp ha hr hc =>
    simp only [Policy.toExpr, PrincipalScope.toExpr, ResourceScope.toExpr, hp.eq_toExpr,
      ha.eq_toExpr, hr.eq_toExpr, hc.eq_toExpr]

/-! ## Action substitution -/

theorem substituteAction_set (uid : EntityUID) (xs : List Expr) :
    substituteAction uid (.set xs) = .set (xs.map (substituteAction uid)) := by
  cases xs with
  | nil => exact Cedar.Thm.substitute_action_nil_set uid
  | cons h t => exact Cedar.Thm.substitute_action_cons_set h t uid

theorem substituteAction_call (uid : EntityUID) (f : ExtFun) (xs : List Expr) :
    substituteAction uid (.call f xs) = .call f (xs.map (substituteAction uid)) := by
  cases xs with
  | nil => exact Cedar.Thm.substitute_action_nil_call uid f
  | cons h t => exact Cedar.Thm.substitute_action_cons_call h t uid f

theorem substituteAction_record (uid : EntityUID) (axs : List (Attr × Expr)) :
    substituteAction uid (.record axs) =
      .record (axs.map fun (a, x) => (a, substituteAction uid x)) := by
  cases axs with
  | nil => exact Cedar.Thm.substitute_action_nil_record uid
  | cons h t => exact Cedar.Thm.substitute_action_cons_record h t uid

mutual
theorem SubstAction.eq_substituteAction {uid x x'} :
    SubstAction uid x x' → x' = substituteAction uid x
  | .lit _ _ | .action _ | .principal _ | .resource _ | .context _ => by
    simp only [substituteAction, mapOnVars]
  | .ite _ _ _ _ _ _ _ ha hb hc => by
    rw [ha.eq_substituteAction, hb.eq_substituteAction, hc.eq_substituteAction]
    simp only [substituteAction, mapOnVars]
  | .and _ _ _ _ _ ha hb | .or _ _ _ _ _ ha hb | .binaryApp _ _ _ _ _ _ ha hb => by
    rw [ha.eq_substituteAction, hb.eq_substituteAction]; simp only [substituteAction, mapOnVars]
  | .unaryApp _ _ _ _ ha | .getAttr _ _ _ _ ha | .hasAttr _ _ _ _ ha
  | .extHasAttr _ _ _ _ _ ha => by
    rw [ha.eq_substituteAction]; simp only [substituteAction, mapOnVars]
  | .set _ _ _ hl => by rw [substituteAction_set, hl.eq_map]
  | .call _ _ _ _ hl => by rw [substituteAction_call, hl.eq_map]
  | .record _ _ _ hr => by rw [substituteAction_record, hr.eq_map]

theorem SubstActionList.eq_map {uid xs xs'} :
    SubstActionList uid xs xs' → xs' = xs.map (substituteAction uid)
  | .nil _ => rfl
  | .cons _ _ _ _ _ hx hxs => by rw [hx.eq_substituteAction, hxs.eq_map, List.map_cons]

theorem SubstActionRecord.eq_map {uid axs axs'} :
    SubstActionRecord uid axs axs' → axs' = axs.map fun (a, x) => (a, substituteAction uid x)
  | .nil _ => rfl
  | .cons _ _ _ _ _ _ hx hxs => by rw [hx.eq_substituteAction, hxs.eq_map, List.map_cons]
end

mutual
theorem substAction_substituteAction (uid : EntityUID) :
    ∀ x : Expr, SubstAction uid x (substituteAction uid x)
  | .lit p => by simp only [substituteAction, mapOnVars]; exact .lit _ _
  | .var .action => by simp only [substituteAction, mapOnVars]; exact .action _
  | .var .principal => by simp only [substituteAction, mapOnVars]; exact .principal _
  | .var .resource => by simp only [substituteAction, mapOnVars]; exact .resource _
  | .var .context => by simp only [substituteAction, mapOnVars]; exact .context _
  | .ite a b c => by
    have h := SubstAction.ite _ _ _ _ _ _ _ (substAction_substituteAction uid a)
      (substAction_substituteAction uid b) (substAction_substituteAction uid c)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .and a b => by
    have h := SubstAction.and _ _ _ _ _ (substAction_substituteAction uid a)
      (substAction_substituteAction uid b)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .or a b => by
    have h := SubstAction.or _ _ _ _ _ (substAction_substituteAction uid a)
      (substAction_substituteAction uid b)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .unaryApp op a => by
    have h := SubstAction.unaryApp _ op _ _ (substAction_substituteAction uid a)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .binaryApp op a b => by
    have h := SubstAction.binaryApp _ op _ _ _ _ (substAction_substituteAction uid a)
      (substAction_substituteAction uid b)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .getAttr a k => by
    have h := SubstAction.getAttr _ _ k _ (substAction_substituteAction uid a)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .hasAttr a k => by
    have h := SubstAction.hasAttr _ _ k _ (substAction_substituteAction uid a)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .extHasAttr a k ks => by
    have h := SubstAction.extHasAttr _ _ k ks _ (substAction_substituteAction uid a)
    simp only [substituteAction, mapOnVars] at h ⊢; exact h
  | .set xs => by rw [substituteAction_set]; exact .set _ _ _ (substActionList_map uid xs)
  | .call f xs => by rw [substituteAction_call]; exact .call _ _ _ _ (substActionList_map uid xs)
  | .record axs => by
    rw [substituteAction_record]; exact .record _ _ _ (substActionRecord_map uid axs)

theorem substActionList_map (uid : EntityUID) :
    ∀ xs : List Expr, SubstActionList uid xs (xs.map (substituteAction uid))
  | [] => .nil _
  | x :: xs => .cons _ _ _ _ _ (substAction_substituteAction uid x) (substActionList_map uid xs)

theorem substActionRecord_map (uid : EntityUID) :
    ∀ axs : List (Attr × Expr),
      SubstActionRecord uid axs (axs.map fun (a, x) => (a, substituteAction uid x))
  | [] => .nil _
  | (_, x) :: axs =>
    .cons _ _ _ _ _ _ (substAction_substituteAction uid x) (substActionRecord_map uid axs)
end

/-! ## Declared entities -/

private theorem bind_unit_ok_iff {ε : Type} {x y : Except ε Unit} :
    (x >>= fun _ => y) = .ok () ↔ x = .ok () ∧ y = .ok () := by
  cases x <;> simp [bind, Except.bind]

theorem checkEntities_list_ok_iff {schema : Schema} {xs : List Expr} :
    xs.attach.forM (fun x => checkEntities schema x.val) = .ok () ↔
      ∀ x ∈ xs, checkEntities schema x = .ok () := by
  constructor
  · intro h x hx
    exact List.forM_ok_implies_all_ok _ _ h ⟨x, hx⟩ (List.mem_attach _ _)
  · intro h
    exact List.all_ok_implies_forM_ok _ _ (fun y _ => h y.val y.property)

theorem checkEntities_record_ok_iff {schema : Schema} {axs : List (Attr × Expr)} :
    axs.attach₂.forM (fun p => checkEntities schema p.val.snd) = .ok () ↔
      ∀ p ∈ axs, checkEntities schema p.snd = .ok () := by
  constructor
  · intro h p hp
    have hmem : (⟨p, List.sizeOf_snd_lt_sizeOf_list hp⟩ :
        { x : Attr × Expr // sizeOf x.snd < 1 + sizeOf axs }) ∈ axs.attach₂ := by
      simp only [List.attach₂, List.mem_pmap]; exact ⟨p, hp, rfl⟩
    exact List.forM_ok_implies_all_ok _ _ h _ hmem
  · intro h
    exact List.all_ok_implies_forM_ok _ _ (fun q hq => h q.val (List.mem_attach₂ hq))

theorem validEntityType_checkEntities {ets : EntitySchema} {acts : ActionSchema} {ety : EntityType}
    (hnd : (ets.toList.map Prod.fst).Nodup) (h : ValidEntityType ety ets acts) :
    (ets.contains ety || acts.actionType? ety) = true := by
  cases h with
  | inSchema => rename_i hmc; simp [EntitySchema.contains, mapContains_find?_nodup hmc hnd]
  | isAction => rename_i hpk; simp [mapContainsPairKey_actionType? hpk]

theorem validEntityType_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    {ety : EntityType} (h : (ets.contains ety || acts.actionType? ety) = true) :
    ValidEntityType ety ets acts := by
  rcases Bool.or_eq_true_iff.mp h with hc | ha
  · simp only [EntitySchema.contains, Option.isSome_iff_exists] at hc
    obtain ⟨entry, hf⟩ := hc
    exact .inSchema _ _ _ _ (find?_mapContains hf)
  · obtain ⟨eid, entry, hpk⟩ := actionType?_mapContainsPairKey ha
    exact .isAction _ _ _ _ _ hpk

theorem validEntityUID_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    {uid : EntityUID} (hnd : (ets.toList.map Prod.fst).Nodup)
    (h : (ets.isValidEntityUID uid || acts.contains uid) = true) :
    ValidEntityUID uid.ty uid.eid ets acts := by
  rcases Bool.or_eq_true_iff.mp h with hv | hc
  · exact validEntityUID_of_isValid hnd hv
  · simp only [ActionSchema.contains, Option.isSome_iff_exists] at hc
    obtain ⟨entry, hfind⟩ := hc
    obtain ⟨e, hpk⟩ := mapContainsPairKey_of_mapContains (find?_mapContains hfind)
    exact ValidEntityUID.action uid.ty uid.eid ets acts e hpk

mutual
theorem EntitiesDeclared.checkEntities_ok {ets : EntitySchema} {acts : ActionSchema} {x : Expr}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    EntitiesDeclared ets acts x → checkEntities ⟨ets, acts⟩ x = .ok ()
  | .litBool _ _ _ | .litInt _ _ _ | .litString _ _ _ | .var _ _ _ => by simp [checkEntities]
  | .litEntity _ _ _ _ hv => by simp [checkEntities, validEntityUID_lit hv hndE hndA]
  | .ite _ _ _ _ _ ha hb hc => by
    simp [checkEntities, ha.checkEntities_ok hndE hndA, hb.checkEntities_ok hndE hndA,
      hc.checkEntities_ok hndE hndA]
  | .and _ _ _ _ ha hb | .or _ _ _ _ ha hb | .binaryApp _ _ _ _ _ ha hb => by
    simp [checkEntities, ha.checkEntities_ok hndE hndA, hb.checkEntities_ok hndE hndA]
  | .is _ _ _ _ hv ha => by
    simp [checkEntities, validEntityType_checkEntities hndE hv, ha.checkEntities_ok hndE hndA]
  | .not _ _ _ ha | .neg _ _ _ ha | .isEmpty _ _ _ ha | .like _ _ _ _ ha | .getAttr _ _ _ _ ha
  | .hasAttr _ _ _ _ ha | .extHasAttr _ _ _ _ _ ha => by
    simp [checkEntities, ha.checkEntities_ok hndE hndA]
  | .set _ _ _ hl | .call _ _ _ _ hl => by
    simp only [checkEntities]; exact checkEntities_list_ok_iff.mpr (hl.checkEntities_ok hndE hndA)
  | .record _ _ _ hr => by
    simp only [checkEntities]
    exact checkEntities_record_ok_iff.mpr (hr.checkEntities_ok hndE hndA)

theorem EntitiesDeclaredList.checkEntities_ok {ets : EntitySchema} {acts : ActionSchema}
    {xs : List Expr}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    EntitiesDeclaredList ets acts xs → ∀ x ∈ xs, checkEntities ⟨ets, acts⟩ x = .ok ()
  | .nil _ _ => by simp
  | .cons _ _ _ _ hx hxs => by
    intro y hy
    rcases List.mem_cons.mp hy with he | hy
    · rw [he]; exact hx.checkEntities_ok hndE hndA
    · exact hxs.checkEntities_ok hndE hndA y hy

theorem EntitiesDeclaredRecord.checkEntities_ok {ets : EntitySchema} {acts : ActionSchema}
    {axs : List (Attr × Expr)}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup) :
    EntitiesDeclaredRecord ets acts axs → ∀ p ∈ axs, checkEntities ⟨ets, acts⟩ p.snd = .ok ()
  | .nil _ _ => by simp
  | .cons _ _ _ _ _ hx hxs => by
    intro q hq
    rcases List.mem_cons.mp hq with he | hq
    · rw [he]; exact hx.checkEntities_ok hndE hndA
    · exact hxs.checkEntities_ok hndE hndA q hq
end

mutual
theorem entitiesDeclared_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    ∀ x : Expr, checkEntities ⟨ets, acts⟩ x = .ok () → EntitiesDeclared ets acts x
  | .lit (.bool _), _ => .litBool _ _ _
  | .lit (.int _), _ => .litInt _ _ _
  | .lit (.string _), _ => .litString _ _ _
  | .lit (.entityUID ⟨ety, eid⟩), h => by
    simp only [checkEntities] at h
    split at h
    · rename_i hcond
      exact .litEntity _ _ _ _ (validEntityUID_of_checkEntities (uid := ⟨ety, eid⟩) hnd hcond)
    · simp at h
  | .var _, _ => .var _ _ _
  | .ite a b c, h => by
    simp only [checkEntities, bind_unit_ok_iff] at h
    exact .ite _ _ _ _ _ (entitiesDeclared_of_checkEntities hnd a h.1)
      (entitiesDeclared_of_checkEntities hnd b h.2.1) (entitiesDeclared_of_checkEntities hnd c h.2.2)
  | .and a b, h => by
    simp only [checkEntities, bind_unit_ok_iff] at h
    exact .and _ _ _ _ (entitiesDeclared_of_checkEntities hnd a h.1)
      (entitiesDeclared_of_checkEntities hnd b h.2)
  | .or a b, h => by
    simp only [checkEntities, bind_unit_ok_iff] at h
    exact .or _ _ _ _ (entitiesDeclared_of_checkEntities hnd a h.1)
      (entitiesDeclared_of_checkEntities hnd b h.2)
  | .binaryApp op a b, h => by
    simp only [checkEntities, bind_unit_ok_iff] at h
    exact .binaryApp _ _ op _ _ (entitiesDeclared_of_checkEntities hnd a h.1)
      (entitiesDeclared_of_checkEntities hnd b h.2)
  | .unaryApp (.is ety) a, h => by
    simp only [checkEntities] at h
    split at h
    · rename_i hcond
      exact .is _ _ _ _ (validEntityType_of_checkEntities hcond)
        (entitiesDeclared_of_checkEntities hnd a h)
    · simp at h
  | .unaryApp .not a, h => by
    simp only [checkEntities] at h; exact .not _ _ _ (entitiesDeclared_of_checkEntities hnd a h)
  | .unaryApp .neg a, h => by
    simp only [checkEntities] at h; exact .neg _ _ _ (entitiesDeclared_of_checkEntities hnd a h)
  | .unaryApp .isEmpty a, h => by
    simp only [checkEntities] at h
    exact .isEmpty _ _ _ (entitiesDeclared_of_checkEntities hnd a h)
  | .unaryApp (.like p) a, h => by
    simp only [checkEntities] at h
    exact .like _ _ p _ (entitiesDeclared_of_checkEntities hnd a h)
  | .getAttr a k, h => by
    simp only [checkEntities] at h
    exact .getAttr _ _ _ k (entitiesDeclared_of_checkEntities hnd a h)
  | .hasAttr a k, h => by
    simp only [checkEntities] at h
    exact .hasAttr _ _ _ k (entitiesDeclared_of_checkEntities hnd a h)
  | .extHasAttr a k ks, h => by
    simp only [checkEntities] at h
    exact .extHasAttr _ _ _ k ks (entitiesDeclared_of_checkEntities hnd a h)
  | .set xs, h => by
    simp only [checkEntities] at h
    exact .set _ _ _ (entitiesDeclaredList_of_checkEntities hnd xs (checkEntities_list_ok_iff.mp h))
  | .call f xs, h => by
    simp only [checkEntities] at h
    exact .call _ _ f _
      (entitiesDeclaredList_of_checkEntities hnd xs (checkEntities_list_ok_iff.mp h))
  | .record axs, h => by
    simp only [checkEntities] at h
    exact .record _ _ _
      (entitiesDeclaredRecord_of_checkEntities hnd axs (checkEntities_record_ok_iff.mp h))

theorem entitiesDeclaredList_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    ∀ xs : List Expr, (∀ x ∈ xs, checkEntities ⟨ets, acts⟩ x = .ok ()) →
      EntitiesDeclaredList ets acts xs
  | [], _ => .nil _ _
  | x :: xs, h => .cons _ _ _ _ (entitiesDeclared_of_checkEntities hnd x (h x (by simp)))
      (entitiesDeclaredList_of_checkEntities hnd xs (fun y hy => h y (by simp [hy])))

theorem entitiesDeclaredRecord_of_checkEntities {ets : EntitySchema} {acts : ActionSchema}
    (hnd : (ets.toList.map Prod.fst).Nodup) :
    ∀ axs : List (Attr × Expr), (∀ p ∈ axs, checkEntities ⟨ets, acts⟩ p.snd = .ok ()) →
      EntitiesDeclaredRecord ets acts axs
  | [], _ => .nil _ _
  | (a, x) :: axs, h =>
    .cons _ _ a _ _ (entitiesDeclared_of_checkEntities hnd x (h (a, x) (by simp)))
      (entitiesDeclaredRecord_of_checkEntities hnd axs (fun q hq => h q (by simp [hq])))
end

/-! ## Typing in each environment -/

mutual
/-- Replacing `action` by a literal keeps an expression well formed. -/
theorem SubstAction.wfExpr {env : TypeEnv} {uid : EntityUID} {x x' : Expr} :
    SubstAction uid x x' → WfExpr env x → WfExpr env x'
  | .lit _ _, _ | .action _, _ => .lit _ _
  | .principal _, _ | .resource _, _ | .context _, _ => .var _ _
  | .ite _ _ _ _ _ _ _ ha hb hc, .ite _ _ _ _ wa wb wc =>
    .ite _ _ _ _ (ha.wfExpr wa) (hb.wfExpr wb) (hc.wfExpr wc)
  | .and _ _ _ _ _ ha hb, .and _ _ _ wa wb => .and _ _ _ (ha.wfExpr wa) (hb.wfExpr wb)
  | .or _ _ _ _ _ ha hb, .or _ _ _ wa wb => .or _ _ _ (ha.wfExpr wa) (hb.wfExpr wb)
  | .unaryApp _ _ _ _ ha, .unaryApp _ _ _ hop wa => .unaryApp _ _ _ hop (ha.wfExpr wa)
  | .binaryApp _ _ _ _ _ _ ha hb, .binaryApp _ _ _ _ wa wb =>
    .binaryApp _ _ _ _ (ha.wfExpr wa) (hb.wfExpr wb)
  | .getAttr _ _ _ _ ha, .getAttr _ _ _ wa => .getAttr _ _ _ (ha.wfExpr wa)
  | .hasAttr _ _ _ _ ha, .hasAttr _ _ _ wa => .hasAttr _ _ _ (ha.wfExpr wa)
  | .extHasAttr _ _ _ _ _ ha, .extHasAttr _ _ _ _ wa => .extHasAttr _ _ _ _ (ha.wfExpr wa)
  | .set _ _ _ hl, .set _ _ wl => .set _ _ (hl.wfExpr wl)
  | .call _ _ _ _ hl, .call _ _ _ wl => .call _ _ _ (hl.wfExpr wl)
  | .record _ _ _ hr, .record _ _ hsort wr => .record _ _ (hr.keys ▸ hsort) (hr.wfExpr wr)

theorem SubstActionList.wfExpr {env : TypeEnv} {uid : EntityUID} {xs xs' : List Expr} :
    SubstActionList uid xs xs' → (∀ e ∈ xs, WfExpr env e) → ∀ e ∈ xs', WfExpr env e
  | .nil _, _ => by simp
  | .cons _ _ _ _ _ hx hxs, w => by
    intro e he
    rcases List.mem_cons.mp he with he | he
    · rw [he]; exact hx.wfExpr (w _ (List.mem_cons_self ..))
    · exact hxs.wfExpr (fun e' h' => w e' (List.mem_cons_of_mem _ h')) e he

theorem SubstActionRecord.wfExpr {env : TypeEnv} {uid : EntityUID} {axs axs' : List (Attr × Expr)} :
    SubstActionRecord uid axs axs' → (∀ e ∈ axs.map Prod.snd, WfExpr env e) →
      ∀ e ∈ axs'.map Prod.snd, WfExpr env e
  | .nil _, _ => by simp
  | .cons _ _ _ _ _ _ hx hxs, w => by
    intro e he
    simp only [List.map_cons, List.mem_cons] at he
    rcases he with he | he
    · rw [he]; exact hx.wfExpr (w _ (by simp))
    · exact hxs.wfExpr (fun e' h' => w e' (by simp only [List.map_cons, List.mem_cons]; exact .inr h'))
        e he

theorem SubstActionRecord.keys {uid : EntityUID} {axs axs' : List (Attr × Expr)} :
    SubstActionRecord uid axs axs' → axs'.map Prod.fst = axs.map Prod.fst
  | .nil _ => rfl
  | .cons _ _ _ _ _ _ _ hxs => by simp only [List.map_cons, hxs.keys]
end

theorem subty_bool_anyBool {ty : CedarType} : (ty ⊑ .bool .anyBool) = true ↔ ∃ b, ty = .bool b := by
  constructor
  · intro h
    cases ty <;> simp_all [subty, lub?]
  · rintro ⟨b, rfl⟩
    cases b <;> simp [subty, lub?, lubBool]

/-- `typecheckPolicy` gives type `.bool b` exactly when `HasType` derives it for the policy
    expression with `action` replaced by the environment's action. -/
theorem typecheckPolicy_ok_iff {p : Policy} {env : TypeEnv} (hwf : EnvAssumptions env)
    (hwfx : WfExpr env (substituteAction env.reqty.action p.toExpr)) {b : BoolType} :
    (∃ tx, typecheckPolicy p env = .ok tx ∧ tx.typeOf = .bool b) ↔
      ∃ cout, HasType (substituteAction env.reqty.action p.toExpr) [] env (.bool b) cout := by
  rw [hasType_iff_typeOf_ok hwf hwfx]
  simp only [typecheckPolicy, List.empty_eq]
  cases hto : typeOf (substituteAction env.reqty.action p.toExpr) [] env with
  | error e => simp
  | ok r =>
    obtain ⟨tx, c'⟩ := r
    simp only
    constructor
    · rintro ⟨tx', h, hty⟩
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact ⟨tx, c', rfl, hty⟩
      · simp at h
    · rintro ⟨tx', c'', h, hty⟩
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, _⟩ := h
      subst h1
      exact ⟨tx, by simp [subty_bool_anyBool.mpr ⟨b, hty⟩], hty⟩

/-- Every environment's typed policy has a Boolean type. -/
theorem mapM_typecheckPolicy_bool {p : Policy} :
    ∀ {envs : List TypeEnv} {txs : List TypedExpr}, envs.mapM (typecheckPolicy p) = .ok txs →
      ∃ bs : List BoolType, txs.map TypedExpr.typeOf = bs.map .bool
  | [], txs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨[], rfl⟩
  | env :: envs, txs, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i tx htc
      split at h
      · simp at h
      · rename_i txs' hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        obtain ⟨bs, hbs⟩ := mapM_typecheckPolicy_bool hrest
        simp only [typecheckPolicy] at htc
        split at htc
        · split at htc
          · rename_i hsub
            simp only [Except.ok.injEq] at htc; subst htc
            obtain ⟨b, hb⟩ := subty_bool_anyBool.mp hsub
            exact ⟨b :: bs, by simp [hb, hbs]⟩
          · simp at htc
        · simp at htc

/-- `TypedInEnvs` is `typecheckPolicy` succeeding in every environment. -/
theorem typedInEnvs_iff {p : Policy} :
    ∀ {envs : List TypeEnv}, (∀ env ∈ envs, EnvAssumptions env) →
      (∀ env ∈ envs, WfExpr env p.toExpr) → ∀ {bs : List BoolType},
        TypedInEnvs envs p.toExpr bs ↔
          ∃ txs, envs.mapM (typecheckPolicy p) = .ok txs ∧ txs.map TypedExpr.typeOf = bs.map .bool
  | [], _, _, bs => by
    constructor
    · intro h; cases h; exact ⟨[], rfl, rfl⟩
    · rintro ⟨txs, h, hbs⟩
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
      cases bs with
      | nil => exact .nil _
      | cons _ _ => simp at hbs
  | env :: envs, hwf, hwfx, bs => by
    obtain ⟨ets, acts, ⟨pr, act, r, ctx⟩⟩ := env
    have hwf₀ := hwf _ (List.mem_cons_self ..)
    have hwfx₀ := (substAction_substituteAction act p.toExpr).wfExpr (hwfx _ (List.mem_cons_self ..))
    have hwf' : ∀ e ∈ envs, EnvAssumptions e := fun e he => hwf e (List.mem_cons_of_mem _ he)
    have hwfx' : ∀ e ∈ envs, WfExpr e p.toExpr := fun e he => hwfx e (List.mem_cons_of_mem _ he)
    constructor
    · intro h
      cases h with
      | cons _ _ _ _ _ _ _ x' b cout _ bs' hs hht hrest =>
        obtain ⟨tx, htc, hty⟩ := (typecheckPolicy_ok_iff (b := b) hwf₀ hwfx₀).mpr
          ⟨cout, hs.eq_substituteAction ▸ hht⟩
        obtain ⟨txs, hm, hbs⟩ := (typedInEnvs_iff (bs := bs') hwf' hwfx').mp hrest
        exact ⟨tx :: txs, by simp [List.mapM_cons, htc, hm, bind, Except.bind, pure, Except.pure],
          by simp [hty, hbs]⟩
    · rintro ⟨txs, hm, hbs⟩
      simp only [List.mapM_cons, bind, Except.bind] at hm
      split at hm
      · simp at hm
      · rename_i tx htc
        split at hm
        · simp at hm
        · rename_i txs' hrest
          simp only [pure, Except.pure, Except.ok.injEq] at hm; subst hm
          cases bs with
          | nil => simp at hbs
          | cons b bs' =>
            simp only [List.map_cons, List.cons.injEq] at hbs
            obtain ⟨hty, hbs'⟩ := hbs
            obtain ⟨cout, hht⟩ := (typecheckPolicy_ok_iff (b := b) hwf₀ hwfx₀).mp
              ⟨tx, htc, hty⟩
            exact .cons _ _ _ _ _ _ _ _ _ _ _ _ (substAction_substituteAction act p.toExpr) hht
              ((typedInEnvs_iff (bs := bs') hwf' hwfx').mpr ⟨txs', hrest, hbs'⟩)

/-! ## Not statically false everywhere -/

theorem notFf_iff {b : BoolType} : NotFf b ↔ b ≠ .ff := by
  constructor
  · intro h; cases h <;> simp
  · intro h
    cases b with
    | tt => exact .tt
    | ff => exact absurd rfl h
    | anyBool => exact .anyBool

theorem allFalse_eq_false_iff :
    ∀ {txs : List TypedExpr} {bs : List BoolType}, txs.map TypedExpr.typeOf = bs.map .bool →
      (allFalse txs = false ↔ SomeNotFf bs)
  | [], [], _ => by simp only [allFalse, List.all_nil, Bool.true_eq_false, false_iff]; intro h; cases h
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | tx :: txs, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hty, hrest⟩ := h
    have ih := allFalse_eq_false_iff hrest
    simp only [allFalse, List.all_cons, Bool.and_eq_false_iff] at ih ⊢
    rw [ih, hty]
    constructor
    · rintro (h | h)
      · exact .here _ _ (notFf_iff.mpr (by intro hb; subst hb; simp at h))
      · exact .there _ _ h
    · intro h
      cases h with
      | here _ _ hnf => exact .inl (by have := notFf_iff.mp hnf; simpa using this)
      | there _ _ h => exact .inr h

/-! ## Validation -/

theorem mem_environments {schema : Schema} {env : TypeEnv} (h : env ∈ schema.environments) :
    env.ets = schema.ets ∧ env.acts = schema.acts := by
  simp only [Schema.environments, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem typedInEnvs_ne_nil {envs : List TypeEnv} {x : Expr} {bs : List BoolType}
    (h : TypedInEnvs envs x bs) (hs : SomeNotFf bs) : ∃ env, env ∈ envs := by
  cases h with
  | nil => cases hs
  | cons ets acts pr act r ctx => exact ⟨_, List.mem_cons_self ..⟩

private theorem forM_singleton {ε α : Type} (f : α → Except ε Unit) (a : α) :
    [a].forM f = f a := by
  cases h : f a with
  | error e => simp [List.forM, h, bind, Except.bind]
  | ok u => cases u; simp [List.forM, h, bind, Except.bind, pure, Except.pure]

theorem typecheckPolicyWithEnvironments_ok_iff {p : Policy} {schema : Schema} :
    typecheckPolicyWithEnvironments typecheckPolicy p schema = .ok () ↔
      checkEntities schema p.toExpr = .ok () ∧
        ∃ txs, schema.environments.mapM (typecheckPolicy p) = .ok txs ∧ allFalse txs = false := by
  simp only [typecheckPolicyWithEnvironments]
  cases hce : checkEntities schema p.toExpr with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok u =>
    cases u
    cases hm : schema.environments.mapM (typecheckPolicy p) with
    | error e => simp [Except.mapError, bind, Except.bind]
    | ok txs => cases haf : allFalse txs <;> simp [haf, Except.mapError, bind, Except.bind]

/-- **Policy validation.** On a schema whose environments satisfy `EnvAssumptions`, `validate`
    accepts a policy exactly when `ValidPolicy` holds for it. -/
theorem validate_singleton_iff {schema : Schema} {p : Policy}
    (hwf : ∀ env ∈ schema.environments, EnvAssumptions env)
    (hwfx : ∀ env ∈ schema.environments, WfExpr env p.toExpr) :
    validate [p] schema = .ok () ↔ ValidPolicy schema.ets schema.acts schema.environments p := by
  rw [validate, forM_singleton, typecheckPolicyWithEnvironments_ok_iff]
  constructor
  · rintro ⟨hce, txs, hm, hnf⟩
    obtain ⟨bs, hbs⟩ := mapM_typecheckPolicy_bool hm
    have hsome := (allFalse_eq_false_iff hbs).mp hnf
    have htyped := (typedInEnvs_iff hwf hwfx).mpr ⟨txs, hm, hbs⟩
    obtain ⟨env, henv⟩ := typedInEnvs_ne_nil htyped hsome
    have hnd := (hwf env henv).ets_keys_nodup
    rw [(mem_environments henv).1] at hnd
    exact .mk _ _ _ _ _ bs (policyExpr_toExpr p)
      (entitiesDeclared_of_checkEntities (acts := schema.acts) hnd _ hce) htyped hsome
  · intro h
    cases h with
    | mk x bs hpe hent htyped hsome =>
      rw [hpe.eq_toExpr] at hent htyped
      obtain ⟨env, henv⟩ := typedInEnvs_ne_nil htyped hsome
      obtain ⟨hets, hacts⟩ := mem_environments henv
      have hndE := (hwf env henv).ets_keys_nodup
      have hndA := (hwf env henv).acts_keys_nodup
      rw [hets] at hndE
      rw [hacts] at hndA
      obtain ⟨txs, hm, hbs⟩ := (typedInEnvs_iff hwf hwfx).mp htyped
      exact ⟨hent.checkEntities_ok hndE hndA, txs, hm, (allFalse_eq_false_iff hbs).mpr hsome⟩

/-- `validate` accepts a set of policies exactly when it accepts each one. -/
theorem validate_iff {schema : Schema} {ps : Policies}
    (hwf : ∀ env ∈ schema.environments, EnvAssumptions env)
    (hwfx : ∀ p ∈ ps, ∀ env ∈ schema.environments, WfExpr env p.toExpr) :
    validate ps schema = .ok () ↔
      ∀ p ∈ ps, ValidPolicy schema.ets schema.acts schema.environments p := by
  have hone : ∀ p ∈ ps, (typecheckPolicyWithEnvironments typecheckPolicy p schema = .ok () ↔
      ValidPolicy schema.ets schema.acts schema.environments p) := by
    intro p hp
    have := validate_singleton_iff (p := p) hwf (hwfx p hp)
    rwa [validate, forM_singleton] at this
  constructor
  · intro h p hp
    exact (hone p hp).mp (List.forM_ok_implies_all_ok _ _ h p hp)
  · intro h
    exact List.all_ok_implies_forM_ok _ _ (fun p hp => (hone p hp).mpr (h p hp))

end Cedar.Validation.Relational

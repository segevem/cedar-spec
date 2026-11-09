import CedarGen.Relational.Depth.Basic
import Specimen.Correctness.WalkSGen
import Specimen.Correctness.SuccObs
import CedarGenProof.ExprGen.Sound

namespace Cedar.Validation.Relational.Depth

open Cedar.Spec Cedar.Validation Cedar.Data Specimen.Correctness

theorem nat_div_eq_div (n k : Nat) : n.div k = n / k := rfl

theorem produces_vectorOf_length {α : Type} {g : SGen α} : ∀ (k : Nat) (xs : List α),
    Produces (_root_.vectorOf k g) xs → xs.length = k := by
  intro k; induction k with
  | zero => intro xs h; simp [_root_.vectorOf] at h; subst h; rfl
  | succ k ih =>
    intro xs h
    rw [_root_.vectorOf_succ] at h
    simp only [produces_bind_iff, produces_pure_iff] at h
    obtain ⟨y, -, ys, hys, rfl⟩ := h
    simp [ih ys hys]

theorem produces_chooseNat_le {lo hi : Nat} {h : lo ≤ hi} {k : Nat}
    (hk : Produces (_root_.chooseNat lo hi h : SGen Nat) k) : k ≤ hi := by
  unfold _root_.chooseNat at hk
  rw [map_eq_bind_pure_comp] at hk
  simp only [produces_bind_iff, produces_pure_iff, Function.comp] at hk
  obtain ⟨a, -, rfl⟩ := hk
  exact a.down.property.2

/-- An unconstrained list is no longer than its size. -/
theorem arb_list_succ {α : Type} [Basalt.ArbitrarySized α] (n : Nat) :
    succObs.spec (Basalt.ArbitrarySized.arbitrarySized n : SGen (List α)) (fun v => v.length ≤ n) := by
  intro xs h
  have h' : Produces ((_root_.chooseNat 0 n (Nat.zero_le n) : SGen Nat) >>= fun k =>
      _root_.vectorOf k (Basalt.ArbitrarySized.arbitrarySized n : SGen α)) xs := h
  simp only [produces_bind_iff] at h'
  obtain ⟨k, hk, hv⟩ := h'
  rw [produces_vectorOf_length k xs hv]; exact produces_chooseNat_le hk

theorem produces_vectorOf_mem {α : Type} {g : SGen α} : ∀ (k : Nat) (xs : List α),
    Produces (_root_.vectorOf k g) xs → ∀ x ∈ xs, Produces g x := by
  intro k; induction k with
  | zero => intro xs h x hx; simp [_root_.vectorOf] at h; subst h; simp at hx
  | succ k ih =>
    intro xs h x hx
    rw [_root_.vectorOf_succ] at h
    simp only [produces_bind_iff, produces_pure_iff] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hy
    · exact ih ys hys x hx

theorem listDepth_le {xs : List Expr} {k : Nat} (h : ∀ x ∈ xs, exprDepth x ≤ k) : listDepth xs ≤ k := by
  induction xs with
  | nil => simp [listDepth]
  | cons x xs ih => simp only [listDepth]; simp at h; exact Nat.max_le.mpr ⟨h.1, ih h.2⟩

theorem recDepth_le {axs : List (Attr × Expr)} {k : Nat} (h : ∀ ax ∈ axs, exprDepth ax.2 ≤ k) :
    recDepth axs ≤ k := by
  induction axs with
  | nil => simp [recDepth]
  | cons ax axs ih =>
    obtain ⟨a, x⟩ := ax; simp only [recDepth]; simp at h; exact Nat.max_le.mpr ⟨h.1, ih (fun ax hx => h.2 ax.1 ax.2 hx)⟩

/-- `anyExprB f b` is at most `b` deep: every constructor spends one of the budget, and an extended
`has` also its attributes. -/
theorem anyExprB_depth : ∀ f b, succObs.spec (anyExprB f b : SGen Expr) (fun x => exprDepth x ≤ b) := by
  intro f
  induction f with
  | zero => intro b; unfold anyExprB; walk; all_goals (simp only [exprDepth]; omega)
  | succ f ih =>
    intro b
    cases b with
    | zero => unfold anyExprB; walk; all_goals (simp only [exprDepth]; omega)
    | succ m =>
      have hv : ∀ k, succObs.spec (_root_.vectorOf k (anyExprB f m) : SGen (List Expr))
          (fun xs => listDepth xs ≤ m) := fun k xs hxs =>
        listDepth_le fun x hx => ih m x (produces_vectorOf_mem k xs hxs x hx)
      have hr : ∀ k, succObs.spec (_root_.vectorOf k (do
          let a ← Basalt.ArbitrarySized.arbitrarySized f
          let x ← anyExprB f m
          pure (a, x)) : SGen (List (Attr × Expr))) (fun axs => recDepth axs ≤ m) := fun k axs haxs =>
        recDepth_le fun ax hx => by
          have h := produces_vectorOf_mem k axs haxs ax hx
          simp only [produces_bind_iff, produces_pure_iff] at h
          obtain ⟨a, -, x, hx', rfl⟩ := h
          exact ih m x hx'
      have hk : ∀ j, succObs.spec (_root_.vectorOf j (Basalt.ArbitrarySized.arbitrarySized f) :
          SGen (List Attr)) (fun ks => ks.length = j) := fun j ks hks =>
        produces_vectorOf_length j ks hks
      unfold anyExprB
      walk [ih, hv, hr, hk]
      all_goals (simp only [exprDepth] at *; omega)

/-- `anyExpr n` is at most `n` deep. -/
theorem anyExpr_depth (n : Nat) : succObs.spec (anyExpr n : SGen Expr) (fun x => exprDepth x ≤ n) := by
  unfold anyExpr; exact anyExprB_depth n n

/-! ## The callees of the expression-producing block

Each fact bounds what one callee produces, mostly from its soundness theorem and a depth fact
about its relation. -/

open Cedar.Validation.Relational.ExprGen.RequestVars

theorem succ_mono {α : Type} {g : SGen α} {P Q : α → Prop} (h : succObs.spec g P)
    (hpq : ∀ v, P v → Q v) : succObs.spec g Q := fun v hv => hpq v (h v hv)

theorem succ_true {α : Type} (g : SGen α) : succObs.spec g (fun _ => True) := fun _ _ => trivial

open Lean Meta Elab Tactic in
/-- Put into context, for every derived generator whose name contains `pat`, the fact that nothing
is known of what it produces (`succObs`). The walk tries a hypothesis only after the facts passed to
it, so these are fallbacks: a callee whose output does not matter to the depth is passed over at
once, instead of the walk unifying it with every fact. `clear_trivial_gen_facts` removes them. -/
elab "add_trivial_succ_facts" pat:str : tactic => withMainContext do
  let sgen := mkConst ``Specimen.Correctness.SGen
  let p := pat.getString
  let env ← getEnv
  let mut goal ← getMainGoal
  for (n, ci) in env.constants.toList do
    unless (n.toString.splitOn p).length > 1 do continue
    unless ci.isDef do continue
    if n.isInternal then continue
    let last := match n with | .str _ l => l | _ => ""
    unless last.startsWith "specimen_gen_" do continue
    let r ← observing? do
      let f ← try mkAppOptM n #[some sgen, none, none, none, none, none, none]
        catch _ => mkConstWithFreshMVarLevels n
      let fty ← inferType f
      forallTelescopeReducing fty fun xs body => do
        unless body.isAppOf ``Specimen.Correctness.SGen do failure
        let pf ← mkAppM ``succ_true #[mkAppN f xs]
        let pf ← mkLambdaFVars xs pf
        return (pf, ← inferType pf)
    let some (pf, pty) := r | continue
    let (_, g) ← (← goal.assert (← mkFreshUserName `htriv) pty pf).intro1P
    goal := g
  replaceMainGoal [goal]

/-- A skipped operand is a leaf, or `anyExpr` at the leaf size. -/
theorem deadOperand_depth {decl syn : Bool} {env : TypeEnv} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun x => DeadOperand decl syn env x) (G := SGen) s l)
      (fun x => exprDepth x ≤ l) := by
  simp only [BacktrackGenFor.gen]
  walk [anyExpr_depth]
  · split_ifs <;> simp [exprDepth]
  · assumption

theorem CapTagMem.depth_le {x e c} (h : CapTagMem x e c) :
    exprDepth x ≤ capsDepth c ∧ exprDepth e ≤ capsDepth c := by
  induction h with
  | here => simp only [capsDepth, keyDepth]; omega
  | there _ _ _ _ ih => simp only [capsDepth]; omega

theorem ctm01_depth (fuel iS sz : Nat) (c : Capabilities) :
    succObs.spec (specimen_gen_Cedar_Validation_Relational_CapTagMem_0_1__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars fuel iS sz c)
      (fun v => exprDepth v.1 ≤ capsDepth c ∧ exprDepth v.2 ≤ capsDepth c) :=
  succ_mono (specimen_gen_Cedar_Validation_Relational_CapTagMem_0_1__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.sound fuel iS sz c)
    fun _ h => CapTagMem.depth_le h

theorem cm2_depth (fuel iS sz : Nat) (a b : Capabilities) :
    succObs.spec (specimen_gen_Cedar_Validation_Relational_CapMerge_2__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars fuel iS sz a b)
      (fun v => capsDepth v ≤ max (capsDepth a) (capsDepth b)) :=
  succ_mono (specimen_gen_Cedar_Validation_Relational_CapMerge_2__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.sound fuel iS sz a b)
    fun _ h => CapMerge.capsDepth_le h

theorem chain7_depth (fuel iS sz : Nat) (env ty x a as c b) :
    succObs.spec (specimen_gen_Cedar_Validation_Relational_ExtHasAttrChain_7__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars fuel iS sz env ty x a as c b)
      (fun v => capsDepth v ≤ exprDepth x + as.length) :=
  succ_mono (specimen_gen_Cedar_Validation_Relational_ExtHasAttrChain_7__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.sound fuel iS sz env ty x a as c b)
    fun _ h => ExtHasAttrChain.capsDepth_le h

theorem chain67_depth (fuel iS sz : Nat) (env ty x a as c) :
    succObs.spec (specimen_gen_Cedar_Validation_Relational_ExtHasAttrChain_6_7__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars fuel iS sz env ty x a as c)
      (fun v => capsDepth v.2 ≤ exprDepth x + as.length) :=
  succ_mono (specimen_gen_Cedar_Validation_Relational_ExtHasAttrChain_6_7__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.sound fuel iS sz env ty x a as c)
    fun _ h => ExtHasAttrChain.capsDepth_le h

theorem hair26_depth (fuel iS sz : Nat) (rty x c k ty) :
    succObs.spec (specimen_gen_Cedar_Validation_Relational_HasAttrInRecord_2_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars fuel iS sz rty x c k ty)
      (fun v => capsDepth v.2 ≤ exprDepth x) :=
  succ_mono (specimen_gen_Cedar_Validation_Relational_HasAttrInRecord_2_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.sound fuel iS sz rty x c k ty)
    fun _ h => HasAttrInRecord.capsDepth_le h

theorem hair256_depth (fuel iS sz : Nat) (rty x c k) :
    succObs.spec (specimen_gen_Cedar_Validation_Relational_HasAttrInRecord_2_5_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars fuel iS sz rty x c k)
      (fun v => capsDepth v.2.2 ≤ exprDepth x) :=
  succ_mono (specimen_gen_Cedar_Validation_Relational_HasAttrInRecord_2_5_6__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.sound fuel iS sz rty x c k)
    fun _ h => HasAttrInRecord.capsDepth_le h

/-- The attributes of an extended `has` are at most the leaf size. -/
theorem extHasIf_depth (fuel iS sz : Nat) (b : Bool) :
    succObs.spec (specimen_gen_Cedar_Validation_Relational_ExtHasIf_1_2__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars fuel iS sz b)
      (fun v => v.2.length ≤ iS) := by
  cases fuel with
  | zero =>
    unfold specimen_gen_Cedar_Validation_Relational_ExtHasIf_1_2__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars
    walk
  | succ f =>
    rw [specimen_gen_Cedar_Validation_Relational_ExtHasIf_1_2__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.eq_body]
    delta specimen_gen_Cedar_Validation_Relational_ExtHasIf_1_2__CedarGen_Relational_ExprGen_Cedar_Validation_Relational_ExprGen_RequestVars.body
    walk [@arb_list_succ]
    all_goals assumption

theorem capIntersect_depth (a b : Capabilities) (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun e => e = capIntersect a b) (G := SGen) s l)
      (fun e => capsDepth e ≤ capsDepth a) :=
  succ_mono (succ_gen_eqRight _ s l) fun _ h => h ▸ capsDepth_capIntersect a b

theorem isActionLitMemSet_depth {acts : ActionSchema} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) (G := SGen) s l)
      (fun p => exprDepth p.1 = 0 ∧ exprDepth p.2 ≤ 1) :=
  succ_mono (isActionLitMemSet_gen s l) fun p h => by
    obtain ⟨x₁, x₂⟩ := p
    cases h with
    | mk uid₁ xs acts entry _ hxs =>
      refine ⟨rfl, ?_⟩
      simp only [exprDepth]
      have : listDepth xs ≤ 0 := listDepth_le fun x hx => by
        obtain ⟨uid, rfl⟩ := hxs x hx; simp [exprDepth]
      omega

theorem InsertSortedField.recDepth_eq {ax axs axs'} (h : InsertSortedField ax axs axs') :
    recDepth axs' = max (exprDepth ax.2) (recDepth axs) := by
  induction h with
  | nil => simp [recDepth]
  | here => simp only [recDepth]
  | there _ _ _ _ _ _ _ ih => simp only [recDepth] at *; omega

theorem SortsTo.recDepth_eq {axs axs'} (h : SortsTo axs axs') : recDepth axs = recDepth axs' := by
  induction h with
  | nil => rfl
  | cons ax _ _ _ _ hi ih =>
    obtain ⟨a, x⟩ := ax
    simp only [recDepth, InsertSortedField.recDepth_eq hi, ih]

theorem sortsTo_depth {axs' : List (Attr × Expr)} (s l : Nat) :
    succObs.spec (BacktrackGenFor.gen (P := fun axs => SortsTo axs axs') (G := SGen) s l)
      (fun axs => recDepth axs = recDepth axs') :=
  succ_mono (sortsTo_gen s l) fun _ h => SortsTo.recDepth_eq h

end Cedar.Validation.Relational.Depth

import Specimen
import Plausible

open Specimen.Tactic
open Plausible

/-! # Specimen demo — a buggy STLC big-step evaluator

A tiny simply-typed lambda calculus (de Bruijn). `Typing Γ e τ` is the typing
relation; Specimen derives a generator for **well-typed** terms from it. We then
run them through a big-step evaluator that has a deliberate bug, and let the
`specimen` tactic find a well-typed term the evaluator mishandles.
-/

inductive Ty where
  | nat
  | fn : Ty → Ty → Ty
deriving DecidableEq, Enum

inductive Tm where
  | const : Nat → Tm
  | add   : Tm → Tm → Tm
  | var   : Nat → Tm
  | lam   : Ty → Tm → Tm
  | app   : Tm → Tm → Tm
deriving DecidableEq

/-- Pretty-print types & terms so counterexamples read like λ-calculus
    (`(λ:Nat. #0) 0`) instead of raw constructors. -/
partial def ppTy : Ty → String
  | .nat    => "Nat"
  | .fn a b => s!"({ppTy a} → {ppTy b})"

partial def ppTm : Tm → String
  | .const n => toString n
  | .add a b => s!"({ppTm a} + {ppTm b})"
  | .var x   => s!"#{x}"
  | .lam τ e => s!"(λ:{ppTy τ}. {ppTm e})"
  | .app f a => s!"({ppTm f} {ppTm a})"

instance : Repr Ty := ⟨fun t _ => f!"{ppTy t}"⟩
instance : Repr Tm := ⟨fun t _ => f!"{ppTm t}"⟩

deriving instance Plausible.Shrinkable for Ty
deriving instance Plausible.Shrinkable for Tm

/-- Budget-based `Arbitrary Ty`: `size` is a total *node budget*, split at a
    random point across a `fn`'s two children — not a depth bound that recurses
    at full size. So `size` caps the number of nodes, and the split (chosen
    uniformly in `[0, remaining]`) decides how the budget is shared. -/
partial def genTy : Nat → Gen Ty
  | 0     => pure .nat
  | n + 1 =>
    Gen.oneOfWithDefault (pure .nat)
      [ pure .nat,
        (do
          let ⟨k, _⟩ ← Gen.choose Nat 0 n (by omega)   -- random split of the remaining budget
          return .fn (← genTy k) (← genTy (n - k))) ]

instance : Plausible.Arbitrary Ty where
  arbitrary := Gen.sized genTy

/-- de Bruijn context lookup. -/
inductive Lookup : List Ty → Nat → Ty → Prop where
  | now   : Lookup (τ :: Γ) 0 τ
  | later : Lookup Γ n τ → Lookup (τ' :: Γ) (n + 1) τ

/-- `Typing Γ e τ`  —  `Γ ⊢ e : τ`. -/
inductive Typing : List Ty → Tm → Ty → Prop where
  | const : Typing Γ (.const n) .nat
  | add   : Typing Γ a .nat → Typing Γ b .nat → Typing Γ (.add a b) .nat
  | var   : Lookup Γ x τ → Typing Γ (.var x) τ
  | lam   : Typing (τ₁ :: Γ) e τ₂ → Typing Γ (.lam τ₁ e) (.fn τ₁ τ₂)
  | app   : Typing Γ f (.fn τ₁ τ₂) → Typing Γ a τ₁ → Typing Γ (.app f a) τ₂

/-- Runtime values: numerals and closures (captured env + param type + body). -/
inductive Val where
  | vnat  : Nat → Val
  | vclos : List Val → Ty → Tm → Val

/-- Big-step evaluator with a **bug** in `app`: it evaluates the argument but
    forgets to *bind* it before running the body (should be `v :: cenv`). -/
partial def eval (env : List Val) : Tm → Option Val
  | .const n => some (.vnat n)
  | .add a b => do
      let (.vnat na) ← eval env a | none
      let (.vnat nb) ← eval env b | none
      some (.vnat (na + nb))
  | .var x   => env[x]?
  | .lam τ e => some (.vclos env τ e)
  | .app f a => do
      let (.vclos cenv _ body) ← eval env f | none
      let _v ← eval env a
      eval cenv body          -- BUG: dropped the argument; should be `eval (_v :: cenv) body`

/-- A closed, `Nat`-typed term should evaluate to a numeral. -/
def evalsToNat (e : Tm) : Bool :=
  match eval [] e with
  | some (.vnat _) => true
  | _              => false

/- Property: every closed well-typed term of type `Nat` evaluates to a numeral.
    True for a correct evaluator — but the buggy `app` (which never binds the
    argument) leaves an application stuck, so `specimen` finds a counterexample. -/
set_option specimen.autoDeriveDeps true in
example : ∀ e : Tm, Typing [] e .nat → evalsToNat e = true := by
  specimen (min := 20)
  sorry

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.autoDeriveDeps true in
example : ∀ e : Tm, Typing [] e .nat → evalsToNat e = true := by
  specimen (min := 20)
  sorry

set_option specimen.scoreType "Scoring.DensityScore" in
set_option specimen.autoDeriveDeps true in
example : ∀ e : Tm, Typing [] e .nat → evalsToNat e = true := by
  specimen (min := 10)
  sorry

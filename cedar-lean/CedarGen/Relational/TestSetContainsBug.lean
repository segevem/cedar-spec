import Specimen

open Plausible

set_option linter.unusedVariables false
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.textOutput 3

/-! ## Bug: derive_mutual fails to resolve DecOpt for polymorphic inductives used via negation

When an inductive has a type parameter (implicit or explicit), `derive_mutual` derives
a checker for it, but the generated code for a negation `¬ P` can't find the `DecOpt`
instance because the type variable isn't being supplied/unified properly.

### Reproduces (polymorphic — FAILS):
-/

inductive MyContains {α : Type} : α → List α → Prop where
  | here : ∀ x rest, MyContains x (x :: rest)
  | there : ∀ x y rest, MyContains x rest → MyContains x (y :: rest)

inductive NotIn {α : Type} : α → List α → Prop where
  | mk : ∀ x xs, ¬ MyContains x xs → NotIn x xs

-- deriving instance Enum for Nat
-- deriving instance DecidableEq for Nat

-- FAILS: "failed to synthesize instance DecOpt (MyContains b_1 c_1)"
-- The derived checker exists but the negation can't find it.
derive_mutual
  checker (fun α x xs => @MyContains α x xs),
  generator (fun α xs => ∃ x, @NotIn α x xs)

/-! ### Works (monomorphic — no type variable):

inductive MyContainsNat : Nat → List Nat → Prop where
  | here : ∀ x rest, MyContainsNat x (x :: rest)
  | there : ∀ x y rest, MyContainsNat x rest → MyContainsNat x (y :: rest)

inductive NotInNat : Nat → List Nat → Prop where
  | mk : ∀ x xs, ¬ MyContainsNat x xs → NotInNat x xs

-- This works fine:
derive_mutual
  checker (fun (x : Nat) (xs : List Nat) => MyContainsNat x xs),
  generator (fun (xs : List Nat) => ∃ x, NotInNat x xs)
-/

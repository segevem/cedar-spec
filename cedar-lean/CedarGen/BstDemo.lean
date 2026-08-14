import Specimen
import Plausible

open Specimen.Tactic
open Plausible

/-! # Specimen demo — binary search trees

`BST lo hi t` says the tree `t` is a binary search tree whose keys all lie in
`[lo, hi]`. Its `node` rule *builds* a BST from a key and two sub-BSTs whose
bounds are split around that key, so Specimen can generate BSTs
**correct-by-construction** — recursion and the ordering constraint included —
instead of sampling random trees and hoping they happen to be sorted (rejection
sampling, which almost never lands on a BST).
-/

inductive Tree where
  | leaf
  | node : Tree → Nat → Tree → Tree
deriving DecidableEq

/-- Pretty-print trees so counterexamples read like `(· 3 (· 5 ·))`. -/
partial def ppTree : Tree → String
  | .leaf       => "·"
  | .node l x r => s!"({ppTree l} {x} {ppTree r})"

instance : Repr Tree := ⟨fun t _ => ppTree t⟩

deriving instance Plausible.Shrinkable for Tree

/-- `BST lo hi t` — `t` is a BST with every key in `[lo, hi]`. The `node` rule
    splits the bound `[lo, hi]` at the key `x`, recursing left on `[lo, x]` and
    right on `[x, hi]`. -/
inductive BST : Nat → Nat → Tree → Prop where
  | leaf : lo ≤ hi → BST lo hi .leaf
  | node : lo ≤ x → x ≤ hi → BST lo x l → BST x hi r → BST lo hi (.node l x r)

def size : Tree → Nat
  | .leaf       => 0
  | .node l _ r => 1 + size l + size r

/- A (false) property: every BST over `[0, 8]` has at most two nodes.

Rejection sampling over random trees almost never yields a BST, so it would miss
the counterexample. Specimen generates BSTs directly and finds one immediately.
The tactic is *diagnostic* — it reports a counterexample but does not close the
goal, so we discharge it with `sorry`. -/
set_option specimen.autoDeriveDeps true in
example : ∀ t : Tree, BST 0 8 t → size t ≤ 2 := by
  specimen
  sorry

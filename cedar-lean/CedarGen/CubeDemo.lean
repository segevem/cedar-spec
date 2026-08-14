import Specimen
import Plausible

open Specimen.Tactic
open Plausible

/-! # Specimen demo — the cube example (from the EOI talk)

`IsCube n` says `n` is a perfect cube. Its single rule *builds* a cube from a base
`m`, so Specimen can generate cubes **correct-by-construction** — pick `m`, output
`m * m * m` — instead of sampling random naturals and hoping they land on a cube
(rejection sampling, which almost never does).
-/

inductive IsCube : Nat → Prop where
  | mk (m : Nat) : IsCube (m * m * m)

/-- The talk's *false* property: "every perfect cube is ≤ 27."

Rejection sampling over random `Nat`s almost never hits a cube, so it would miss
the counterexample entirely. The `specimen` tactic generates cubes directly and
finds one immediately (e.g. `64 = 4³`). The tactic is *diagnostic* — it reports a
counterexample but does not close the goal, so we discharge it with `sorry`. -/
example : ∀ n : Nat, IsCube (id n) → n ≤ 27 := by
  specimen
  sorry

example : ∀ n : Nat, IsCube n → n ≤ 27 := by
  specimen
  sorry

-- Equivalent one-liner (command form, no proof scaffold):
specimen_test (∀ n : Nat, IsCube n → n ≤ 27)

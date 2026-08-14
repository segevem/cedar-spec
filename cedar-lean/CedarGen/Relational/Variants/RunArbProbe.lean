import CedarGen.Relational.Variants.Default

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible
open Variant.Default

-- What does the `Arbitrary Expr` instance the derive falls back to actually produce?
def main : IO Unit := do
  IO.println "sampling `(Arbitrary.arbitrary : Gen Expr)` across seeds:"
  for s in [1, 2, 3, 5, 7, 11, 42, 99] do
    let e ← Gen.runWith s (Arbitrary.arbitrary : Gen Expr) 4
    IO.println s!"  seed {s}: {(reprStr e).take 120}"

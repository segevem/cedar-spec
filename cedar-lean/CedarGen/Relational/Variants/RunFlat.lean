import CedarGen.Relational.Variants.Flat
import CedarGen.Relational.Variants.SmokeTest

open Variant.Flat in
def main : IO Unit := do
  IO.println "=== flat (BudgetAwareScore + flatCtorWeight) ==="
  timedTest testEnv defaultCaps #[5, 7, 8]

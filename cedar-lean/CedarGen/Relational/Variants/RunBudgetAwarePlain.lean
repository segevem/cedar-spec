import CedarGen.Relational.Variants.BudgetAwarePlain
import CedarGen.Relational.Variants.SmokeTest

open Variant.BudgetAwarePlain in
def main : IO Unit := do
  IO.println "=== budget-aware PLAIN (BudgetAwareScore, no weight modifier) ==="
  timedTest testEnv defaultCaps testSizes

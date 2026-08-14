import CedarGen.Relational.Variants.BudgetAware
import CedarGen.Relational.Variants.SmokeTest

open Variant.BudgetAware in
def main : IO Unit := do
  IO.println "=== budget-aware (BudgetAwareScore + balancedCtorWeight) ==="
  timedTest testEnv defaultCaps testSizes

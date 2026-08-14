import CedarGen.Relational.Variants.Custom
import CedarGen.Relational.Variants.SmokeTest

open Variant.Custom in
def main : IO Unit := do
  IO.println "=== custom (BudgetAwareScore + cedarHasTypeWeight) ==="
  timedTest testEnv defaultCaps testSizes

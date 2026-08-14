import CedarGen.Relational.Variants.Steep
import CedarGen.Relational.Variants.SmokeTest

open Variant.Steep in
def main : IO Unit := do
  IO.println "=== steep (BudgetAwareScore + steepQualityWeight 16/4/2/1) ==="
  timedTest testEnv defaultCaps testSizes

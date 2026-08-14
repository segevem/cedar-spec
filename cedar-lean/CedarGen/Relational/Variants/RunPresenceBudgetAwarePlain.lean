import CedarGen.Relational.Variants.BudgetAwarePlain
import CedarGen.Relational.Variants.PresenceTest

open Variant.BudgetAwarePlain in
def main : IO Unit := do
  IO.println "=== BudgetAware plain (no weighting): type distribution + construct presence ==="
  PresenceTest.analyzeGen testEnv defaultCaps #[10, 12, 15] 1500

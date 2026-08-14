import CedarGen.Relational.Variants.BudgetAware
import CedarGen.Relational.Variants.PresenceTest

open Variant.BudgetAware in
def main : IO Unit := do
  IO.println "=== BudgetAware + favorHasTag: type distribution + construct presence ==="
  PresenceTest.analyzeGen testEnv defaultCaps #[10, 12, 15] 1500

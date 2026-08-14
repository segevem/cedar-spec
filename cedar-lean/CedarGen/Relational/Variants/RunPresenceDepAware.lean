import CedarGen.Relational.Variants.DepAwareDefault
import CedarGen.Relational.Variants.PresenceTest

open Variant.DepAwareDefault in
def main : IO Unit := do
  IO.println "=== DepAwareDefaultScore: type distribution + construct presence ==="
  PresenceTest.analyzeGen testEnv defaultCaps #[10, 12, 15] 1500

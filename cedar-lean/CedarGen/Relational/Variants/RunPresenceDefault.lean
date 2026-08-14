import CedarGen.Relational.Variants.Default
import CedarGen.Relational.Variants.PresenceTest

open Variant.Default in
def main : IO Unit := do
  IO.println "=== DefaultScore: type distribution + construct presence ==="
  PresenceTest.analyzeGen testEnv defaultCaps #[10, 12, 15] 1500

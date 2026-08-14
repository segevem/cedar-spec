import CedarGen.Relational.Variants.DefaultCheck
import CedarGen.Relational.Variants.PresenceTest

open Variant.DefaultCheck in
def main : IO Unit := do
  IO.println "=== DefaultScore + typeOf-backed checker: type distribution + presence ==="
  PresenceTest.analyzeGen testEnv defaultCaps #[10, 12, 15] 1500

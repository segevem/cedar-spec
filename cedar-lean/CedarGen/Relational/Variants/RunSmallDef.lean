import CedarGen.Relational.Variants.Default
import CedarGen.Relational.Variants.PresenceTest
open Variant.Default in
def main : IO Unit := do
  IO.println "=== DefaultScore (fixed) at small size ==="
  PresenceTest.analyzeGen testEnv defaultCaps #[3, 4] 200

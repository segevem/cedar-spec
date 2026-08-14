import CedarGen.Relational.Variants.Default
import CedarGen.Relational.Variants.SmokeTest

open Variant.Default in
def main : IO Unit := do
  IO.println "=== default (DefaultScore + balancedCtorWeight) ==="
  timedTest testEnv defaultCaps testSizes

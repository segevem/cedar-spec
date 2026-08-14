import CedarGen.Relational.Variants.Density
import CedarGen.Relational.Variants.SmokeTest

open Variant.Density in
def main : IO Unit := do
  IO.println "=== density (DensityScore + balancedCtorWeight, no weight modifier) ==="
  timedTest testEnv defaultCaps testSizes

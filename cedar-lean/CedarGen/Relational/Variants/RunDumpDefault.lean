import CedarGen.Relational.Variants.Default
import CedarGen.Relational.Variants.PresenceTest


open Variant.Default in
def main : IO Unit := do
  IO.println "=== DefaultScore: why are outputs ill-typed? (8 examples) ==="
  PresenceTest.dumpIllTyped testEnv defaultCaps #[2] 1

#eval main

open CedarGen.Relational.Lean Variant.Default in
#eval show IO Unit from do
  for fuel in [0, 1, 3, 10] do
    let r := DecOpt.decOpt
      (P := HasType (.binaryApp .getTag (.lit (.bool true)) (.lit (.bool true))) defaultCaps testEnv .string []) fuel
    let s := match r with
      | .ok true  => "ok true"
      | .ok false => "ok false"
      | .error _  => "error / unknown"
    IO.println s!"fuel={fuel}: {s}"

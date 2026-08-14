import CedarGen.Relational.Variants.Default

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible
open Variant.Default

def main : IO Unit := do
  IO.println "=== full exprs the generator returns for target `set int` (empty caps) ==="
  for s in [5, 6, 7, 8, 9] do
    try
      let (x, _) ← Gen.runUntilWith s (attempts := .some 1)
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (e, cout) => HasType e [] testEnv (.set .int) cout) 4) 4
      IO.println s!"\nseed {s}:\n{reprStr x}"
    catch e => IO.println s!"seed {s}: threw {e}"

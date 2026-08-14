import CedarGen.Relational.Variants.Default

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible
open Variant.Default

-- Ask the DefaultScore generator for an expr of a *specific* type and see whether it ever
-- returns something of the wrong type (fabrication via an unchecked Arbitrary fallback).
def probe (label : String) (ty : CedarType) (size : Nat) (n : Nat)
    [ArbitrarySizedSuchThat (Expr × Capabilities) (fun (e, cout) => HasType e [] testEnv ty cout)]
    : IO Unit := do
  let mut match_ := 0
  let mut wrong := 0
  let mut err := 0
  let mut examples : Array String := #[]
  for _ in [0:n] do
    try
      let (x, _) ← Gen.runUntil (attempts := .some 1)
        (ArbitrarySizedSuchThat.arbitrarySizedST (fun (e, cout) => HasType e [] testEnv ty cout) size) 5
      match Cedar.Validation.typeOf x [] testEnv with
      | .ok (tx, _) =>
        if tx.typeOf == ty then match_ := match_ + 1
        else
          wrong := wrong + 1
          if examples.size < 5 then examples := examples.push s!"got {reprStr tx.typeOf}: {(reprStr x).take 100}"
      | .error _ =>
        err := err + 1
        if examples.size < 5 then examples := examples.push s!"ILL-TYPED: {(reprStr x).take 100}"
    catch _ => pure ()
  IO.println s!"\n[{label}] asked for {reprStr ty} @size {size}, n={n}"
  IO.println s!"  on-target={match_}  wrong-type={wrong}  ill-typed={err}"
  for e in examples do IO.println s!"    e.g. {e}"

def main : IO Unit := do
  probe "entity User" (.entity ⟨"User", []⟩) 4 30
  probe "set int"     (.set .int)            4 30
  probe "string"      .string                4 30

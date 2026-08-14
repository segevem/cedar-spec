import CedarGen.Relational.Variants.Default

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

open Variant.Default in
def main : IO Unit := do
  let ety : EntityType := ⟨"User", []⟩
  let show3 (r : Except GenError Bool) : String :=
    match r with
    | .ok true  => "ok true"
    | .ok false => "ok FALSE  (correct reject)"
    | .error _  => "ERROR / unknown  (<-- would NOT reject)"
  IO.println "Q1: is `true` an entity User?   HasType (lit true) [] testEnv (entity User) []"
  for fuel in [1,2,3,5,10,20,50] do
    IO.println s!"  fuel={fuel}: {show3 (DecOpt.decOpt (P := HasType (.lit (.bool true)) [] testEnv (.entity ety) []) fuel)}"
  IO.println "\nQ2 (control): is `true` a bool tt?   HasType (lit true) [] testEnv (bool tt) []"
  for fuel in [1,3,10] do
    IO.println s!"  fuel={fuel}: {show3 (DecOpt.decOpt (P := HasType (.lit (.bool true)) [] testEnv (.bool .tt) []) fuel)}"
  IO.println "\nQ3: is `true` a string?   HasType (lit true) [] testEnv string []"
  for fuel in [1,3,10] do
    IO.println s!"  fuel={fuel}: {show3 (DecOpt.decOpt (P := HasType (.lit (.bool true)) [] testEnv .string []) fuel)}"
  IO.println "\nQ4: SAME but id-WRAPPED (as in getTag's premise):  HasType (id (lit true)) [] testEnv (entity User) []"
  for fuel in [1,3,10,20] do
    IO.println s!"  fuel={fuel}: {show3 (DecOpt.decOpt (P := HasType (id (.lit (.bool true))) [] testEnv (.entity ety) []) fuel)}"
  IO.println "\nQ5: the whole thing:  HasType (getTag true true) [] testEnv (bool anyBool) []"
  for fuel in [1,3,10,20] do
    IO.println s!"  fuel={fuel}: {show3 (DecOpt.decOpt (P := HasType (.binaryApp .getTag (.lit (.bool true)) (.lit (.bool true))) [] testEnv (.bool .anyBool) []) fuel)}"

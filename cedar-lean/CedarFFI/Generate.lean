/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Basalt.IO
import CedarGen.Relational.PolicyGen
import CedarGen.Relational.SchemaGenFDerive
import CedarProto.Encode
import Lean.Data.Json

/-! # Inputs from the derived generators, for the Rust harness

`generateSchemaPolicies` draws a schema with the derived `GenTypeEnvF` generator, every flag on (a
well-formed schema whose names Rust accepts, `genTypeEnvF_iff_validateWellFormed`), then policies
with the derived `ValidGuidedPolicy` generator over the schema's request environments (each valid
for the schema, `validate_generated`). Both run at `IO`, on Basalt's SplitMix.

Parameters, as JSON: `seed`, `size` (the generators' size, default 8), `budget` (the most request
environments a schema has, default 8), `count` (policies, default 8). The result is

  `[u32 schema length][Schema][u32 n]`, then `n` times `[u32 length][PolicySet of one policy]`

with lengths little-endian, or empty bytes when no schema was found. -/

-- Compiling the calls to the derived instances takes the compiler longer than the default allows.
set_option maxHeartbeats 0

namespace CedarFFI.Generate

open Cedar.Spec Cedar.Validation Cedar.Validation.Relational
open Cedar.Validation.Relational.SchemaGen Cedar.Validation.Relational.PolicyGen

/-- The generators' monad at `IO`: failure, and running out of fuel, are both `none`. -/
abbrev G := ExceptT Specimen.Exhaustion (OptionT IO)

/-- SplitMix64's finalizer: consecutive seeds give unrelated streams. -/
def scramble (seed : UInt64) : UInt64 :=
  let x := seed + 0x9e3779b97f4a7c15
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

/-- Run `g` from `seed`. -/
def run (seed : UInt64) (g : G α) : IO (Option α) := do
  ioGen.set (SplitMix.ofSeed (scramble seed))
  match ← g.run.run with
  | some (.ok a) => pure (some a)
  | _ => pure none

/-- A schema, from the first of `attempts` seeds the generator succeeds on. -/
def schema (seed : UInt64) (size budget : Nat) (attempts : Nat := 16) : IO (Option TypeEnv) := do
  for i in [0:attempts] do
    if let some (_, env) ← run (seed * 64 + i.toUInt64) (BacktrackGenFor.gen
        (P := fun p : HierMode × TypeEnv => GenTypeEnvF true true true true true true true p.1 budget p.2)
        (G := G) size size) then
      return some env
  return none

/-- `count` policies valid for `S`, from consecutive seeds, skipping the seeds the generator fails
on (at most `count * 64` seeds in all). -/
def policies (S : Schema) (seed : UInt64) (size count : Nat) : IO (List Policy) := do
  let mut out := #[]
  for i in [0:count * 64] do
    if out.size ≥ count then break
    if let some p ← run (seed + i.toUInt64) (BacktrackGenFor.gen
        (P := fun p => ValidGuidedPolicy S.ets S.acts S.environments p) (G := G) size size) then
      out := out.push p
  return out.toList

private def u32 (n : Nat) : ByteArray :=
  ⟨#[n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]⟩

private def framed (b : ByteArray) : ByteArray := u32 b.size ++ b

private def param (j : Lean.Json) (key : String) (default : Nat) : Nat :=
  (j.getObjValAs? Nat key).toOption.getD default

@[export generateSchemaPolicies]
unsafe def generateSchemaPoliciesFFI (req : ByteArray) : ByteArray :=
  unsafeIO (do
    let j := (Lean.Json.parse (String.fromUTF8! req)).toOption.getD (.mkObj [])
    let seed := (param j "seed" 0).toUInt64
    let size := param j "size" 8
    match ← schema seed size (param j "budget" 8) with
    | none => return .empty
    | some env =>
      let ps ← policies env.schema (scramble seed) size (param j "count" 8)
      return ps.foldl (fun acc p => acc ++ framed (CedarProto.Encode.encodePolicies [p]))
        (framed (CedarProto.Encode.encodeSchema env) ++ u32 ps.length))
  |>.toOption.getD .empty

end CedarFFI.Generate

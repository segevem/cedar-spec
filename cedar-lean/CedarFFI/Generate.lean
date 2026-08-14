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

import Lean.Data.Json
import Cedar.Spec
import Cedar.Validation
import CedarGen.Relational.Variants.BudgetAware
import CedarGen.Relational.Variants.Steep
import CedarGen.Relational.Variants.SteepTags
import CedarGen.Relational.Variants.TypeOfCheck
import CedarGen.Relational.TypeOfLeanBase
-- NOTE: BudgetAwarePlain / Custom / Default / Flat / GradedUniform are temporarily
-- not imported: after adding the `HasTypeExtCall` mutual member, their derived
-- generators' `decreasing_by` termination proof exceeds simp's step limit
-- (GradedUniform confirmed; others derive over the same enlarged mutual block).
-- The four kept here (budget-aware, steep, steep-tags, typeof-check) build cleanly.
-- Re-add once the derive-termination proof is fixed.
import CedarGen.Relational.SchemaTest
import CedarGen.Relational.PolicyGen
import CedarGen.Relational.PolicyGenError
import CedarProto.Encode
import CedarProto.PolicySet
import CedarFFI.Main

/-! # Generator FFI with variant dispatch

Each Specimen variant (scoring/weighting combo) is derived in a separate
file under `Variants/`. This module dispatches to the correct scoped
instance based on the `"strategy"` param in the JSON request.
-/

namespace CedarFFI.Generate

open Cedar.Spec
open Cedar.Validation
open CedarGen.Relational.Lean
open Plausible

/-! ## Helpers -/

def getUInt64 (params : Lean.Json) (key : String) (default : UInt64) : UInt64 :=
  match params.getObjValAs? Nat key with
  | .ok n => n.toUInt64
  | .error _ => default

def getUInt32 (params : Lean.Json) (key : String) (default : UInt32) : UInt32 :=
  match params.getObjValAs? Nat key with
  | .ok n => n.toUInt32
  | .error _ => default

def getString (params : Lean.Json) (key : String) (default : String) : String :=
  match params.getObjValAs? String key with
  | .ok s => s
  | .error _ => default

/-! ## Variant-dispatched generation

Each variant generates expressions by opening its namespace to bring
the scoped `ArbitrarySizedSuchThat` instance into scope. -/

open Variant.BudgetAware in
private def generateWithBudgetAware (env : TypeEnv) (caps : Capabilities) (ty : CedarType)
    (size count : Nat) (seed : Option Nat) : IO (List Expr) :=
  generateExprs env caps ty size count seed

open Variant.Steep in
private def generateWithSteep (env : TypeEnv) (caps : Capabilities) (ty : CedarType)
    (size count : Nat) (seed : Option Nat) : IO (List Expr) :=
  generateExprs env caps ty size count seed

open Variant.SteepTags in
private def generateWithSteepTags (env : TypeEnv) (caps : Capabilities) (ty : CedarType)
    (size count : Nat) (seed : Option Nat) : IO (List Expr) :=
  generateExprs env caps ty size count seed

open Variant.TypeOfCheck in
private def generateWithTypeOfCheck (env : TypeEnv) (caps : Capabilities) (ty : CedarType)
    (size count : Nat) (seed : Option Nat) : IO (List Expr) :=
  generateExprs env caps ty size count seed

/-- Dispatch to the appropriate variant based on strategy name.
    When `seed` is `some n`, generation is deterministic and reproducible. -/
def dispatchGenerate (strategy : String) (env : TypeEnv) (caps : Capabilities) (ty : CedarType)
    (size count : Nat) (seed : Option Nat) : IO (List Expr) :=
  match strategy with
  | "steep"               => generateWithSteep env caps ty size count seed
  | "steep-tags"          => generateWithSteepTags env caps ty size count seed
  | "typeof-check"        => generateWithTypeOfCheck env caps ty size count seed
  | _                     => generateWithBudgetAware env caps ty size count seed

/-! ## Protobuf-based generation FFI

Returns raw protobuf-encoded PolicySet bytes.
Accepts a `"strategy"` param to select the Specimen variant. -/

@[export generateTypeOfProto]
unsafe def generateTypeOfProtoFFI (req : ByteArray) : ByteArray :=
  unsafeIO (do
    let reqStr := String.fromUTF8! req
    let params := match Lean.Json.parse reqStr with
      | .ok j => j
      | .error _ => Lean.Json.mkObj []
    let seed := getUInt64 params "seed" 0
    let size := (getUInt32 params "size" 20).toNat
    let count := (getUInt32 params "count" 1).toNat
    let strategy := getString params "strategy" "budget-aware"
    let deterministic := match params.getObjValAs? Bool "deterministic" with
      | .ok b => b | .error _ => false
    let env := testEnv
    let caps := defaultCaps
    let types := #[CedarType.bool .anyBool, .bool .tt, .bool .ff]
    let mut exprs : List Expr := []
    let mut currentSeed := seed.toNat
    for _ in List.range count do
      let tyIdx := currentSeed % types.size
      let ty := types[tyIdx]!
      let genSeed := if deterministic then some currentSeed else none
      let batch ← dispatchGenerate strategy env caps ty size 1 genSeed
      exprs := exprs ++ batch
      currentSeed := currentSeed + 1
    return CedarProto.Encode.encodePolicySet exprs
  ) |>.toOption |>.getD ByteArray.empty

/-! ## Schema + typeof variant

Generates one well-formed `TypeEnv` (schema) and `count` well-typed expressions
against it. The env is transmitted to Rust along with the policies, so a single
expensive schema generation is amortized over many policies.

Wire format:
  [4-byte LE schema length][schema proto bytes]
  [4-byte LE policy count]
  repeated: [4-byte LE policyset length][policyset proto bytes]  (one policy each)
-/

/-- Encode a `Nat` as 4 little-endian bytes. -/
private def encodeU32LE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    (UInt8.ofNat (n % 256)),
    (UInt8.ofNat (n / 256 % 256)),
    (UInt8.ofNat (n / 65536 % 256)),
    (UInt8.ofNat (n / 16777216 % 256)) ]

@[export generateSchemaTypeOfProto]
unsafe def generateSchemaTypeOfProtoFFI (req : ByteArray) : ByteArray :=
  unsafeIO (do
    let reqStr := String.fromUTF8! req
    let params := match Lean.Json.parse reqStr with
      | .ok j => j
      | .error _ => Lean.Json.mkObj []
    let seed := getUInt64 params "seed" 0
    let size := (getUInt32 params "size" 20).toNat
    -- Schema fuel defaults to the term fuel but can be set independently
    -- (e.g. richer schemas: schema_size=20 with size=12 terms).
    let schemaSize := (getUInt32 params "schema_size" (size.toUInt32)).toNat
    let count := (getUInt32 params "count" 1000).toNat
    let strategy := getString params "strategy" "budget-aware"
    -- Generate one schema, then dispatch to the chosen variant for the terms.
    match ← generateSchemaOnly seed.toNat schemaSize with
    | some env =>
      let schemaBytes := CedarProto.Encode.encodeSchema env
      let mut out := encodeU32LE schemaBytes.size
      out := out ++ schemaBytes
      if strategy == "welltyped-policy" || strategy == "illtyped-policy" || strategy == "mixed-policy" then
        -- Policy-level generators (real principal/action/resource scope constraints), each
        -- encoded as a PolicySet with `encodePolicies`. Three variants:
        --   welltyped-policy — all WELL-typed (`WellTypedPolicy`).
        --   illtyped-policy  — all ILL-typed (`IllTypedPolicy`/`PolicyBodyErr`, drives error paths).
        --   mixed-policy     — ~half well-typed + half ill-typed (disjoint seed ranges), the
        --                      specimen analog of the handwritten `hw-slots-off` (both kinds).
        let policies ← do
          if strategy == "welltyped-policy" then
            CedarGen.Relational.PolicyGen.generatePolicies env size count (some (seed.toNat + 1))
          else if strategy == "illtyped-policy" then
            CedarGen.Relational.PolicyGenError.generateErrorPolicies env size count (some (seed.toNat + 1))
          else
            let nErr := count / 2
            let nWt := count - nErr
            let wt ← CedarGen.Relational.PolicyGen.generatePolicies env size nWt (some (seed.toNat + 1))
            let er ← CedarGen.Relational.PolicyGenError.generateErrorPolicies env size nErr (some (seed.toNat + 1 + nWt))
            pure (wt ++ er)
        out := out ++ encodeU32LE policies.length
        for p in policies do
          let ps := CedarProto.Encode.encodePolicies [p]
          out := out ++ encodeU32LE ps.size
          out := out ++ ps
      else
        -- Existing path: generate well-typed boolean expressions and wrap each in a
        -- `permit(principal, action, resource) when { expr }` (all-`Any` scopes).
        let exprs ← dispatchGenerate strategy env defaultCaps (.bool .anyBool) size count (some (seed.toNat + 1))
        out := out ++ encodeU32LE exprs.length
        for e in exprs do
          let ps := CedarProto.Encode.encodePolicySet [e]
          out := out ++ encodeU32LE ps.size
          out := out ++ ps
      return out
    | none => return ByteArray.empty
  ) |>.toOption |>.getD ByteArray.empty

/-! ## Ill-typed generator self-check (COMPILED, in-Lean validate)

Generates the ill-typed corpus with the SAME compiled generator the FFI uses, then validates
each policy with the Lean `validate` *before any proto encoding*, returning counts + reprs of
any policy the validator ACCEPTS (i.e. an unsound generator output). This isolates generator
soundness from the proto round-trip. Request/response are JSON UTF-8 bytes. -/
@[export illtypedSelfCheck]
unsafe def illtypedSelfCheckFFI (req : ByteArray) : ByteArray :=
  unsafeIO (do
    let reqStr := String.fromUTF8! req
    let params := match Lean.Json.parse reqStr with
      | .ok j => j | .error _ => Lean.Json.mkObj []
    let seed := getUInt64 params "seed" 0
    let size := (getUInt32 params "size" 20).toNat
    let schemaSize := (getUInt32 params "schema_size" (size.toUInt32)).toNat
    let count := (getUInt32 params "count" 100).toNat
    match ← generateSchemaOnly seed.toNat schemaSize with
    | none => return "{\"error\":\"no schema\"}".toUTF8
    | some env =>
      let schema : Schema := ⟨env.ets, env.acts⟩
      let policies ← CedarGen.Relational.PolicyGenError.generateErrorPolicies env size count (some (seed.toNat + 1))
      let mut rejected := 0
      let mut accepted := 0
      let mut samples : List String := []
      for p in policies do
        match validate [p] schema with
        | .error _ => rejected := rejected + 1
        | .ok _ =>
          accepted := accepted + 1
          if samples.length < 25 then samples := samples ++ [toString (repr p)]
      let j := Lean.Json.mkObj [
        ("envs", Lean.toJson schema.environments.length),
        ("generated", Lean.toJson policies.length),
        ("rejected", Lean.toJson rejected),
        ("accepted", Lean.toJson accepted),
        ("samples", Lean.toJson samples)]
      return (toString j).toUTF8
  ) |>.toOption |>.getD ByteArray.empty

/-! ## PolicySet proto roundtrip (cross-language fidelity testing)

Decodes a protobuf-encoded `PolicySet` (as produced by cedar-policy's Rust encoder),
links its templates into concrete `Cedar.Spec.Policy`s, and re-encodes them with
`encodePolicies`. A Rust property test uses this to assert that the chain
  Rust encode → Lean decode → Lean encode → Rust decode
preserves the policy set (exercising the scope-constraint encode/decode paths added
in `CedarProto.Encode`). Returns empty bytes if the Lean decode fails, which the Rust
side reports as a roundtrip mismatch. -/
@[export roundtripPolicySetProto]
unsafe def roundtripPolicySetProtoFFI (req : ByteArray) : ByteArray :=
  match (Proto.Message.interpret? req : Except String Cedar.Spec.Proto.PolicySet) with
  | .ok ps    => CedarProto.Encode.encodePolicies ps.toPolicies
  | .error _  => ByteArray.empty

/-- Decode a protobuf-encoded `Schema` (as produced by cedar-policy's Rust encoder),
link it into a `Cedar.Validation.Schema`, and re-encode with `encodeSchema`. The Rust
schema-roundtrip property test uses this the same way as `roundtripPolicySetProto`:
  Rust encode → Lean decode → Lean encode → Rust decode  should preserve the schema
(exercising the ancestor⇄descendant inversion in both the decoder and the encoder).
`encodeSchema` reads only `ets`/`acts`, so the request type is a placeholder. Returns
empty bytes if the Lean decode fails. -/
@[export roundtripSchemaProto]
unsafe def roundtripSchemaProtoFFI (req : ByteArray) : ByteArray :=
  match ((@Proto.Message.interpret? Cedar.Validation.Proto.Schema) req) >>= (·.toSchema) with
  | .ok s     => CedarProto.Encode.encodeSchema { ets := s.ets, acts := s.acts, reqty := default }
  | .error _  => ByteArray.empty

/-! ## List available strategies -/

@[export listStrategies]
unsafe def listStrategiesFFI (_unit : ByteArray) : String :=
  toString (Lean.toJson (["budget-aware", "steep", "steep-tags", "typeof-check", "welltyped-policy", "illtyped-policy", "mixed-policy"] : List String))

end CedarFFI.Generate

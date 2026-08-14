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

import CedarGen.Relational.InstanceOf
import CedarGen.Relational.DeriveGenerators
import CedarGen.Prim
import CedarGen.Data
import CedarGen.Value
import CedarGen.Schema
import Specimen

/-! # Mutual generators for InstanceOf / AllInstanceOf / RecordFieldsConform

These generators are assembled from Specimen's `derive_generator` output,
combined into a mutual block with cross-references resolved.
-/

namespace CedarGen.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

-- DecOpt for ValidEntityUID (manual, checks the schema)
instance : DecOpt (ValidEntityUID uid ets acts) where
  decOpt _ :=
    let valid := match ets.find? uid.ty with
      | some (.standard _) => true
      | some (.enum eids) => eids.contains uid.eid
      | none => acts.contains uid
    .ok valid

-- DecOpt for list membership (needed by RecordFieldsConform)
instance [DecidableEq α] : DecOpt (Membership.mem (l : List α) (x : α)) where
  decOpt _ := .ok (l.contains x)

/-! ## Mutual generator definitions -/

mutual

def genInstanceOf (initSize : Nat) (size : Nat) (ty : CedarType) (ets : EntitySchema) (acts : ActionSchema) :
    Gen Value :=
  match size with
  | Nat.zero =>
    GeneratorCombinators.backtrack
      [(1, match ty with
        | .bool bty => do
          let b ← ArbitrarySizedSuchThat.arbitrarySizedST (fun b => InstanceOfBool b bty) initSize
          return Value.prim (.bool b)
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .int => do
          let i ← Arbitrary.arbitrary (α := Int64)
          return Value.prim (.int i)
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .string => do
          let s ← Arbitrary.arbitrary (α := String)
          return Value.prim (.string s)
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .entity ety => do
          let eid ← Arbitrary.arbitrary (α := String)
          let uid : EntityUID := ⟨ety, eid⟩
          match DecOpt.decOpt (ValidEntityUID uid ets acts) initSize with
          | .ok true => return Value.prim (.entityUID uid)
          | _ => MonadExcept.throw Gen.genericFailure
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .ext xty => do
          let x ← ArbitrarySizedSuchThat.arbitrarySizedST (fun x => InstanceOfExt x xty) initSize
          return Value.ext x
        | _ => MonadExcept.throw Gen.genericFailure)]
  | Nat.succ size' =>
    GeneratorCombinators.backtrack
      [(1, match ty with
        | .bool bty => do
          let b ← ArbitrarySizedSuchThat.arbitrarySizedST (fun b => InstanceOfBool b bty) initSize
          return Value.prim (.bool b)
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .int => do
          let i ← Arbitrary.arbitrary (α := Int64)
          return Value.prim (.int i)
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .string => do
          let s ← Arbitrary.arbitrary (α := String)
          return Value.prim (.string s)
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .entity ety => do
          let eid ← Arbitrary.arbitrary (α := String)
          let uid : EntityUID := ⟨ety, eid⟩
          match DecOpt.decOpt (ValidEntityUID uid ets acts) initSize with
          | .ok true => return Value.prim (.entityUID uid)
          | _ => MonadExcept.throw Gen.genericFailure
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .set elemTy => do
          let elems ← genAllInstanceOf initSize size' elemTy ets acts
          return Value.set (Set.make elems)
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .record rty => do
          let fields ← genRecordFieldsConform initSize size' rty.toList ets acts
          return Value.record (Map.make fields)
        | _ => MonadExcept.throw Gen.genericFailure),
       (1, match ty with
        | .ext xty => do
          let x ← ArbitrarySizedSuchThat.arbitrarySizedST (fun x => InstanceOfExt x xty) initSize
          return Value.ext x
        | _ => MonadExcept.throw Gen.genericFailure)]

def genAllInstanceOf (initSize : Nat) (size : Nat) (ty : CedarType) (ets : EntitySchema) (acts : ActionSchema) :
    Gen (List Value) :=
  match size with
  | Nat.zero => GeneratorCombinators.backtrack [(1, return [])]
  | Nat.succ size' =>
    GeneratorCombinators.backtrack
      [(1, return []),
       (Nat.succ size', do
          let v ← genInstanceOf initSize size' ty ets acts
          let vs ← genAllInstanceOf initSize size' ty ets acts
          return v :: vs)]

def genRecordFieldsConform (initSize : Nat) (size : Nat) (rty : List (Attr × QualifiedType))
    (ets : EntitySchema) (acts : ActionSchema) : Gen (List (Attr × Value)) :=
  match size with
  | Nat.zero => GeneratorCombinators.backtrack [(1, return [])]
  | Nat.succ size' =>
    GeneratorCombinators.backtrack
      [(1, return []),
       (Nat.succ size', do
          -- Pick a random (k, qty) from rty
          let k ← Arbitrary.arbitrary (α := String)
          let qty ← Arbitrary.arbitrary (α := QualifiedType)
          match DecOpt.decOpt (Membership.mem rty (k, qty)) initSize with
          | .ok true => do
            let v ← genInstanceOf initSize size' qty.getType ets acts
            let rest ← genRecordFieldsConform initSize size' rty ets acts
            return (k, v) :: rest
          | _ => MonadExcept.throw Gen.genericFailure)]

end

/-! ## Register typeclass instances -/

instance : ArbitrarySizedSuchThat Value (fun v => InstanceOf v ty ets acts) where
  arbitrarySizedST := fun size => genInstanceOf size size ty ets acts

instance : ArbitrarySizedSuchThat (List Value) (fun elems => AllInstanceOf elems ty ets acts) where
  arbitrarySizedST := fun size => genAllInstanceOf size size ty ets acts

instance : ArbitrarySizedSuchThat (List (Attr × Value)) (fun fields => RecordFieldsConform fields rty ets acts) where
  arbitrarySizedST := fun size => genRecordFieldsConform size size rty ets acts

/-! ## Convenience: generate a value of a given type -/

def generateValue (ty : CedarType) (ets : EntitySchema) (acts : ActionSchema) (size : Nat := 5) : Gen Value :=
  genInstanceOf size size ty ets acts

end CedarGen.Relational

/-! ## Quick test -/

open Cedar.Spec Cedar.Data Cedar.Validation CedarGen.Relational Plausible in
#eval do
  let ets : EntitySchema := Map.make [
    ({ id := "User", path := [] }, .standard { ancestors := Set.empty, attrs := Map.make [("name", .required .string)], tags := none })
  ]
  let acts : ActionSchema := Map.empty
  let run (name : String) (ty : CedarType) : IO Unit := do
    try
      let v ← Gen.run (generateValue ty ets acts 5) 42
      IO.println s!"  {name} → {repr v}"
    catch _ =>
      IO.println s!"  {name} → (generation failed)"
  run "int" .int
  run "string" .string
  run "bool" (.bool .anyBool)
  run "set<string>" (.set .string)

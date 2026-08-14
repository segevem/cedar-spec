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
import CedarGen.Prim
import CedarGen.Data
import CedarGen.Value
import CedarGen.Schema
import Specimen

/-! # Derive constrained generators from relational specs using Specimen

This module uses Specimen's `derive_generator` to automatically produce
generators that satisfy the relational specifications in `InstanceOf.lean`.
-/

namespace CedarGen.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Generate values of a given bool type -/

derive_generator (fun bty => ∃ b, InstanceOfBool b bty)

/-! ## Generate values of a given extension type -/

derive_generator (fun xty => ∃ x, InstanceOfExt x xty)

/-! ## Mutual recursive generators for InstanceOf / AllInstanceOf / RecordFieldsConform

    Strategy: provide dummy stubs for the mutual dependencies, derive each generator
    individually (capturing the output), then assemble into a mutual block. -/

-- Dummy stubs so Specimen can derive each generator in isolation
instance : DecOpt (ValidEntityUID uid ets acts) where
  decOpt _ := .ok true

instance : ArbitrarySizedSuchThat Value (fun v => InstanceOf v ty ets acts) where
  arbitrarySizedST _ := MonadExcept.throw Plausible.Gen.genericFailure

instance : ArbitrarySizedSuchThat (List Value) (fun elems => AllInstanceOf elems ty ets acts) where
  arbitrarySizedST _ := return []

instance : ArbitrarySizedSuchThat (List (Attr × Value)) (fun fields => RecordFieldsConform fields rty ets acts) where
  arbitrarySizedST _ := return []

-- Now derive each generator. The output will be printed.
derive_generator (fun ty ets acts => ∃ v, InstanceOf v ty ets acts)

derive_generator (fun ty ets acts => ∃ elems, AllInstanceOf elems ty ets acts)

derive_generator (fun rty ets acts => ∃ fields, RecordFieldsConform fields rty ets acts)

/-! ## Quick smoke test: generate a Value of type Int -/

#eval do
  let ets : EntitySchema := Map.empty
  let acts : ActionSchema := Map.empty
  let gen := ArbitrarySizedSuchThat.arbitrarySizedST
    (fun (v : Value) => InstanceOf v .int ets acts) 10
  let v ← gen.run 42
  IO.println s!"Generated int value: {repr v}"

end CedarGen.Relational

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

import Cedar.Spec
import Specimen
import CedarGen.Prim
import CedarGen.Data
import CedarGen.ExtFun

/-! Arbitrary instance for Cedar.Spec.Value (recursive via Set/Map) -/

namespace CedarGen

open Cedar.Spec
open Cedar.Data
open Plausible

/-! ## Value

Value is recursive through Set Value and Map Attr Value.
We use explicit fuel to bound recursion depth.
-/

private partial def genValue (fuel : Nat) : Gen Value := do
  if fuel = 0 then
    return .prim (← Arbitrary.arbitrary)
  else
    let ⟨choice, _⟩ ← Gen.choose Nat 0 9 (by omega)
    match choice with
    | 0 | 1 | 2 | 3 | 4 => return .prim (← Arbitrary.arbitrary)
    | 5 | 6 => do
      let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
      let mut elems : List Value := []
      for _ in List.range len do
        elems := (← genValue (fuel - 1)) :: elems
      return .set (Set.make elems)
    | 7 | 8 => do
      let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
      let mut pairs : List (Attr × Value) := []
      for _ in List.range len do
        let k ← Arbitrary.arbitrary (α := String)
        let v ← genValue (fuel - 1)
        pairs := (k, v) :: pairs
      return .record (Map.make pairs)
    | _ => return .ext (← Arbitrary.arbitrary)

instance : Arbitrary Value where
  arbitrary := genValue 3

end CedarGen

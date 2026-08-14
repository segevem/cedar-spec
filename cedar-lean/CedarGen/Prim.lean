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

/-! Arbitrary instances for Cedar primitive types: Var, Name, EntityUID, Prim -/

namespace CedarGen

open Cedar.Spec
open Cedar.Data
open Plausible

/-! ## String generation

We draw from a small pool of identifiers to increase collisions,
which makes generated inputs more interesting for testing.
-/

private def identPool : List String :=
  ["a", "b", "c", "d", "e", "foo", "bar", "baz", "id", "name", "owner"]

private def entityIdPool : List String :=
  ["alice", "bob", "carol", "dave", "resource1", "resource2", "doc1"]

instance : Inhabited String := ⟨"a"⟩

instance arbString : Arbitrary String where
  arbitrary := GeneratorCombinators.elementsWithDefault "a" identPool

/-! ## Var -/

instance : Arbitrary Var where
  arbitrary := Gen.elements [.principal, .action, .resource, .context] (by decide)

/-! ## Name / EntityType -/

private def genId : Gen Id :=
  GeneratorCombinators.elementsWithDefault "a" identPool

private def genPath : Gen (List Id) := do
  let ⟨len, _⟩ ← Gen.choose Nat 0 2 (by omega)
  let mut path : List Id := []
  for _ in List.range len do
    path := (← genId) :: path
  return path

instance : Arbitrary Name where
  arbitrary := do
    let id ← genId
    let path ← genPath
    return { id, path }

instance arbEntityType : Arbitrary EntityType where
  arbitrary := (inferInstance : Arbitrary Name).arbitrary

/-! ## EntityUID -/

instance : Arbitrary EntityUID where
  arbitrary := do
    let ty ← arbEntityType.arbitrary
    let eid ← GeneratorCombinators.elementsWithDefault "alice" entityIdPool
    return { ty, eid }

/-! ## Int64 -/

instance : Arbitrary Int64 where
  arbitrary := do
    let ⟨i, _⟩ ← Gen.choose Int (-100) 100 (by omega)
    return Int64.ofInt i

/-! ## Prim -/

instance : Arbitrary Prim where
  arbitrary :=
    Gen.oneOfWithDefault
      (pure (.bool true))
      [ pure (.bool false),
        (do return .int (← Arbitrary.arbitrary)),
        (do return .string (← Arbitrary.arbitrary)),
        (do return .entityUID (← Arbitrary.arbitrary)) ]

end CedarGen

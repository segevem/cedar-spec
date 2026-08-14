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

import Cedar.Data
import Specimen

/-! Arbitrary instances for Cedar.Data.Set and Cedar.Data.Map -/

namespace CedarGen

open Cedar.Data
open Plausible

/-! ## Set

Cedar Sets are sorted, duplicate-free lists. We generate a list and then
use `Set.make` which sorts and deduplicates.
-/

instance [Arbitrary α] [LT α] [DecidableLT α] :
    Arbitrary (Set α) where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 4 (by omega)
    let mut elems : List α := []
    for _ in List.range len do
      elems := (← Arbitrary.arbitrary) :: elems
    return Set.make elems

/-! ## Map

Cedar Maps are sorted by key, duplicate-free. We generate key-value pairs
and use `Map.make` which sorts and deduplicates by key.
-/

instance [Arbitrary α] [Arbitrary β] [LT α] [DecidableLT α] :
    Arbitrary (Map α β) where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 4 (by omega)
    let mut pairs : List (α × β) := []
    for _ in List.range len do
      let k ← Arbitrary.arbitrary
      let v ← Arbitrary.arbitrary
      pairs := (k, v) :: pairs
    return Map.make pairs

end CedarGen

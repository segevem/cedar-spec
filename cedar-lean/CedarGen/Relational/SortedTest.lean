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

import Specimen
import Plausible

set_option match.ignoreUnusedAlts true

/-! # Testing sorted list generation with Specimen

InsertSorted is defined twice: once with separate args (x, xs, sorted)
and once tupled (sorted, (x, xs)). SortedOf uses the tupled version
so it works in both directions with Specimen.
-/

/-! ## InsertSorted: both forms -/

-- Standard form: given x and xs, produce sorted
inductive InsertSorted : Nat → List Nat → List Nat → Prop where
  | nil : InsertSorted x [] [x]
  | lt : ∀ x y ys, x < y → InsertSorted x (y :: ys) (x :: y :: ys)
  | ge : ∀ x y ys zs, ¬(x < y) → InsertSorted x ys zs → InsertSorted x (y :: ys) (y :: zs)

-- Tupled form: given sorted, produce (x, xs) — same relation, invertible
inductive InsertSortedT : List Nat → Nat × List Nat → Prop where
  | nil : InsertSortedT [x] (x,[])
  | hd : ∀ x ys, InsertSortedT (x :: ys) (x, ys)
  | tl : ∀ y zs x ys, ¬(x < y) → InsertSortedT zs (x, ys) → InsertSortedT (y :: zs) (x, y :: ys)

/-! ## SortedOf using the tupled InsertSortedT -/

inductive SortedOf : List Nat → List Nat → Prop where
  | nil : SortedOf [] []
  | cons : ∀ xs zs x ys,
    SortedOf xs ys →
    InsertSortedT zs (x, ys) →
    SortedOf (x :: xs) zs

/-! ## DecOpt instances for arithmetic comparisons -/

instance (n m : Nat) : DecOpt (n < m) where
  decOpt _ := .ok (n < m)

instance (n m : Nat) : DecOpt (¬(n < m)) where
  decOpt _ := .ok (!(n < m))

set_option match.ignoreUnusedAlts true in

/-! ## Derive generators -/

-- Forward: given x and xs, produce sorted
derive_generator (fun x xs => ∃ sorted, InsertSorted x xs sorted)

-- Forward tupled: given sorted, produce (x, xs)
derive_generator (fun sorted => ∃ pair, InsertSortedT sorted pair)

derive_generator (fun pair => ∃ sorted, InsertSortedT sorted pair)

-- Forward sort: given unsorted, produce sorted
derive_generator (fun xs => ∃ sorted, SortedOf xs sorted)

-- Inverse sort: given sorted, produce unsorted
derive_generator (fun sorted => ∃ xs, SortedOf xs sorted)

-- Find element: given xs and sorted, find x
derive_generator (fun xs sorted => ∃ x, InsertSorted x xs sorted)

/-! ## Derive enumerators -/

derive_enumerator (fun x xs => ∃ sorted, InsertSorted x xs sorted)
derive_enumerator (fun sorted => ∃ pair, InsertSortedT sorted pair)
derive_enumerator (fun xs => ∃ sorted, SortedOf xs sorted)
derive_enumerator (fun sorted => ∃ xs, SortedOf xs sorted)

/-! ## Test generators -/

open Plausible in
def testInsert (x : Nat) (xs : List Nat) (seed size : Nat) : IO Unit := do
  try
    let result ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST (fun sorted => InsertSorted x xs sorted) size) seed
    IO.println s!"  InsertSorted {x} {xs} → {result}"
  catch _ =>
    IO.println s!"  InsertSorted {x} {xs} → (failed)"

open Plausible in
def testSort (xs : List Nat) (seed size : Nat) : IO Unit := do
  try
    let result ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST (fun sorted => SortedOf xs sorted) size) seed
    IO.println s!"  SortedOf {xs} → {result}"
  catch _ =>
    IO.println s!"  SortedOf {xs} → (failed)"

open Plausible in
def testUnsort (sorted : List Nat) (seed size : Nat) : IO Unit := do
  try
    let result ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST (fun xs => SortedOf xs sorted) size) seed
    IO.println s!"  SortedOf⁻¹ {sorted} → {result}"
  catch _ =>
    IO.println s!"  SortedOf⁻¹ {sorted} → (failed)"

open Plausible in
def testExtract (sorted : List Nat) (seed size : Nat) : IO Unit := do
  try
    let result ← Gen.run
      (ArbitrarySizedSuchThat.arbitrarySizedST (fun pair => InsertSortedT sorted pair) size) seed
    IO.println s!"  InsertSortedT⁻¹ {sorted} → {result}"
  catch _ =>
    IO.println s!"  InsertSortedT⁻¹ {sorted} → (failed)"

/-! ## Run tests -/

open Plausible in
#eval testInsert 3 [] 42 100
open Plausible in
#eval testInsert 0 [1, 2, 3] 42 100
open Plausible in
#eval testInsert 3 [1, 2, 4, 5] 42 100

open Plausible in
#eval testSort [5, 3, 1, 4, 2] 42 100
open Plausible in
#eval testSort [3, 1, 4, 1, 5, 9] 42 100
open Plausible in
#eval testSort [] 42 100

open Plausible in
#eval testUnsort [1, 2, 3, 4, 5] 42 100
open Plausible in
#eval testUnsort [1, 2, 3] 42 100
open Plausible in
#eval testUnsort [] 42 100

open Plausible in
#eval testExtract [1, 2, 3, 4, 5] 42 100
open Plausible in
#eval testExtract [7] 42 100

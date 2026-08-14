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

import CedarGen.Relational.TypeOfLeanBase

/-! # Variant: BudgetAwareScore + extinction weight

Steep quality (16/4/2/1) plus hard extinction: recursive constructors
get weight 0 at size ≤ 2, forcing immediate termination at leaf nodes.
This eliminates all wasted backtracking in the tail of generation where
recursive attempts almost always fail.

Above size 2, uses the same steep quality scaling as the Steep variant.
Base cases get quality * 5 at all sizes.
-/

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.textOutput 3
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

@[inline] def extinctionWeight (_ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (scoreBadness : Nat) (isRec : Bool)
    (size : Nat) (_numBase numRec : Nat) (_numRecCalls : Nat) : Nat :=
  let quality := if scoreBadness < 250 then 16
    else if scoreBadness < 500 then 4
    else if scoreBadness < 750 then 2
    else 1
  if isRec then
    if size ≤ 2 then 0
    else max 1 (size / max 1 numRec) * quality
  else quality * 5

namespace Variant.Custom

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightFn "extinctionWeight" in
scoped derive_mutual
  generator (fun env c ty => ∃ x cout, HasType x c env ty cout)

end Variant.Custom

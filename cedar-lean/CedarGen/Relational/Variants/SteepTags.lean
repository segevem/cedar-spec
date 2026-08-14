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

import CedarGen.Relational.Variants.BudgetAware
import CedarGen.Relational.Variants.Steep

/-! # Variant: BudgetAwareScore + steep quality curve + favorHasTag modifier

Combines the `steepQualityWeight` base weight function (from `Steep`) with the
`favorHasTag` weight modifier (from `BudgetAware`). The steep curve computes the
base weight; `favorHasTag` then boosts the tag rules on top of it, so this keeps
the tag emphasis of the original schema-gen derive while adopting steep weighting.
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

namespace Variant.SteepTags

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightFn "steepQualityWeight" in
set_option specimen.weightModifier "favorHasTag" in
scoped derive_mutual
  generator (fun env c ty => ∃ x cout, HasType x c env ty cout)

end Variant.SteepTags

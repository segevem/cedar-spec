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

/-! # Variant: GradedUniformDensityScore + balancedCtorWeight -/

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

namespace Variant.GradedUniform

-- DISABLED: after adding the `HasTypeExtCall` mutual member, this variant's
-- derived generator fails its `decreasing_by` termination proof (simp exceeds
-- its step limit) — unique to `GradedUniformDensityScore`, which produces a
-- larger schedule than the other scorers. The variant is unused (only the
-- FFI dispatch referenced it, now removed). Re-enable once the derive-side
-- termination proof is fixed.
-- set_option specimen.scoreType "Scoring.GradedUniformDensityScore" in
-- scoped derive_mutual
--   generator (fun env c ty => ∃ x cout, HasType x c env ty cout)

end Variant.GradedUniform

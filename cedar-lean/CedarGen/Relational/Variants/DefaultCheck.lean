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

/-! # Variant: DefaultScore + `typeOf`-backed `HasType` checker

`Scoring.DefaultScore` with no weight modifier (the ill-typed baseline), but with
the same authoritative `DecOpt (HasType …)` instance `TypeOfCheck` uses: every
`check HasType …` step becomes a real `typeOf` call instead of the (evidently
non-enforcing) auto-derived relational checker. Tests whether a real checker
rescues DefaultScore's validity. -/

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

instance : DecOpt (HasType e c env ty cout) where
  decOpt _ :=
    match (Cedar.Validation.typeOf e c env).typeOf with
    | .ok (ty', cout') => .ok (ty' == ty && cout' == cout)
    | .error _ => .ok false

namespace Variant.DefaultCheck

set_option specimen.scoreType "Scoring.DefaultScore" in
set_option specimen.precomputeWeights true in
scoped derive_mutual
  generator (fun env c ty => ∃ x cout, HasType x c env ty cout)

end Variant.DefaultCheck

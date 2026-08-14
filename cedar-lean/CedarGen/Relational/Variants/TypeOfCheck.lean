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

/-! # Variant: BudgetAwareScore + `typeOf`-backed `HasType` checker

Same scoring/weighting as `Variant.BudgetAware` (`Scoring.BudgetAwareScore`,
`favorHasTag`), but registers a `DecOpt (HasType …)` instance backed by the
functional `Cedar.Validation.typeOf` *before* deriving the generator.

Effect: every `check HasType …` step in the derived schedules becomes a single
authoritative `typeOf` call (the checker projection resolves as "(pre-existing)")
instead of the derived relational checker's recursive backtracking search. Only
the *producing* projections (generator / enumerators) are derived; verification
defers to `typeOf`.
-/

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible
open Scoring Schedules

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.textOutput 3
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-- Check `HasType e c env ty cout` via the functional typechecker: `e` is
well-typed at `ty` with output capabilities `cout` exactly when `typeOf e c env`
succeeds with that type and those capabilities. Defined at the root namespace so
it is synthesizable at derive time; the derive then marks `HasType`'s checker
projection "(pre-existing)" and routes every `check HasType …` step here. -/
instance : DecOpt (HasType e c env ty cout) where
  decOpt _ :=
    match (Cedar.Validation.typeOf e c env).typeOf with
    | .ok (ty', cout') => .ok (ty' == ty && cout' == cout)
    | .error _ => .ok false

namespace Variant.TypeOfCheck

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightModifier "favorHasTag" in
scoped derive_mutual
  generator (fun env c ty => ∃ x cout, HasType x c env ty cout)

end Variant.TypeOfCheck

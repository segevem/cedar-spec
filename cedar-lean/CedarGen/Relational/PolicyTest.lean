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

import CedarGen.Relational.Policy
import CedarGen.Relational.Variants.BudgetAware
import Specimen

/-! # Test: derive a generator for well-typed policies

Layer 2 of the scope-coverage work: given a `TypeEnv`, derive a Specimen generator
that produces a fully well-typed `Policy` — principal/action/resource scope constraints
consistent with the env's request type AND `when`/`unless` conditions whose bodies are
well-typed booleans (via `HasType`), all from `WellTypedPolicy` in `Policy.lean`.

The condition bodies reuse the EXISTING `HasType` generator (the BudgetAware derivation,
brought into scope by `open Variant.BudgetAware`) instead of an unconstrained `Arbitrary Expr`.
The generator is `scoped`, so the `import` alone is not enough — the `open` is what activates
the `ArbitrarySizedSuchThat HasType` instance for the derive to reuse.
-/

open CedarGen.Relational.Policy
open Variant.BudgetAware
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

-- Effect (permit | forbid) is a free field of the generated policy.
deriving instance Plausible.Arbitrary for Effect

/-! ## Derive a generator for well-typed policies

`env` is the input; the policy is the output. The dependency closure pulls in the scope
relations (from `Policy.lean`); the condition body's `HasType` dependency is satisfied by
the already-derived BudgetAware generator that `open Variant.BudgetAware` brings into scope. -/

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.precomputeWeights true in
#time derive_mutual
  generator (fun env => ∃ p, WellTypedPolicy env p)

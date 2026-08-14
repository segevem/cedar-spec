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

/-! # Well-typed policy generator (Layer 2)

Derives a Specimen generator from `WellTypedPolicy` (`Policy.lean`) and exposes a runtime
`generatePolicies` for the FFI. Given a `TypeEnv`, it produces a fully well-typed `Policy`:
principal/action/resource scope constraints consistent with the request type, plus a
`when`/`unless` condition whose bodies are well-typed booleans (via `HasType`).

The condition bodies reuse the EXISTING `HasType` generator (BudgetAware derivation). That
generator is `scoped`, so `open Variant.BudgetAware` — not just the `import` — is what
activates the `ArbitrarySizedSuchThat HasType` instance the derive reuses (rather than
falling back to an unconstrained `Arbitrary Expr`). -/

open Scoring Schedules in
/-- Bias `WellTypedConditions` toward NON-empty conditions: the terminating `nil` is made
    rare and the clause constructors are boosted, so most generated policies carry a `when`
    (and sometimes an `unless`) rather than an empty condition list. The `size`/fuel bound
    still keeps the number of clauses small.

    Defined at ROOT namespace (not under `CedarGen.Relational.PolicyGen`) so the derive's
    `specimen.weightModifier "favorConditions"` resolves it via the env `contains` fallback —
    a namespaced definition would not be found by the short name. -/
def favorConditions (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  -- Target ~1–2 conditions/policy. With the `id bty` fix bodies are cheap, so length is
  -- weight-controlled (geometric): P(continue) = (when+unless)/(nil+when+unless). These
  -- give (when+unless):nil ≈ 4:3 ⇒ P≈0.57 ⇒ E[len]≈1.3. (The old `nil→1` starved
  -- termination; it only looked fine because expensive bodies drained the budget instead.)
  match ctorName with
  | .str (.str _ "WellTypedConditions") "nil"    => baseWeight * 3 + 1
  | .str (.str _ "WellTypedConditions") "when"   => baseWeight * 2 + 1
  | .str (.str _ "WellTypedConditions") "unless" => baseWeight * 2 + 1
  | _                                            => baseWeight

initialize Scoring.registerWeightModifier `favorConditions favorConditions ``favorConditions

namespace CedarGen.Relational.PolicyGen

open CedarGen.Relational.Policy
open Variant.BudgetAware
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible
open Scoring Schedules

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

-- Effect (permit | forbid) is a free field of the generated policy.
deriving instance Plausible.Arbitrary for Effect

set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.precomputeWeights true in
set_option specimen.weightModifier "favorConditions" in
#time derive_mutual
  generator (fun env => ∃ p, WellTypedPolicy env p)

/-- Generate `count` well-typed policies for `env`. Mirrors `generateExprs`: the derived
    `ArbitrarySizedSuchThat` instance is supplied implicitly (deterministic when `seed` is set). -/
def generatePolicies
    (env : TypeEnv) (size count : Nat) (seed : Option Nat := none)
    [inst : ArbitrarySizedSuchThat Policy (fun p => WellTypedPolicy env p)]
    : IO (List Policy) := do
  let mut policies : List Policy := []
  let mut currentSeed := seed.getD 0
  for _ in List.range count do
    try
      let p ← if seed.isSome then
          Gen.runUntilWith currentSeed (attempts := .some 3) (inst.arbitrarySizedST size) size
        else
          Gen.runUntil (attempts := .some 3) (inst.arbitrarySizedST size) size
      policies := policies ++ [p]
    catch _ => pure ()
    currentSeed := currentSeed + 1
  return policies

/-! ## Runtime self-check: generate policies for `testEnv` and confirm the validator accepts them -/

#eval do
  let env := testEnv
  let policies ← generatePolicies env 12 100 (some 45)
  let mut ok := 0
  let mut bad := 0
  for p in policies do
    match typecheckPolicy p env with
    | .ok _    => do
      ok := ok + 1;
      IO.println s!"Policy {ok}: {repr p}\n\n"
    | .error e =>
      bad := bad + 1
      if bad ≤ 3 then IO.println s!"  ILL-TYPED: {repr e}\n    {repr p}"
  IO.println s!"=== generatePolicies: {ok} well-typed, {bad} ill-typed, {policies.length} generated / 20 requested ==="

end CedarGen.Relational.PolicyGen

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

import CedarGen.Relational.PolicyGenError
import CedarGen.Relational.SchemaTest

/-! # Self-checks for the ill-typed policy generator, over REALISTIC generated schemas.

`testEnv` has an empty `Schema.environments` (its actions have empty applies-to sets), which
makes `validate` vacuously return `impossiblePolicy` for everything. So we validate against
schemas from `generateSchemaOnly` (2–11 environments each), i.e. what the real corpus uses.

Test A — soundness of the real `IllTypedPolicy` generator: every generated policy must be
REJECTED by the full multi-environment `validate`; tally actual error kinds.
Test B — per-kind faithfulness: sample `ErrorExpr (x, k)` directly, wrap in trivial (`.any`)
scopes so the body is reached under every environment, and confirm the validator's kind == k. -/

namespace CedarGen.Relational.PolicyGenErrorTest

open CedarGen.Relational.PolicyGenError
open CedarGen.Relational.Lean
open CedarGen.Relational.Policy
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

private def bump (kinds : List (String × Nat)) (k : String) : List (String × Nat) :=
  match kinds.find? (·.1 == k) with
  | some _ => kinds.map (fun (k', n) => if k' == k then (k', n + 1) else (k', n))
  | none   => kinds ++ [(k, 1)]

/-- Predicted kind of a `VErrKind` as the validator's kind string. -/
private def predicted : VErrKind → String
  | .unknownEntity        => "unknownEntity"
  | .unexpectedType       => "unexpectedType"
  | .attrNotFound         => "attrNotFound"
  | .tagNotFound          => "tagNotFound"
  | .lubErr               => "lubErr"
  | .extensionErr         => "extensionErr"
  | .emptySetErr          => "emptySetErr"
  | .incompatibleSetTypes => "incompatibleSetTypes"
  | .impossiblePolicy     => "impossiblePolicy"

/- ## Test A: soundness of the real generator over multi-env schemas. -/
#eval! show IO Unit from do
  let mut rejected := 0
  let mut accepted := 0
  let mut kinds : List (String × Nat) := []
  let mut envs := 0
  for s in List.range 20 do
    let r : Option TypeEnv ← generateSchemaOnly (100 + s) 12
    match r with
    | none => pure ()
    | some env =>
      envs := envs + 1
      let schema : Schema := ⟨env.ets, env.acts⟩
      let policies ← generateErrorPolicies env 12 20 (some (7000 + s))
      for p in policies do
        match validate [p] schema with
        | .error e => rejected := rejected + 1; kinds := bump kinds (errKind e)
        | .ok _    =>
          accepted := accepted + 1
          if accepted ≤ 5 then IO.println s!"  UNSOUND (accepted) under {schema.environments.length} envs: {repr p}"
  IO.println s!"=== TEST A (real generator, {envs} schemas): {rejected} rejected, {accepted} accepted ==="
  IO.println s!"    actual kinds: {repr kinds}"

/- ## Test B: per-kind faithfulness of the faithfully-reconstructed `PolicyBodyErr` (predicted
   VErrKind vs validator kind), `.any` scopes. Uses repr length as a nesting-depth proxy.
   `#eval!` because the derived generator carries a termination `sorry`. -/
#eval! show IO Unit from do
  let mut matched := 0
  let mut mismatched := 0
  let mut byKind : List (String × Nat) := []      -- predicted kinds seen
  let mut misPairs : List (String × String) := [] -- (predicted, actual) mismatches
  let mut nested := 0                              -- defects with node-count > 1 (propagated)
  let mut maxNodes := 0
  for s in List.range 20 do
    let r : Option TypeEnv ← generateSchemaOnly (100 + s) 12
    match r with
    | none => pure ()
    | some env =>
      let schema : Schema := ⟨env.ets, env.acts⟩
      for t in List.range 20 do
        let xk : Option (Expr × VErrKind) ← (do
          try
            let v ← Gen.runUntilWith (9000 + s * 100 + t) (attempts := .some 3)
              (ArbitrarySizedSuchThat.arbitrarySizedST
                (fun (xk : Expr × VErrKind) => PolicyBodyErr ∅ env xk.1 xk.2) 12) 12
            pure (some v)
          catch _ => pure none)
        match xk with
        | none => pure ()
        | some (x, k) =>
          let p : Policy := Policy.mk "p0" .permit (.principalScope .any) (.actionScope .any) (.resourceScope .any) [Condition.mk .when x]
          let pk := predicted k
          byKind := bump byKind pk
          let n := (ToString.toString (repr x)).length   -- repr length ≈ nesting size
          if n > 12 then nested := nested + 1
          if n > maxNodes then maxNodes := n
          match validate [p] schema with
          | .error e =>
            if errKind e == pk then matched := matched + 1
            else
              mismatched := mismatched + 1
              misPairs := (pk, errKind e) :: misPairs
          | .ok _ =>
            mismatched := mismatched + 1
            misPairs := (pk, "ACCEPTED") :: misPairs
  IO.println s!"=== TEST B (faithful PolicyBodyErr): {matched} match, {mismatched} mismatch ==="
  IO.println s!"    predicted-kind distribution: {repr byKind}"
  IO.println s!"    nesting: {nested} defects with >1 node (max nodes = {maxNodes})"
  IO.println s!"    mismatches (predicted → actual): {repr (misPairs.take 15)}"

/- ## Test C: TARGETED generation — ask for each specific kind `k` and confirm the validator
   returns exactly `k`. Reports, per kind, how many were produced (of 30 requested over 3 schemas)
   and how many the validator confirmed as that kind. -/
#eval! show IO Unit from do
  let allKinds : List VErrKind :=
    [.unknownEntity, .unexpectedType, .attrNotFound, .tagNotFound, .lubErr,
     .extensionErr, .emptySetErr, .incompatibleSetTypes, .impossiblePolicy]
  for k in allKinds do
    let mut produced := 0
    let mut confirmed := 0
    for s in List.range 3 do
      let r : Option TypeEnv ← generateSchemaOnly (100 + s) 12
      match r with
      | none => pure ()
      | some env =>
        let schema : Schema := ⟨env.ets, env.acts⟩
        let bodies ← generateBodiesOfKind env k 12 10 (some (5000 + s * 10))
        for x in bodies do
          produced := produced + 1
          let p : Policy := Policy.mk "p0" .permit (.principalScope .any) (.actionScope .any) (.resourceScope .any) [Condition.mk .when x]
          match validate [p] schema with
          | .error e => if errKind e == predicted k then confirmed := confirmed + 1
          | .ok _    => pure ()
    IO.println s!"    kind {predicted k}: produced {produced}/30, validator-confirmed {confirmed}"
  IO.println "=== TEST C (targeted generation) done ==="

end CedarGen.Relational.PolicyGenErrorTest

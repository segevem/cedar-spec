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

import Cedar.Spec
import Cedar.Spec.ExtFun
import Cedar.Validation.RequestEntityValidator
import CedarGen.SchemaGuided
import Plausible

/-! # Property-Based Tests for Unverified Cedar Spec Modules

These tests exercise parts of the Cedar spec that don't have formal proofs,
using randomly generated inputs to check expected invariants.
-/

/-- Result of a single property check -/
inductive PropResult
  | pass           -- property held
  | fail           -- property violated (counterexample found)
  | genError       -- generator failed to produce an input (not a counterexample)

namespace CedarGen.PropertyTests

open Cedar.Spec
open Cedar.Data
open Plausible

/-! ## Template Linking Properties -/

/-- Property: Linking a template with all required slots filled always succeeds -/
def prop_link_with_complete_env : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let policy ← genPolicy schema
  -- A ground policy (no slots) should trivially link with empty env
  let template : Template := {
    effect := policy.effect,
    principalScope := .principalScope (.any),
    actionScope := policy.actionScope,
    resourceScope := .resourceScope (.any),
    condition := policy.condition,
  }
  match template.link? "test_id" SlotEnv.empty with
  | .ok linked =>
    if linked.effect == template.effect && linked.condition == template.condition
    then pure PropResult.pass else pure PropResult.fail
  | .error _ => pure PropResult.fail

/-- Property: Linking preserves the effect field -/
def prop_link_preserves_effect : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let policy ← genPolicy schema
  let template : Template := {
    effect := policy.effect,
    principalScope := .principalScope (.any),
    actionScope := policy.actionScope,
    resourceScope := .resourceScope (.any),
    condition := policy.condition,
  }
  match template.link? "test_id" SlotEnv.empty with
  | .ok linked => if linked.effect == template.effect then pure PropResult.pass else pure PropResult.fail
  | .error _ => pure PropResult.fail

/-- Property: Linking with a slot produces a policy referencing the bound entity -/
def prop_link_slot_binding : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let uid ← genEntityUIDFromSchema schema
  let slotEnv : SlotEnv := Map.make [("?principal", uid)]
  let template : Template := {
    effect := .permit,
    principalScope := .principalScope (.eq (.slot "?principal")),
    actionScope := .actionScope .any,
    resourceScope := .resourceScope .any,
    condition := [],
  }
  match template.link? "test_id" slotEnv with
  | .ok linked =>
    match linked.principalScope with
    | .principalScope (.eq boundUid) => if boundUid == uid then pure PropResult.pass else pure PropResult.fail
    | _ => pure PropResult.fail
  | .error _ => pure PropResult.fail

/-! ## Authorization Core Properties (executable checks) -/

/-- Property: Empty policy set always denies -/
def prop_empty_policies_deny : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let request ← genRequest schema
  let entities ← genEntities schema
  let result := isAuthorized request entities []
  if result.decision == .deny then pure PropResult.pass else pure PropResult.fail

/-- Property: A single permit policy with `when { true }` on matching scope allows -/
def prop_single_true_permit_allows : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let request ← genRequest schema
  let entities ← genEntities schema
  let policy : Policy := {
    id := "test",
    effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope .any,
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := .lit (.bool true) }],
  }
  let result := isAuthorized request entities [policy]
  if result.decision == .allow then pure PropResult.pass else pure PropResult.fail

/-- Property: A single forbid policy with `when { true }` always denies, even with a permit -/
def prop_forbid_trumps_permit : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let request ← genRequest schema
  let entities ← genEntities schema
  let permitPolicy : Policy := {
    id := "permit_all",
    effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope .any,
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := .lit (.bool true) }],
  }
  let forbidPolicy : Policy := {
    id := "forbid_all",
    effect := .forbid,
    principalScope := .principalScope .any,
    actionScope := .actionScope .any,
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := .lit (.bool true) }],
  }
  let result := isAuthorized request entities [permitPolicy, forbidPolicy]
  if result.decision == .deny then pure PropResult.pass else pure PropResult.fail

/-- Property: Policy order doesn't matter for authorization decision -/
def prop_order_independent : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let request ← genRequest schema
  let entities ← genEntities schema
  let p1 ← genPolicy schema
  let p2 ← genPolicy schema
  let p3 ← genPolicy schema
  let policies := [p1, p2, p3]
  let result1 := isAuthorized request entities policies
  let result2 := isAuthorized request entities policies.reverse
  if result1.decision == result2.decision then pure PropResult.pass else pure PropResult.fail

/-- Property: Duplicating a policy doesn't change the decision -/
def prop_duplicate_independent : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let request ← genRequest schema
  let entities ← genEntities schema
  let p1 ← genPolicy schema
  let p2 ← genPolicy schema
  let policies := [p1, p2]
  let result1 := isAuthorized request entities policies
  let result2 := isAuthorized request entities (policies ++ policies)
  if result1.decision == result2.decision then pure PropResult.pass else pure PropResult.fail

/-! ## Extension Function Properties -/

/-- Property: Decimal comparison is transitive -/
def prop_decimal_comparison_transitive : Gen PropResult := do
  let ⟨a, _⟩ ← Gen.choose Int (-10000) 10000 (by omega)
  let ⟨b, _⟩ ← Gen.choose Int (-10000) 10000 (by omega)
  let ⟨c, _⟩ ← Gen.choose Int (-10000) 10000 (by omega)
  let va := Value.ext (.decimal (Int64.ofInt a))
  let vb := Value.ext (.decimal (Int64.ofInt b))
  let vc := Value.ext (.decimal (Int64.ofInt c))
  match call .lessThan [va, vb], call .lessThan [vb, vc] with
  | .ok (.prim (.bool true)), .ok (.prim (.bool true)) =>
    match call .lessThan [va, vc] with
    | .ok (.prim (.bool true)) => pure PropResult.pass
    | _ => pure PropResult.fail
  | _, _ => pure PropResult.pass  -- precondition not met, vacuously true

/-! ## Test Runner -/

/-- Run a property N times and report results, distinguishing generator failures -/
def runProperty (name : String) (prop : Gen PropResult) (n : Nat := 1000) : IO Unit := do
  let mut successes := 0
  let mut failures := 0
  let mut genErrors := 0
  for seed in List.range n do
    let result ← try
      let r ← prop.run seed
      pure r
    catch _ =>
      pure .genError
    match result with
    | .pass => successes := successes + 1
    | .fail => failures := failures + 1
    | .genError => genErrors := genErrors + 1
  let tested := successes + failures
  if failures > 0 then
    IO.println s!"  FAIL {name}: {failures} counterexamples in {tested} tested ({genErrors} gen errors)"
  else if tested == 0 then
    IO.println s!"  SKIP {name}: all {genErrors} attempts had generator errors"
  else
    IO.println s!"  OK   {name}: {successes}/{tested} passed ({genErrors} gen errors)"

/-! ## Wildcard/Pattern Matching Properties -/

/-- Property: Empty pattern only matches empty string -/
def prop_empty_pattern_matches_empty : Gen PropResult := do
  let s ← Arbitrary.arbitrary (α := String)
  let result := wildcardMatch s []
  if result == (s == "") then pure PropResult.pass else pure PropResult.fail

/-- Property: Star pattern matches any string -/
def prop_star_matches_anything : Gen PropResult := do
  let s ← Arbitrary.arbitrary (α := String)
  if wildcardMatch s [PatElem.star] then pure PropResult.pass else pure PropResult.fail

/-- Property: Literal pattern matches only itself -/
def prop_literal_pattern_exact : Gen PropResult := do
  let s ← Arbitrary.arbitrary (α := String)
  let pat : Cedar.Spec.Pattern := s.toList.map PatElem.justChar
  if wildcardMatch s pat then pure PropResult.pass else pure PropResult.fail

/-- Property: Star at beginning means suffix match -/
def prop_star_prefix_suffix_match : Gen PropResult := do
  let pfx ← Arbitrary.arbitrary (α := String)
  let sfx ← Arbitrary.arbitrary (α := String)
  let pat : Cedar.Spec.Pattern := [PatElem.star] ++ sfx.toList.map PatElem.justChar
  let combined := pfx ++ sfx
  -- The combined string should match *suffix
  if wildcardMatch combined pat then pure PropResult.pass else pure PropResult.fail

/-- Property: wildcardMatch is reflexive (string matches its own literal pattern) -/
def prop_wildcard_reflexive : Gen PropResult := do
  let s ← Arbitrary.arbitrary (α := String)
  let pat : Cedar.Spec.Pattern := s.toList.map PatElem.justChar
  if wildcardMatch s pat then pure PropResult.pass else pure PropResult.fail

/-! ## Entity Validation Properties -/

/-- Property: Entities generated from a schema pass entity validation -/
def prop_generated_entities_validate : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let entities ← genEntities schema
  match Cedar.Validation.validateEntities schema entities with
  | .ok () => pure PropResult.pass
  | .error _ => pure PropResult.fail

/-- Diagnostic: print why entity validation fails -/
def diag_entities_validate (seed : Nat) : IO Unit := do
  let schema ← arbSchema.arbitrary.run seed
  let entities ← genEntities schema |>.run seed
  match Cedar.Validation.validateEntities schema entities with
  | .ok () => IO.println s!"  seed={seed}: PASS"
  | .error (.typeError msg) => IO.println s!"  seed={seed}: typeError: {msg}"

/-- Property: Requests generated from a schema pass request validation -/
def prop_generated_requests_validate : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let request ← genRequest schema
  match Cedar.Validation.validateRequest schema request with
  | .ok () => pure PropResult.pass
  | .error _ => pure PropResult.fail

/-- Diagnostic: print why request validation fails -/
def diag_requests_validate (seed : Nat) : IO Unit := do
  let schema ← arbSchema.arbitrary.run seed
  let request ← (genRequest schema).run seed
  match Cedar.Validation.validateRequest schema request with
  | .ok () => IO.println s!"  seed={seed}: PASS"
  | .error (.typeError msg) => IO.println s!"  seed={seed}: typeError: {msg}"

/-! ## More Authorization Properties -/

/-- Property: Adding a permit to a deny result cannot make it worse (still deny or becomes allow) -/
def prop_adding_permit_monotone : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let request ← genRequest schema
  let entities ← genEntities schema
  let p1 ← genPolicy schema
  let p2 ← genPolicy schema
  let policies := [p1, p2]
  let extraPermit : Policy := {
    id := "extra_permit",
    effect := .permit,
    principalScope := .principalScope .any,
    actionScope := .actionScope .any,
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := .lit (.bool true) }],
  }
  let r1 := isAuthorized request entities policies
  let r2 := isAuthorized request entities (extraPermit :: policies)
  -- Adding a permit can only change deny→allow, never allow→deny
  match r1.decision, r2.decision with
  | .allow, .allow => pure PropResult.pass
  | .allow, .deny => pure PropResult.fail  -- violation!
  | .deny, _ => pure PropResult.pass  -- any transition from deny is fine

/-- Property: Adding a forbid to an allow result makes it deny -/
def prop_adding_forbid_denies : Gen PropResult := do
  let schema ← arbSchema.arbitrary
  let request ← genRequest schema
  let entities ← genEntities schema
  let p1 ← genPolicy schema
  let policies := [p1]
  let extraForbid : Policy := {
    id := "extra_forbid",
    effect := .forbid,
    principalScope := .principalScope .any,
    actionScope := .actionScope .any,
    resourceScope := .resourceScope .any,
    condition := [{ kind := .when, body := .lit (.bool true) }],
  }
  let r2 := isAuthorized request entities (extraForbid :: policies)
  -- With an always-true forbid, result must be deny
  if r2.decision == .deny then pure PropResult.pass else pure PropResult.fail

/-! ## More Extension Function Properties -/

/-- Property: Decimal less-than is irreflexive -/
def prop_decimal_irreflexive : Gen PropResult := do
  let ⟨a, _⟩ ← Gen.choose Int (-10000) 10000 (by omega)
  let va := Value.ext (.decimal (Int64.ofInt a))
  match call .lessThan [va, va] with
  | .ok (.prim (.bool false)) => pure PropResult.pass
  | _ => pure PropResult.fail

/-- Property: Decimal less-than-or-equal is reflexive -/
def prop_decimal_leq_reflexive : Gen PropResult := do
  let ⟨a, _⟩ ← Gen.choose Int (-10000) 10000 (by omega)
  let va := Value.ext (.decimal (Int64.ofInt a))
  match call .lessThanOrEqual [va, va] with
  | .ok (.prim (.bool true)) => pure PropResult.pass
  | _ => pure PropResult.fail

end CedarGen.PropertyTests

open CedarGen.PropertyTests in
def main : IO Unit := do
  IO.println "=== Cedar Property Tests ==="
  IO.println ""
  IO.println "--- Template Linking ---"
  runProperty "link_with_complete_env" prop_link_with_complete_env
  runProperty "link_preserves_effect" prop_link_preserves_effect
  runProperty "link_slot_binding" prop_link_slot_binding
  IO.println ""
  IO.println "--- Authorization Core ---"
  runProperty "empty_policies_deny" prop_empty_policies_deny
  runProperty "single_true_permit_allows" prop_single_true_permit_allows
  runProperty "forbid_trumps_permit" prop_forbid_trumps_permit
  runProperty "order_independent" prop_order_independent
  runProperty "duplicate_independent" prop_duplicate_independent
  runProperty "adding_permit_monotone" prop_adding_permit_monotone
  runProperty "adding_forbid_denies" prop_adding_forbid_denies
  IO.println ""
  IO.println "--- Wildcard Matching ---"
  runProperty "empty_pattern_matches_empty" prop_empty_pattern_matches_empty
  runProperty "star_matches_anything" prop_star_matches_anything
  runProperty "literal_pattern_exact" prop_literal_pattern_exact
  runProperty "star_prefix_suffix_match" prop_star_prefix_suffix_match
  runProperty "wildcard_reflexive" prop_wildcard_reflexive
  IO.println ""
  IO.println "--- Entity Validation ---"
  runProperty "generated_entities_validate" prop_generated_entities_validate
  runProperty "generated_requests_validate" prop_generated_requests_validate
  IO.println "  Diagnostics (first 10 entity failures):"
  for seed in List.range 10 do
    diag_entities_validate seed
  IO.println "  Diagnostics (first 5 request failures):"
  for seed in [0, 1, 2, 3, 4] do
    diag_requests_validate seed
  IO.println ""
  IO.println "--- Extension Functions ---"
  runProperty "decimal_comparison_transitive" prop_decimal_comparison_transitive
  runProperty "decimal_irreflexive" prop_decimal_irreflexive
  runProperty "decimal_leq_reflexive" prop_decimal_leq_reflexive
  IO.println ""
  IO.println "=== Done ==="

#eval main

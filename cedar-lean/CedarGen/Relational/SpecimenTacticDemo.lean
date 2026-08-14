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

import CedarGen.Relational.RequestEntities
import CedarGen.Schema
import Specimen

/-! # `specimen` as a falsification tactic on **deep** Cedar goals

This is the foundation for wiring Specimen into __INTERNAL_ANALYZER__'s `--prove`
loop as an agent-usable diagnostic. It shows the `specimen` *tactic* (not just
the `specimen_test` command) running on an analyzer-style **deep** theorem —
one phrased over `Cedar.Spec.isAuthorized` — with the request/entities
generated *well-typed* by our `WellTypedRequestAndEntities` relation.

Why this matters for the prove loop:
* `specimen` is a **diagnostic**: it reports pass / counterexample and *leaves
  the goal open*. It never closes a goal, so it cannot fool the analyzer's
  independent `#print axioms` verifier or its statement guards — it only tells
  the agent whether to pursue the theorem or its negation.
* On a goal guarded by a well-typed precondition, `specimen` uses our relational
  generator to sample genuinely well-typed `(req, es)` — exactly the inputs the
  analyzer's `wellTyped` hypothesis restricts to.
-/

open CedarGen.Relational.ReqEnt
open CedarGen.Relational.Policy
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option specimen.richOutput false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ## Arbitrary / Enum / Shrinkable boilerplate -/

instance [Arbitrary α] [Arbitrary β] [LT α] [DecidableLT α] :
    Arbitrary (Map α β) where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
    let mut pairs : List (α × β) := []
    for _ in List.range len do
      pairs := (← Arbitrary.arbitrary, ← Arbitrary.arbitrary) :: pairs
    return Map.make pairs

instance [Enum α] [Enum β] [LT α] [DecidableLT α] :
    Enum (Map α β) where
  enum := do
    let pairs ← Enum.enum (α := List (α × β))
    return Map.make pairs

deriving instance Plausible.Arbitrary for Attr
deriving instance Plausible.Arbitrary for
  Var, ExtFun, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
  Qualified, CedarType

deriving instance Enum for
  Var, ExtFun, UInt64, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
  Qualified
deriving instance Enum for EntityType

deriving instance Shrinkable for Name, EntityUID
deriving instance Shrinkable for Map, Int64, Prim, Set
deriving instance Shrinkable for Ext.IPAddr.IPNetAddr
deriving instance Shrinkable for Ext.IPAddr.CIDR
deriving instance Shrinkable for Ext.IPAddr.IPNet, Ext.Datetime, Ext.Datetime.Duration
deriving instance Shrinkable for Duration
deriving instance Shrinkable for Ext
deriving instance Shrinkable for Value
deriving instance Shrinkable for Request
deriving instance Shrinkable for EntityData
deriving instance Shrinkable for Entities

/-! ## Schema `entity E { foo: Bool, bar: Bool }; action a appliesTo E, E` -/

def eTy : EntityType := { id := "E", path := [] }
def aAction : EntityUID := ⟨{ id := "Action", path := [] }, "a"⟩

def fooBarEnv : TypeEnv :=
  { ets := Map.make [
      (eTy,
       .standard { ancestors := Set.empty,
                   attrs := Map.make [("foo", .required (.bool .anyBool)),
                                      ("bar", .required (.bool .anyBool))],
                   tags := none }) ]
    acts := Map.make [
      (aAction,
       { appliesToPrincipal := Set.make [eTy], appliesToResource := Set.make [eTy],
         ancestors := Set.empty, context := Map.empty }) ]
    reqty :=
      { principal := eTy, action := aAction, resource := eTy, context := Map.empty } }

/-! ## Deep policy values (as __INTERNAL_ANALYZER__ would emit) -/

def eFooP : Expr := .getAttr (.var .principal) "foo"
def eBarR : Expr := .getAttr (.var .resource) "bar"

/-- `permit(...) when { principal.foo && resource.bar };` -/
def fooAndBarPolicy : Policy :=
  ⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
   [⟨.when, .and eFooP eBarR⟩]⟩
/-- `permit(...) when { resource.bar && principal.foo };` -/
def barAndFooPolicy : Policy :=
  ⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
   [⟨.when, .and eBarR eFooP⟩]⟩

def fooAndBarPolicies : Policies := [fooAndBarPolicy]
def barAndFooPolicies : Policies := [barAndFooPolicy]

/-! ## `specimen` tactic on the analyzer's `equivalent` goal (deep)

The exact shape __INTERNAL_ANALYZER__ emits for `--property equivalent`, but guarded
by a well-typed precondition and with `specimen` run as a diagnostic. It should
report "tests passed" (the two orderings agree on all well-typed inputs), then
we discharge with `sorry` (this file only demonstrates the tactic; the real loop
would replace it with a proof). -/

/-- tests passed -/
#guard_msgs (info, substring := true, drop warning) in
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
example :
    ∀ (req : Request) (es : Entities),
      WellTypedRequestAndEntities fooBarEnv req es →
      (isAuthorized req es fooAndBarPolicies)
        = (isAuthorized req es barAndFooPolicies) := by
  specimen (min := 1, max := 100, tests := 1000)
  sorry

/-! ## `specimen` catching a real inequivalence (deep)

`permit when { principal.foo }` vs `permit when { resource.bar }` reach
different decisions on some well-typed input — `specimen` finds a counterexample,
telling the agent to prove the *negation* instead. -/

def fooOnlyPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, eFooP⟩]⟩]
def barOnlyPolicies : Policies :=
  [⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any, [⟨.when, eBarR⟩]⟩]

-- DIAGNOSTIC: is the isAuthorized-level conclusion actually *evaluated* (not
-- vacuously "passed")? `fooOnly always denies` is FALSE (principal.foo = true ⇒
-- allow), so a non-vacuous checker must find a counterexample. Uses the
-- `specimen_test` COMMAND (which respects `tests`; the tactic caps at 100).
/-- error: Found counter-example! -/
#guard_msgs (error, drop info, substring := true, drop warning) in
set_option specimen.scoreType "Scoring.BoundedGradedScore" in
specimen_test (min := 2, max := 8, tests := 20000)
  (∀ (req : Request) (es : Entities),
    WellTypedRequestAndEntities fooBarEnv req es →
    (isAuthorized req es fooOnlyPolicies).decision = .deny)

/-! ## `specimen` **deep inside a proof**, via a conjectured `have` lemma

The realistic loop usage: mid-proof, the agent proposes an intermediate claim
with `have` and *tests it with `specimen`* before investing in a proof. This is
the robust way to use `specimen` deep in a proof — the `have` statement is a
clean, fully-elaborated closed proposition (unlike an arbitrary `simp`-reduced
subgoal, which can carry metavariables that `specimen` cannot delaborate).

Below, the agent has `intro`'d and now conjectures the crux equivalence as a
reusable lemma. `specimen` tests the conjecture over well-typed inputs; it
survives ("tests passed"), so the agent would go on to prove it (here `sorry`)
and close the goal with it. -/

set_option specimen.scoreType "Scoring.BoundedGradedScore" in
example :
    ∀ (req : Request) (es : Entities),
      WellTypedRequestAndEntities fooBarEnv req es →
      (isAuthorized req es fooAndBarPolicies)
        = (isAuthorized req es barAndFooPolicies) := by
  intro req es hwt
  specimen (tests := 10000)
  -- Conjecture the crux as a clean lemma and TEST it with specimen before proving:
  have key : ∀ (r : Request) (e : Entities),
      WellTypedRequestAndEntities fooBarEnv r e →
      evaluate (.and eFooP eBarR) r e = evaluate (.and eBarR eFooP) r e := by
    specimen (min := 1, max := 100, tests := 1000)
    sorry
  sorry

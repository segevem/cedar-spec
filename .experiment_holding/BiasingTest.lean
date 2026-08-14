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

import CedarGen.Relational.TypeOfLean
import CedarGen.Schema
import Specimen

/-! # Biasing: reweight the derived `HasType` generator toward underexplored ops

A weight modifier that (a) **boosts** the underexplored/target ops (arithmetic,
`getTag`/`getAttr`, set ops, extension calls) and (b) **rapidly suppresses
high-fan-out constructors as `size` shrinks**, using the `numRecCalls` argument
(constructor fan-out, baked in at derive time): `ite`→3, `and`/`or`/`binaryApp`→2,
`unaryApp`/`hasAttr`/`getAttr`→1, base ctors→0.

Intuition: near the leaves (small remaining `size`), spawning a wide control-flow
node wastes the budget on shallow structure. Suppressing branchy ctors there frees
`size` for the deeper operand chains where the rare ops actually form, while the
constant boost makes the generator prefer them when it does recurse.

Self-contained (imports the *spec*, not `TypeOfLeanTest`) so its own
`derive_mutual` under `favorRareOps` doesn't collide with the `favorHasTag`
instance. Tune `rareBoost` / `branchCap` below and rebuild. -/

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

/-! ## Arbitrary/Enum instances (mirror of `TypeOfLeanTest`) -/

instance [Arbitrary α] [Arbitrary β] [LT α] [DecidableLT α] :
    Arbitrary (Map α β) where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 4 (by omega)
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

instance : Plausible.Arbitrary Expr where
  arbitrary := return .lit (.bool true)

instance : Plausible.Arbitrary Key where
  arbitrary := return .attr ""

instance : Enum Expr where
  enum := pure (.lit (.bool true))

instance : Enum Key where
  enum := pure (.attr "")

deriving instance Enum for
  Var, ExtFun, UInt64, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
  Qualified

deriving instance Enum for EntityType

instance : Enum CedarType where
  enum := EnumeratorCombinators.oneOfWithDefault (pure .int) [
    pure .int,
    pure .string,
    do let b ← Enum.enum (α := BoolType); return .bool b,
    pure (.entity { id := "User", path := [] }),
    pure (.entity { id := "Group", path := [] }),
    pure (.entity { id := "Document", path := [] }),
    pure (.entity { id := "Action", path := [] }),
    do let x ← Enum.enum (α := ExtType); return .ext x
  ]

instance : Enum EntitySchemaEntry where
  enum := EnumeratorCombinators.oneOfWithDefault
    (pure (.standard { ancestors := Set.empty, attrs := Map.empty, tags := none })) [
    pure (.standard { ancestors := Set.empty, attrs := Map.empty, tags := none }),
    pure (.enum (Set.make ["a", "b"]))
  ]

instance : Enum ActionSchemaEntry where
  enum := pure { appliesToPrincipal := Set.empty, appliesToResource := Set.empty,
                 ancestors := Set.empty, context := Map.empty }

deriving instance DecidableEq for ActionSchemaEntry

/-! ## The biasing weight modifier -/

/-- Underexplored `HasType` constructors to boost (names are the last component of
each rule's constructor name — see `TypeOfLean.lean`). -/
private def rareOps : List String := [
  -- arithmetic
  "binaryAppAdd", "binaryAppSub", "binaryAppMul", "unaryAppNeg",
  -- getAttr / getTag (+ the hasTag guard, so getTag has a capability producer)
  "getAttrRecord", "getAttrEntity", "getTag", "hasTagAnyBool", "hasTagTt", "hasTagFf",
  -- set ops + set/record constructors
  "binaryAppContains", "binaryAppContainsAll", "binaryAppContainsAny", "unaryAppIsEmpty",
  "set", "record",
  -- extension calls + ext comparisons
  "call", "binaryAppLessDatetime", "binaryAppLessDuration",
  "binaryAppLessEqDatetime", "binaryAppLessEqDuration" ]

private def isRareOp : Lean.Name → Bool
  | .str _ n => rareOps.contains n
  | _        => false

-- === Tunables (edit + rebuild) ===
private def rareBoost : Nat := 6    -- multiplier applied to the rare/target ops
private def branchCap : Nat := 8    -- at size ≥ branchCap, no fan-out penalty

/-- Boost `rareOps`; suppress high fan-out ctors rapidly as `size` shrinks.

Below `branchCap`, a ctor with fan-out `f = numRecCalls ≥ 2` is divided by
`f ^ (branchCap - size)` — so at `size = branchCap` there's no penalty, and each
step down divides again by the fan-out. Higher fan-out (`ite`=3) decays faster than
lower (`and`/`or`=2). Rare ops are checked first and thus exempt from suppression
even when they themselves branch (e.g. `binaryAppAdd`), since their operands are
cheap (`litInt`) and we *want* them near the leaves. -/
def favorRareOps (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (size : Nat)
    (_numBase _numRec : Nat) (numRecCalls : Nat) : Nat :=
  if isRareOp ctorName then
    baseWeight * rareBoost + 1
  else if numRecCalls ≥ 2 && size < branchCap then
    max 1 (baseWeight / (numRecCalls ^ (branchCap - size)))
  else
    baseWeight

initialize registerWeightModifier `favorRareOps favorRareOps ``favorRareOps

set_option trace.Meta.synthInstance false
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightModifier "favorRareOps" in
set_option specimen.precomputeWeights true in
#time derive_mutual
  generator (fun env c ty => ∃ x cout, HasType x c env ty cout)

/-! ## Measurement env (mirror of `TypeOfLeanTest.testEnv`) -/

def biasEnv : TypeEnv :=
  { ets := Map.make [
      ({ id := "User", path := [] },
       .standard {
         ancestors := Set.make [{ id := "Group", path := [] }],
         attrs := Map.make [
           ("name", .required .string),
           ("age", .required .int),
           ("active", .required (.bool .anyBool)),
           ("email", .optional .string),
           ("manager", .optional (.entity { id := "User", path := [] }))],
         tags := .some .string }),
      ({ id := "Group", path := [] },
       .standard {
         ancestors := Set.empty,
         attrs := Map.make [
           ("name", .required .string),
           ("public", .required (.bool .anyBool))],
         tags := none }),
      ({ id := "Document", path := [] },
       .standard {
         ancestors := Set.empty,
         attrs := Map.make [
           ("owner", .required (.entity { id := "User", path := [] })),
           ("title", .required .string),
           ("score", .optional .int)],
         tags := .some .int })]
    acts := Map.make [
      (⟨{ id := "Action", path := [] }, "view"⟩,
       { appliesToPrincipal := Set.empty, appliesToResource := Set.empty,
         ancestors := Set.empty, context := Map.empty }),
      (⟨{ id := "Action", path := [] }, "edit"⟩,
       { appliesToPrincipal := Set.empty, appliesToResource := Set.empty,
         ancestors := Set.make [⟨{ id := "Action", path := [] }, "view"⟩],
         context := Map.empty })]
    reqty :=
      { principal := { id := "User", path := [] }
        action := ⟨{ id := "Action", path := [] }, "edit"⟩
        resource := { id := "Document", path := [] }
        context := Map.make [
          ("ip", .required .string),
          ("mfa", .required (.bool .anyBool)),
          ("level", .optional .int)] } }

/-! ## Measurement harness -/

private def binOpName : BinaryOp → String
  | .eq => "eq" | .mem => "mem" | .less => "less" | .lessEq => "lessEq"
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .contains => "contains" | .containsAll => "containsAll" | .containsAny => "containsAny"
  | .hasTag => "hasTag" | .getTag => "getTag"

private def unOpName : UnaryOp → String
  | .not => "not" | .neg => "neg" | .like _ => "like" | .isEmpty => "isEmpty" | .is _ => "is"

private partial def tally (m : Std.HashMap String Nat) (e : Expr) : Std.HashMap String Nat :=
  match e with
  | .lit _ | .var _   => m
  | .ite a b c        => tally (tally (tally m a) b) c
  | .and a b | .or a b => tally (tally m a) b
  | .unaryApp op a    => let k := s!"unOp:{unOpName op}"; tally (m.insert k (m.getD k 0 + 1)) a
  | .binaryApp op a b => let k := s!"binOp:{binOpName op}"; tally (tally (m.insert k (m.getD k 0 + 1)) a) b
  | .hasAttr a _ | .getAttr a _ => tally m a
  | .set xs           => xs.foldl tally m
  | .record axs       => axs.foldl (fun acc (_, x) => tally acc x) m
  | .call _ xs        => let k := "call"; xs.foldl tally (m.insert k (m.getD k 0 + 1))

private partial def depth : Expr → Nat
  | .lit _ | .var _ => 1
  | .ite a b c => 1 + max (depth a) (max (depth b) (depth c))
  | .and a b | .or a b | .binaryApp _ a b => 1 + max (depth a) (depth b)
  | .unaryApp _ a | .hasAttr a _ | .getAttr a _ => 1 + depth a
  | .set xs => 1 + xs.foldl (fun m x => max m (depth x)) 0
  | .record axs => 1 + axs.foldl (fun m (_, x) => max m (depth x)) 0
  | .call _ xs => 1 + xs.foldl (fun m x => max m (depth x)) 0

private partial def nodes : Expr → Nat
  | .lit _ | .var _ => 1
  | .ite a b c => 1 + nodes a + nodes b + nodes c
  | .and a b | .or a b | .binaryApp _ a b => 1 + nodes a + nodes b
  | .unaryApp _ a | .hasAttr a _ | .getAttr a _ => 1 + nodes a
  | .set xs => 1 + xs.foldl (fun s x => s + nodes x) 0
  | .record axs => 1 + axs.foldl (fun s (_, x) => s + nodes x) 0
  | .call _ xs => 1 + xs.foldl (fun s x => s + nodes x) 0

/-- Generate `n` well-typed `bool` policies at `size` under empty caps (the natural
policy target) and report the op distribution + depth — no forcing, just the biased
generator's own output. Compare against `TypeOfLeanTest.propertyTest` to see the shift.

Bounded retries (`attempts`) turn an infeasible/rare seed into a fast `gen-fail`
instead of a hang. Each generation is wall-clock timed: any success OR failure that
takes longer than `slowMs` is logged (with `repr`) so you can see *which* exprs (or
which infeasible boosted rules, when it's a slow failure) are the culprits. -/
def biasMeasure (n size : Nat) (env : TypeEnv := biasEnv) (ty : CedarType := .bool .anyBool)
    (attempts : Nat := 100) (slowMs : Float := 200.0) (maxSlowLogs : Nat := 8) : IO Unit := do
  IO.println s!"\n=== Biased generation (n={n}, size={size}, ty={repr ty}, attempts={attempts}) ==="
  let mut gen := 0
  let mut genFail := 0
  let mut depthSum := 0
  let mut slow := 0
  let mut slowLogged := 0
  let mut maxMs : Float := 0.0
  let mut ops : Std.HashMap String Nat := {}
  for _ in List.range n do
    let t0 ← IO.monoNanosNow
    let res ← (do
      try
        let (x, _cout) ← Gen.runUntil (attempts := .some attempts)
          (ArbitrarySizedSuchThat.arbitrarySizedST (fun (e, cout) => HasType e [] env ty cout) size) 5
        pure (some x)
      catch _ => pure none)
    let ms := ((← IO.monoNanosNow) - t0).toFloat / 1_000_000.0
    if ms > maxMs then maxMs := ms
    match res with
    | some x =>
      gen := gen + 1
      ops := tally ops x
      depthSum := depthSum + depth x
      if ms > slowMs then
        slow := slow + 1
        if slowLogged < maxSlowLogs then
          slowLogged := slowLogged + 1
          IO.println s!"  SLOW-OK ({ms}ms) depth={depth x} nodes={nodes x}: {repr x}"
    | none =>
      genFail := genFail + 1
      if ms > slowMs then
        slow := slow + 1
        if slowLogged < maxSlowLogs then
          slowLogged := slowLogged + 1
          IO.println s!"  SLOW-FAIL ({ms}ms): exhausted {attempts} attempts (rule likely infeasible for this target/schema)"
  let avgDepth := if gen > 0 then depthSum.toFloat / gen.toFloat else 0.0
  IO.println s!"  generated={gen}/{n} gen-fail={genFail} slow(>{slowMs}ms)={slow} maxMs={maxMs} avgDepth={avgDepth}"
  IO.print "  ops:"
  for (op, cnt) in ops.toArray.qsort (fun a b => a.snd > b.snd) do IO.print s!" {op}={cnt}"
  IO.println ""

#eval biasMeasure 0 0

import CedarGen.Relational.TypeOfLean
import CedarGen.Schema
import Specimen

/-!
# Biasing test — RECONSTRUCTED

⚠️ This file's source was lost and reconstructed. FAITHFUL parts (recovered verbatim from
`LubTrace.lean`, which had copied them from here): the imports/opens/options, the Arbitrary/Enum
instance block, the `favorRareOps` weight modifier, and the `HasType` `derive_mutual`.
NOT recovered: the original `biasEnv : TypeEnv` and the property tests below the derive — a
partially-recovered `biasEnv` skeleton is preserved (commented) at the bottom; restore from your
own copy if you have one.

Self-contained (imports the *spec*, not `TypeOfLeanTest`) so its `favorRareOps` weight modifier
doesn't collide with `favorHasTag`. Tune `rareBoost` / `branchCap` below and rebuild.
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

-- TODO(reconstruct): the original `biasEnv : TypeEnv` and the property tests that followed the
-- derive were NOT fully recovered. Below is the partial `biasEnv` skeleton recovered from the
-- session transcript (commented out because it is incomplete and would not compile). Restore the
-- full definition + property tests from your own copy.
/-
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
         -- ... (remainder of biasEnv not recovered) ...
       })],
    -- acts := ...,
    -- reqty := ...,
  }
-/

-- PPALL_DUMP_PROBE (temporary diagnostic)
open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let targets := env.constants.fold (fun acc n _ =>
    let s := n.toString
    if s.endsWith "_unsafe_rec" && (s.splitOn "Lean_Lub").length ≥ 2 then acc.push n else acc) (#[] : Array Lean.Name)
  Command.liftTermElabM do
    withOptions (fun o => o.setBool `pp.all true) do
      for n in targets do
        match env.find? n with
        | some (.defnInfo di) => logInfo m!"◆ {n}\n{← ppExpr di.value}"
        | _ => pure ()

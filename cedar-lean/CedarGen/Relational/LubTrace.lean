import CedarGen.Relational.TypeOfLean
import CedarGen.Schema
import Specimen


/-!
# Isolated `Lub` clique — encoding trace probe (throwaway diagnostic)

Reproduces ONLY the `Lub`/`LubRecord`/`LubQualified` mutual generator clique that dominates
kernel typechecking in the full `HasType` `derive_mutual`, without the 155s of HasType.

The all-outputs 3-tuple mode below is the cleanest probe: in the full profile it had ZERO
`DecOpt` instance holes, so its cost is purely elaborator (matcher/`brecOn` construction) +
kernel (typechecking the `brecOn`-over-`CedarType` encoding) — no typeclass-synthesis confounder.

What to read from the trace:
  * `trace.Elab.definition.structural` — which PARAMETER the mutual clique recurses on
    (want: `fuel`; if it's a `CedarType` arg, the `brecOn` motive is CedarType-laden → expensive).
  * `trace.Meta.mkBRecOn`            — the packed mutual `below`/`brecOn` term being built.
  * `⏱ codegen+pp split` + `⏱ derive_mutual phases` — our-code vs elaborator time.

Differential: prepend `set_option debug.skipKernelTC true in` to the derive to confirm how much
of the time is kernel typechecking (UNSAFE — measurement only, never ship).
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


/-! ## Biasing weight modifier (verbatim from BiasingTest.lean — needed for exact options) -/

private def rareOps : List String := [
  "binaryAppAdd", "binaryAppSub", "binaryAppMul", "unaryAppNeg",
  "getAttrRecord", "getAttrEntity", "getTag", "hasTagAnyBool", "hasTagTt", "hasTagFf",
  "binaryAppContains", "binaryAppContainsAll", "binaryAppContainsAny", "unaryAppIsEmpty",
  "set", "record",
  "call", "binaryAppLessDatetime", "binaryAppLessDuration",
  "binaryAppLessEqDatetime", "binaryAppLessEqDuration" ]

private def isRareOp : Lean.Name → Bool
  | .str _ n => rareOps.contains n
  | _        => false

private def rareBoost : Nat := 6
private def branchCap : Nat := 8

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

/-! ## Traced derivation of the Lub clique — EXACT mode + EXACT options as BiasingTest.
    Mode: `∃ a b c, Lub a b c` = all OUTPUTS = 3-tuple `Gen (CedarType × CedarType × CedarType)`
    (matches the full run's 30.9s block). Options mirror BiasingTest's derive_mutual exactly. -/

set_option trace.profiler true in
set_option trace.profiler.threshold 20 in
set_option trace.profiler.useHeartbeats false in
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightModifier "favorRareOps" in
set_option specimen.precomputeWeights true in
set_option specimen.reportParallelCeiling true in
#time derive_mutual
  generator (∃ a b c, Lub a b c)

/-! ## By-parts mode isolation: `(a b : CedarType) → Gen CedarType` (a,b INPUTS, c OUTPUT).
    This is the full run's 50.8s block — never isolated before. `∃`=output, lambda=input.
    Fast here ⇒ context-dependent like the all-outputs mode; ~50s here ⇒ the term is the cost. -/
set_option trace.profiler true in
set_option trace.profiler.threshold 20 in
set_option trace.profiler.useHeartbeats false in
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightModifier "favorRareOps" in
set_option specimen.precomputeWeights true in
set_option specimen.reportParallelCeiling true in
#time derive_mutual
  generator (fun a b => ∃ c, Lub a b c)

/-! ## Dump the resolved `_unsafe_rec` bodies (pp.all) to inspect what the `_` holes became. -/
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

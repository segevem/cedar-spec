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

import CedarGen.Relational.Schema
import CedarGen.Relational.TypeOfLean
import CedarGen.Relational.TypeOfLeanBase
import CedarGen.Relational.Variants.BudgetAware
import CedarGen.Relational.Variants.BudgetAwarePlain
import CedarGen.Relational.Variants.Steep
import CedarGen.Relational.Variants.SteepTags
import CedarGen.Relational.Variants.TypeOfCheck
import Specimen

/-! # Test: derive generators for well-formed schemas and compose with HasType

Pipeline:
1. Generate a well-formed TypeEnv via `WfTypeEnv`
2. Generate well-typed boolean expressions against that env via `HasType`
-/

open CedarGen.Relational.Schema
open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Variant.TypeOfCheck
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.multiOutput true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ## Arbitrary/Enum instances for base types -/

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
-- deriving instance Plausible.Arbitrary for
--   Var, ExtFun, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
--   Qualified, CedarType

-- instance : Plausible.Arbitrary Expr where
--   arbitrary := return .lit (.bool true)

-- instance : Plausible.Arbitrary Key where
--   arbitrary := return .attr ""

-- instance : Enum Expr where
--   enum := pure (.lit (.bool true))

-- instance : Enum Key where
--   enum := pure (.attr "")

-- deriving instance Enum for
--   Var, ExtFun, UInt64, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
--   Qualified

-- deriving instance Enum for EntityType

-- instance : Enum CedarType where
--   enum := EnumeratorCombinators.oneOfWithDefault (pure .int) [
--     pure .int,
--     pure .string,
--     do let b ← Enum.enum (α := BoolType); return .bool b,
--     pure (.entity { id := "User", path := [] }),
--     pure (.entity { id := "Group", path := [] }),
--     pure (.entity { id := "Document", path := [] }),
--     do let x ← Enum.enum (α := ExtType); return .ext x
--   ]

-- instance : Enum EntitySchemaEntry where
--   enum := EnumeratorCombinators.oneOfWithDefault
--     (pure (.standard { ancestors := Set.empty, attrs := Map.empty, tags := none })) [
--     pure (.standard { ancestors := Set.empty, attrs := Map.empty, tags := none }),
--     pure (.enum (Set.make ["a", "b"]))
--   ]

-- instance : Enum ActionSchemaEntry where
--   enum := pure { appliesToPrincipal := Set.empty, appliesToResource := Set.empty,
--                  ancestors := Set.empty, context := Map.empty }

-- deriving instance DecidableEq for ActionSchemaEntry

-- instance : Enum StandardSchemaEntry where
--   enum := pure { ancestors := Set.empty, attrs := Map.empty, tags := none }

-- instance : Enum RequestType where
--   enum := pure { principal := { id := "User", path := [] },
--                  action := ⟨{ id := "Action", path := [] }, "view"⟩,
--                  resource := { id := "Document", path := [] },
--                  context := Map.empty }

/-! ## Derive generators from schema relations -/

/-- Bias the derived schema generator toward denser hierarchies by boosting the
    `PickClosedAncestors.pick` constructor (add a direct parent + its closure)
    over `.skip`. Mild multiplier: `pick` is feasible whenever `built` is
    non-empty, so this steers without forcing infeasible picks. Must be defined
    at root namespace so the same-file derive resolves it via the `env.contains`
    fallback. -/
def favorAncestors (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  match ctorName with
  -- Mild boost so ancestor lists aren't mostly empty. Kept flat and modest: edge
  -- density already scales with the schema `size` parameter (measured 869→1255→1734
  -- edges at size 12→24→40), and large multipliers on this fuel-competing recursive
  -- rule cause backtracking blowup for little gain.
  | .str (.str _ "PickClosedAncestors") "pick" => baseWeight * 3 + 2
  -- Mild boost toward more *standard* entities (enums can't be ancestors), giving
  -- the hierarchy more nodes to connect.
  | .str (.str _ "WfEntitiesGo") "standard"    => baseWeight * 2 + 1
  | _                                          => baseWeight

/-- MANUAL uniform generator for `SelectRemove` (used by `WfActionSchema` to draw distinct
    action eids from `actionEidPool`). The DERIVED `here/there` generator is geometric
    (head-biased); this picks a UNIFORM index and returns `(xs[i], xs.eraseIdx i)` — same
    `Gen.choose`-style uniform pick used by the other manual list generators, and constructive
    (no generate-and-reject). `xs` (the pool) is unified from the goal predicate. -/
instance {α} [Inhabited α] {xs : List α} :
    ArbitrarySizedSuchThat (α × List α) (fun p => SelectRemove xs p.1 p.2) where
  arbitrarySizedST _ := do
    if 0 < xs.length then
      let ⟨i, _⟩ ← Gen.choose Nat 0 (xs.length - 1) (by omega)
      pure (xs[i]!, xs.eraseIdx i)
    else
      MonadExcept.throw Plausible.Gen.genericFailure

set_option trace.Meta.synthInstance false
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.textOutput 3 in
set_option specimen.precomputeWeights true in
set_option specimen.weightModifier "favorAncestors" in
#time derive_mutual
  generator (∃ env, WfTypeEnv env)

/-! ## Derive generators from HasType (reuses TypeOfLeanTest's derivation) -/

-- NotDescendentOf enumerator (needed by HasType)
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.precomputeWeights true in
#time derive_mutual
  enumerator (fun a b => ∃ c d, NotDescendentOf a b c d)

/-! ## Post-processing: canonicalize generated TypeEnv -/

private def canonicalizeRecordType (rty : RecordType) : RecordType :=
  Map.make rty.toList

private partial def canonicalizeCedarType : CedarType → CedarType
  | .record rty => .record (Map.make (rty.toList.map fun (a, qt) =>
      (a, qt.map canonicalizeCedarType)))
  | .set ty => .set (canonicalizeCedarType ty)
  | ty => ty

private def canonicalizeAttrs (rty : RecordType) : RecordType :=
  Map.make (rty.toList.map fun (a, qt) => (a, qt.map canonicalizeCedarType))

private def canonicalizeEntityEntry : EntitySchemaEntry → EntitySchemaEntry
  | .standard entry => .standard {
      ancestors := Set.make entry.ancestors.toList,
      attrs := canonicalizeAttrs entry.attrs,
      tags := entry.tags.map canonicalizeCedarType }
  | .enum eids => .enum (Set.make eids.toList)

private def canonicalizeActionEntry (entry : ActionSchemaEntry) : ActionSchemaEntry :=
  { appliesToPrincipal := Set.make entry.appliesToPrincipal.toList,
    appliesToResource := Set.make entry.appliesToResource.toList,
    ancestors := Set.make entry.ancestors.toList,
    context := canonicalizeAttrs entry.context }

def canonicalizeEnv (env : TypeEnv) : TypeEnv :=
  { ets := Map.make (env.ets.toList.map fun (et, entry) => (et, canonicalizeEntityEntry entry)),
    acts := Map.make (env.acts.toList.map fun (uid, entry) => (uid, canonicalizeActionEntry entry)),
    reqty := { env.reqty with context := canonicalizeAttrs env.reqty.context } }

/-! ## Compose: generate env then generate expressions -/

def generateSchemaAndExpr (size : Nat) : IO (Option (TypeEnv × Expr × CedarType)) := do
  -- Step 1: generate a well-formed TypeEnv
  let rawEnv ← try
    Gen.runUntil (attempts := .none)
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun env => WfTypeEnv env) size)
      size
  catch _ =>
    -- let _ ← IO.rand 0 1000
    return none

  -- Step 1.5: canonicalize (sort/dedup maps and sets)
  let env := canonicalizeEnv rawEnv

  -- Step 2: generate a well-typed boolean expression against that env
  let caps : Capabilities := []
  let ty := CedarType.bool .anyBool
  let result ← try
    let (x, _cout) ← Gen.runUntil (attempts := .some 1)
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (e, cout) => HasType e caps env ty cout) size)
      size
    pure (some (env, x, ty))
  catch _ =>
    -- let _ ← IO.rand 0 1000
    return none
  return result

/-- Deterministically generate one canonicalized well-formed `TypeEnv` from
    `seed` using `schemaSize` fuel. The term generation is left to the caller
    (the FFI), which dispatches on the requested Specimen strategy. -/
def generateSchemaOnly (seed schemaSize : Nat) : IO (Option TypeEnv) := do
  let rawEnv ← try
    Gen.runUntilWith seed (attempts := .some 100)
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun env => WfTypeEnv env) schemaSize)
      schemaSize
  catch _ =>
    return none
  return some (canonicalizeEnv rawEnv)

def generateSchemaWithExprs (seed schemaSize termSize count : Nat) : IO (Option (TypeEnv × List Expr)) := do
  let rawEnv ← try
    Gen.runUntilWith seed (attempts := .some 100)
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun env => WfTypeEnv env) schemaSize)
      schemaSize
  catch _ =>
    return none
  let env := canonicalizeEnv rawEnv
  let caps : Capabilities := []
  let ty := CedarType.bool .anyBool
  -- Seed the expression generation with seed+1 so it differs from env gen
  let exprs ← generateExprs env caps ty termSize count (some (seed + 1))
  return some (env, exprs)

/-! ## Expression stats (same as TypeOfLeanTest) -/

private def exprCtorId : Expr → UInt8
  | .lit _          => 0
  | .var _          => 1
  | .ite ..         => 2
  | .and ..         => 3
  | .or ..          => 4
  | .unaryApp ..    => 5
  | .binaryApp ..   => 6
  | .hasAttr ..     => 7
  | .getAttr ..     => 8
  | .set ..         => 9
  | .record ..      => 10
  | .call ..        => 11

private def ctorName : UInt8 → String
  | 0 => "lit" | 1 => "var" | 2 => "ite" | 3 => "and" | 4 => "or"
  | 5 => "unaryApp" | 6 => "binaryApp" | 7 => "hasAttr" | 8 => "getAttr"
  | 9 => "set" | 10 => "record" | 11 => "call" | _ => "?"

private def exprDepth (e : Expr) : Nat :=
  match e with
  | .lit _ | .var _ => 1
  | .ite a b c => 1 + max (exprDepth a) (max (exprDepth b) (exprDepth c))
  | .and a b | .or a b | .binaryApp _ a b => 1 + max (exprDepth a) (exprDepth b)
  | .unaryApp _ a | .hasAttr a _ | .getAttr a _ => 1 + exprDepth a
  | .set xs => 1 + exprListMaxDepth xs
  | .record axs => 1 + exprPairListMaxDepth axs
  | .call _ xs => 1 + exprListMaxDepth xs
where
  exprListMaxDepth : List Expr → Nat
    | [] => 0
    | x :: xs => max (exprDepth x) (exprListMaxDepth xs)
  exprPairListMaxDepth : List (Attr × Expr) → Nat
    | [] => 0
    | (_, x) :: xs => max (exprDepth x) (exprPairListMaxDepth xs)

private def exprNodeCount (e : Expr) : Nat :=
  match e with
  | .lit _ | .var _ => 1
  | .ite a b c => 1 + exprNodeCount a + exprNodeCount b + exprNodeCount c
  | .and a b | .or a b | .binaryApp _ a b => 1 + exprNodeCount a + exprNodeCount b
  | .unaryApp _ a | .hasAttr a _ | .getAttr a _ => 1 + exprNodeCount a
  | .set xs => 1 + exprListSum xs
  | .record axs => 1 + exprPairListSum axs
  | .call _ xs => 1 + exprListSum xs
where
  exprListSum : List Expr → Nat
    | [] => 0
    | x :: xs => exprNodeCount x + exprListSum xs
  exprPairListSum : List (Attr × Expr) → Nat
    | [] => 0
    | (_, x) :: xs => exprNodeCount x + exprPairListSum xs

private def incAt (arr : Array Nat) (i : UInt8) : Array Nat :=
  let idx := i.toNat
  if h : idx < arr.size then arr.set idx (arr[idx] + 1) else arr

private def countCtors (arr : Array Nat) (e : Expr) : Array Nat :=
  let arr := incAt arr (exprCtorId e)
  match e with
  | .lit _ | .var _ => arr
  | .ite a b c => countCtors (countCtors (countCtors arr a) b) c
  | .and a b | .or a b | .binaryApp _ a b => countCtors (countCtors arr a) b
  | .unaryApp _ a | .hasAttr a _ | .getAttr a _ => countCtors arr a
  | .set xs => countCtorsList arr xs
  | .record axs => countCtorsPairList arr axs
  | .call _ xs => countCtorsList arr xs
where
  countCtorsList (arr : Array Nat) : List Expr → Array Nat
    | [] => arr
    | x :: xs => countCtorsList (countCtors arr x) xs
  countCtorsPairList (arr : Array Nat) : List (Attr × Expr) → Array Nat
    | [] => arr
    | (_, x) :: xs => countCtorsPairList (countCtors arr x) xs

/-! ## Operator breakdown stats (per unaryApp / binaryApp operator) -/

private def unaryOpId : UnaryOp → UInt8
  | .not => 0 | .neg => 1 | .isEmpty => 2 | .like _ => 3 | .is _ => 4

private def unaryOpName : UInt8 → String
  | 0 => "not" | 1 => "neg" | 2 => "isEmpty" | 3 => "like" | 4 => "is" | _ => "?"

private def binaryOpId : BinaryOp → UInt8
  | .eq => 0 | .mem => 1 | .hasTag => 2 | .getTag => 3 | .less => 4 | .lessEq => 5
  | .add => 6 | .sub => 7 | .mul => 8 | .contains => 9 | .containsAll => 10 | .containsAny => 11

private def binaryOpName : UInt8 → String
  | 0 => "eq" | 1 => "mem" | 2 => "hasTag" | 3 => "getTag" | 4 => "less" | 5 => "lessEq"
  | 6 => "add" | 7 => "sub" | 8 => "mul" | 9 => "contains" | 10 => "containsAll"
  | 11 => "containsAny" | _ => "?"

/-- Walk an expression accumulating per-operator counts: `uArr` indexed by
    `unaryOpId` (unaryApp operators), `bArr` by `binaryOpId` (binaryApp operators). -/
private def countOps (uArr bArr : Array Nat) (e : Expr) : Array Nat × Array Nat :=
  match e with
  | .lit _ | .var _ => (uArr, bArr)
  | .ite a b c =>
    let (u, b') := countOps uArr bArr a
    let (u, b') := countOps u b' b
    countOps u b' c
  | .and a b | .or a b =>
    let (u, b') := countOps uArr bArr a
    countOps u b' b
  | .binaryApp op a b =>
    let bArr := incAt bArr (binaryOpId op)
    let (u, b') := countOps uArr bArr a
    countOps u b' b
  | .unaryApp op a =>
    let uArr := incAt uArr (unaryOpId op)
    countOps uArr bArr a
  | .hasAttr a _ | .getAttr a _ => countOps uArr bArr a
  | .set xs => countOpsList uArr bArr xs
  | .record axs => countOpsPairList uArr bArr axs
  | .call _ xs => countOpsList uArr bArr xs
where
  countOpsList (uArr bArr : Array Nat) : List Expr → Array Nat × Array Nat
    | [] => (uArr, bArr)
    | x :: xs => let (u, b) := countOps uArr bArr x; countOpsList u b xs
  countOpsPairList (uArr bArr : Array Nat) : List (Attr × Expr) → Array Nat × Array Nat
    | [] => (uArr, bArr)
    | (_, x) :: xs => let (u, b) := countOps uArr bArr x; countOpsPairList u b xs

/-! ## Extension-function breakdown (per `ExtFun` used in a `.call`) -/

private def extFunId : ExtFun → UInt8
  | .decimal => 0 | .lessThan => 1 | .lessThanOrEqual => 2 | .greaterThan => 3 | .greaterThanOrEqual => 4
  | .ip => 5 | .isIpv4 => 6 | .isIpv6 => 7 | .isLoopback => 8 | .isMulticast => 9 | .isInRange => 10
  | .datetime => 11 | .duration => 12 | .offset => 13 | .durationSince => 14 | .toDate => 15 | .toTime => 16
  | .toMilliseconds => 17 | .toSeconds => 18 | .toMinutes => 19 | .toHours => 20 | .toDays => 21

private def extFunName : UInt8 → String
  | 0 => "decimal" | 1 => "lessThan" | 2 => "lessThanOrEqual" | 3 => "greaterThan" | 4 => "greaterThanOrEqual"
  | 5 => "ip" | 6 => "isIpv4" | 7 => "isIpv6" | 8 => "isLoopback" | 9 => "isMulticast" | 10 => "isInRange"
  | 11 => "datetime" | 12 => "duration" | 13 => "offset" | 14 => "durationSince" | 15 => "toDate" | 16 => "toTime"
  | 17 => "toMilliseconds" | 18 => "toSeconds" | 19 => "toMinutes" | 20 => "toHours" | 21 => "toDays" | _ => "?"

/-- Walk an expression accumulating per-extension-function counts (indexed by
    `extFunId`), covering every `.call xfn …` node. These are the rarest
    generated expressions, so track each one individually. -/
private def countExtFuns (arr : Array Nat) (e : Expr) : Array Nat :=
  match e with
  | .lit _ | .var _ => arr
  | .ite a b c => countExtFuns (countExtFuns (countExtFuns arr a) b) c
  | .and a b | .or a b | .binaryApp _ a b => countExtFuns (countExtFuns arr a) b
  | .unaryApp _ a | .hasAttr a _ | .getAttr a _ => countExtFuns arr a
  | .set xs => countExtFunsList arr xs
  | .record axs => countExtFunsPairList arr axs
  | .call xfn xs => countExtFunsList (incAt arr (extFunId xfn)) xs
where
  countExtFunsList (arr : Array Nat) : List Expr → Array Nat
    | [] => arr
    | x :: xs => countExtFunsList (countExtFuns arr x) xs
  countExtFunsPairList (arr : Array Nat) : List (Attr × Expr) → Array Nat
    | [] => arr
    | (_, x) :: xs => countExtFunsPairList (countExtFuns arr x) xs

/-! ## Property test: generated schemas produce typeable expressions -/

def schemaPropertyTest (n : Nat) (size : Nat) : IO Unit := do
  let mut schemaSuccess : Nat := 0
  let mut exprSuccess : Nat := 0
  let mut schemaFail : Nat := 0
  let mut exprFail : Nat := 0
  let mut depths : Array Nat := #[]
  let mut nodeCounts : Array Nat := #[]
  let mut ctorCounts : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0]
  let mut unaryCounts : Array Nat := #[0,0,0,0,0]                 -- per unaryApp operator
  let mut binaryCounts : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0]  -- per binaryApp operator
  let mut extFunCounts : Array Nat := (List.replicate 22 0).toArray  -- per extension function
  let mut entityTypeCounts : Std.HashMap Nat Nat := {}  -- num entity types per schema
  let mut numAttrs : Array Nat := #[]  -- total attrs per schema
  for _ in List.range n do
    match ← generateSchemaAndExpr size with
    | some (env, expr, ty) =>
      schemaSuccess := schemaSuccess + 1
      -- Schema stats
      let nEts := env.ets.size
      entityTypeCounts := entityTypeCounts.insert nEts (entityTypeCounts.getD nEts 0 + 1)
      let totalAttrs := env.ets.toList.foldl (fun acc (_, entry) =>
        acc + match entry with | .standard e => e.attrs.size | .enum _ => 0) 0
      numAttrs := numAttrs.push totalAttrs
      -- Expr stats
      depths := depths.push (exprDepth expr)
      nodeCounts := nodeCounts.push (exprNodeCount expr)
      ctorCounts := countCtors ctorCounts expr
      let (u', b') := countOps unaryCounts binaryCounts expr
      unaryCounts := u'
      binaryCounts := b'
      extFunCounts := countExtFuns extFunCounts expr
      -- Verify: does the functional typechecker agree?
      let funcResult := Cedar.Validation.typeOf expr [] env
      match funcResult with
      | .ok (funcTx, _) =>
        if funcTx.typeOf == ty then
          exprSuccess := exprSuccess + 1
        else
          exprFail := exprFail + 1
          if exprFail ≤ 3 then
            IO.println s!"TYPE MISMATCH: expected={repr ty} got={repr funcTx.typeOf}"
            IO.println s!"  env.ets keys: {env.ets.keys.toList}"
            IO.println s!"  expr: {repr expr}"
      | .error e =>
        exprFail := exprFail + 1
        if exprFail ≤ 3 then
          IO.println s!"TYPE ERROR: {repr e}"
          IO.println s!"  expr: {repr expr}"
    | none =>
      schemaFail := schemaFail + 1
  IO.println s!"\n=== Schema+Expr Generation ({n} attempts, size={size}) ==="
  IO.println s!"  Schema generated: {schemaSuccess} / {n}"
  IO.println s!"  Expr typechecks:  {exprSuccess} / {schemaSuccess}"
  IO.println s!"  Schema gen fail:  {schemaFail}"
  IO.println s!"  Expr fail:        {exprFail}"
  if !depths.isEmpty then
    let sortedD := depths.qsort (· < ·)
    let sortedN := nodeCounts.qsort (· < ·)
    let dn := depths.size
    IO.println s!"\n=== Expr depth stats (n={dn}) ==="
    IO.println s!"  min={sortedD[0]!} median={sortedD[dn/2]!} max={sortedD[dn-1]!} mean={(sortedD.foldl (·+·) 0 |>.toFloat) / dn.toFloat}"
    IO.println s!"\n=== Expr node count stats ==="
    IO.println s!"  min={sortedN[0]!} median={sortedN[dn/2]!} max={sortedN[dn-1]!} mean={(sortedN.foldl (·+·) 0 |>.toFloat) / dn.toFloat}"
    IO.println s!"\n=== Constructor frequency (all nodes) ==="
    let totalNodes := nodeCounts.foldl (· + ·) 0
    for i in List.range 12 do
      let count := ctorCounts[i]!
      IO.println s!"  {ctorName i.toUInt8}: {count} ({count.toFloat * 100.0 / totalNodes.toFloat}%)"
    let totalUnary := unaryCounts.foldl (· + ·) 0
    IO.println s!"\n=== unaryApp operator breakdown (total {totalUnary}) ==="
    for i in List.range 5 do
      let count := unaryCounts[i]!
      let pct := if totalUnary == 0 then 0.0 else count.toFloat * 100.0 / totalUnary.toFloat
      IO.println s!"  {unaryOpName i.toUInt8}: {count} ({pct}%)"
    let totalBinary := binaryCounts.foldl (· + ·) 0
    IO.println s!"\n=== binaryApp operator breakdown (total {totalBinary}) ==="
    for i in List.range 12 do
      let count := binaryCounts[i]!
      let pct := if totalBinary == 0 then 0.0 else count.toFloat * 100.0 / totalBinary.toFloat
      IO.println s!"  {binaryOpName i.toUInt8}: {count} ({pct}%)"
    let totalExt := extFunCounts.foldl (· + ·) 0
    IO.println s!"\n=== extension function breakdown (total {totalExt}) ==="
    for i in List.range 22 do
      let count := extFunCounts[i]!
      let pct := if totalExt == 0 then 0.0 else count.toFloat * 100.0 / totalExt.toFloat
      IO.println s!"  {extFunName i.toUInt8}: {count} ({pct}%)"
  IO.println s!"\n=== Schema diversity ==="
  IO.println s!"  Entity types per schema:"
  let etPairs := entityTypeCounts.toArray.qsort (fun a b => a.fst < b.fst)
  for (nEts, count) in etPairs do
    IO.println s!"    {nEts} entity types: {count} schemas"
  if !numAttrs.isEmpty then
    let sortedA := numAttrs.qsort (· < ·)
    let an := numAttrs.size
    IO.println s!"  Attrs per schema: min={sortedA[0]!} median={sortedA[an/2]!} max={sortedA[an-1]!}"

#time #eval schemaPropertyTest 1000 18
-- #time #eval schemaPropertyTest 300 18
-- #time #eval schemaPropertyTest 300 18
-- #time #eval schemaPropertyTest 300 22



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

/-! # Test: derive generators from the LEAN (no TypedExpr) typing relation

Compare performance against `TypeOfTest.lean` (factored, with TypedExpr)
and `TypeOfInlinedTest.lean` (inlined, with TypedExpr).
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

/-- Weight modifier: boost the `hasTag` rules so `hasTag` occurs more often.
Only rewrites the three `hasTag` constructors (matched on the last component of
the constructor name); every other rule passes through at `baseWeight`. Pattern
from Specimen's `ForwardRefListGenerator.lean`. -/
def favorHasTag (baseWeight : Nat) (ctorName : Lean.Name) (_outputIndices : List Nat)
    (_deriveSort : DeriveSort) (_scoreBadness : Nat) (_isRec : Bool) (_size : Nat)
    (_numBase _numRec : Nat) (_numRecCalls : Nat) : Nat :=
  match ctorName with
  -- Mild boost: steer toward hasTag without forcing it. A large multiplier makes
  -- the generator re-attempt hasTag on tag-less random schemas (where HasTagSchema
  -- is infeasible), which with unbounded retries causes severe backtracking.
  | .str _ "hasTagAnyBool" => baseWeight * 2 + 1
  | .str _ "hasTagTt"      => baseWeight * 2 + 1
  | .str _ "hasTagFf"      => baseWeight * 2 + 1
  | .str _ "getTag"        => baseWeight * 2 + 1
  | _                      => baseWeight

initialize registerWeightModifier `favorHasTag favorHasTag ``favorHasTag

set_option trace.Meta.synthInstance false
set_option specimen.scoreType "Scoring.BudgetAwareScore" in
set_option specimen.weightModifier "favorHasTag" in
set_option specimen.precomputeWeights true in
#time derive_mutual
  generator (fun env c ty => ∃ x cout, HasType x c env ty cout)

/-! ## Test: generate well-typed expressions -/

def testEnv : TypeEnv :=
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

/-! ## Property-based test: generated expressions typecheck -/

private def capsSubset (c₁ c₂ : Capabilities) : Bool :=
  c₁.all (c₂.contains ·)

private def capsEq (c₁ c₂ : Capabilities) : Bool :=
  capsSubset c₁ c₂ && capsSubset c₂ c₁

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

private def binOpName : BinaryOp → String
  | .eq => "eq" | .mem => "mem" | .less => "less" | .lessEq => "lessEq"
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .contains => "contains" | .containsAll => "containsAll" | .containsAny => "containsAny"
  | .hasTag => "hasTag" | .getTag => "getTag"

private def unaryOpName : UnaryOp → String
  | .not => "not" | .neg => "neg" | .like _ => "like" | .isEmpty => "isEmpty" | .is _ => "is"

structure ExprStats where
  depths : Array Nat := #[]
  nodeCounts : Array Nat := #[]
  capsSizes : Array Nat := #[]
  topCtorCounts : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0]
  allCtorCounts : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0]
  pathCounts : Array Nat := (List.replicate 144 0).toArray
  opCounts : Std.HashMap String Nat := {}
  attrCounts : Std.HashMap String Nat := {}
  entityCounts : Std.HashMap String Nat := {}
  uniqueExprs : Std.HashSet UInt64 := {}

instance : Hashable Name where hash n := mixHash (hash n.id) (hash n.path)
instance : Hashable EntityUID where hash uid := mixHash (hash uid.ty) (hash uid.eid)
instance : Hashable Prim where
  hash | .bool b => mixHash 0 (hash b) | .int i => mixHash 1 (hash i.toUInt64)
       | .string s => mixHash 2 (hash s) | .entityUID uid => mixHash 3 (hash uid)
instance : Hashable Var where
  hash | .principal => 0 | .action => 1 | .resource => 2 | .context => 3
instance : Hashable PatElem where
  hash | .star => 0 | .justChar c => mixHash 1 (hash c)
instance : Hashable UnaryOp where
  hash | .not => 0 | .neg => 1 | .like p => mixHash 2 (hash p) | .isEmpty => 3 | .is e => mixHash 4 (hash e)
instance : Hashable BinaryOp where
  hash | .eq => 0 | .mem => 1 | .less => 2 | .lessEq => 3 | .add => 4 | .sub => 5
       | .mul => 6 | .contains => 7 | .containsAll => 8 | .containsAny => 9
       | .hasTag => 10 | .getTag => 11
instance : Hashable ExtFun where
  hash | .decimal => 0 | .ip => 1 | .datetime => 2 | .duration => 3
       | .lessThan => 4 | .lessThanOrEqual => 5 | .greaterThan => 6 | .greaterThanOrEqual => 7
       | .isIpv4 => 8 | .isIpv6 => 9 | .isLoopback => 10 | .isMulticast => 11 | .isInRange => 12
       | .toDate => 13 | .toTime => 14 | .offset => 15 | .durationSince => 16
       | .toMilliseconds => 17 | .toSeconds => 18 | .toMinutes => 19 | .toHours => 20 | .toDays => 21

private partial def exprHash : Expr → UInt64
  | .lit p            => mixHash 1 (hash p)
  | .var v            => mixHash 2 (hash v)
  | .ite a b c        => mixHash 3 (mixHash (exprHash a) (mixHash (exprHash b) (exprHash c)))
  | .and a b          => mixHash 4 (mixHash (exprHash a) (exprHash b))
  | .or a b           => mixHash 5 (mixHash (exprHash a) (exprHash b))
  | .unaryApp op a    => mixHash 6 (mixHash (hash op) (exprHash a))
  | .binaryApp op a b => mixHash 7 (mixHash (hash op) (mixHash (exprHash a) (exprHash b)))
  | .hasAttr a attr   => mixHash 8 (mixHash (exprHash a) (hash attr))
  | .getAttr a attr   => mixHash 9 (mixHash (exprHash a) (hash attr))
  | .set xs           => mixHash 10 (xs.foldl (fun h x => mixHash h (exprHash x)) 0)
  | .record axs       => mixHash 11 (axs.foldl (fun h (a, x) => mixHash h (mixHash (hash a) (exprHash x))) 0)
  | .call fn xs       => mixHash 12 (mixHash (hash fn) (xs.foldl (fun h x => mixHash h (exprHash x)) 0))

private def incAt (arr : Array Nat) (i : UInt8) : Array Nat :=
  let idx := i.toNat
  if h : idx < arr.size then arr.set idx (arr[idx] + 1) else arr

private partial def analyze (s : ExprStats) (parentId : Option UInt8) (x : Expr) : ExprStats :=
  let myId := exprCtorId x
  let s := { s with
    allCtorCounts := incAt s.allCtorCounts myId
    pathCounts := match parentId with
      | some pid => incAt s.pathCounts (pid * 12 + myId)
      | none => s.pathCounts }
  match x with
  | .lit (.entityUID uid) =>
    { s with entityCounts := s.entityCounts.insert s!"entity:{uid.ty.id}" (s.entityCounts.getD s!"entity:{uid.ty.id}" 0 + 1) }
  | .var v =>
    let k := match v with | .principal => "var:principal" | .resource => "var:resource" | .action => "var:action" | .context => "var:context"
    { s with entityCounts := s.entityCounts.insert k (s.entityCounts.getD k 0 + 1) }
  | .lit _ => s
  | .ite a b c => analyze (analyze (analyze s (some myId) a) (some myId) b) (some myId) c
  | .and a b => analyze (analyze s (some myId) a) (some myId) b
  | .or a b => analyze (analyze s (some myId) a) (some myId) b
  | .unaryApp op a =>
    let k := s!"unOp:{unaryOpName op}"
    analyze { s with opCounts := s.opCounts.insert k (s.opCounts.getD k 0 + 1) } (some myId) a
  | .binaryApp op a b =>
    let k := s!"binOp:{binOpName op}"
    analyze (analyze { s with opCounts := s.opCounts.insert k (s.opCounts.getD k 0 + 1) } (some myId) a) (some myId) b
  | .hasAttr a attr =>
    let k := s!"hasAttr:{attr}"
    analyze { s with attrCounts := s.attrCounts.insert k (s.attrCounts.getD k 0 + 1) } (some myId) a
  | .getAttr a attr =>
    let k := s!"getAttr:{attr}"
    analyze { s with attrCounts := s.attrCounts.insert k (s.attrCounts.getD k 0 + 1) } (some myId) a
  | .set xs => xs.foldl (fun acc e => analyze acc (some myId) e) s
  | .record axs => axs.foldl (fun acc (_, e) => analyze acc (some myId) e) s
  | .call _ xs => xs.foldl (fun acc e => analyze acc (some myId) e) s

private partial def exprDepth : Expr → Nat
  | .lit _ | .var _ => 1
  | .ite a b c => 1 + max (exprDepth a) (max (exprDepth b) (exprDepth c))
  | .and a b | .or a b | .binaryApp _ a b => 1 + max (exprDepth a) (exprDepth b)
  | .unaryApp _ a | .hasAttr a _ | .getAttr a _ => 1 + exprDepth a
  | .set xs => 1 + (xs.foldl (fun m x => max m (exprDepth x)) 0)
  | .record axs => 1 + (axs.foldl (fun m (_, x) => max m (exprDepth x)) 0)
  | .call _ xs => 1 + (xs.foldl (fun m x => max m (exprDepth x)) 0)

private partial def exprNodeCount : Expr → Nat
  | .lit _ | .var _ => 1
  | .ite a b c => 1 + exprNodeCount a + exprNodeCount b + exprNodeCount c
  | .and a b | .or a b | .binaryApp _ a b => 1 + exprNodeCount a + exprNodeCount b
  | .unaryApp _ a | .hasAttr a _ | .getAttr a _ => 1 + exprNodeCount a
  | .set xs => 1 + xs.foldl (fun s x => s + exprNodeCount x) 0
  | .record axs => 1 + axs.foldl (fun s (_, x) => s + exprNodeCount x) 0
  | .call _ xs => 1 + xs.foldl (fun s x => s + exprNodeCount x) 0

private def ExprStats.record (s : ExprStats) (x : Expr) (cout : Capabilities) : ExprStats :=
  let d := exprDepth x
  let nc := exprNodeCount x
  let topId := exprCtorId x
  let s := analyze { s with
    depths := s.depths.push d
    nodeCounts := s.nodeCounts.push nc
    capsSizes := s.capsSizes.push cout.length
    topCtorCounts := incAt s.topCtorCounts topId
    uniqueExprs := s.uniqueExprs.insert (exprHash x) } none x
  s

private def ExprStats.print (s : ExprStats) : IO Unit := do
  if s.depths.isEmpty then return
  let n := s.depths.size
  let sortedD := s.depths.qsort (· < ·)
  let sortedN := s.nodeCounts.qsort (· < ·)
  let sortedC := s.capsSizes.qsort (· < ·)
  IO.println s!"\n=== Depth stats (n={n}) ==="
  IO.println s!"  min={sortedD[0]!} median={sortedD[n/2]!} mean={(sortedD.foldl (·+·) 0).toFloat / n.toFloat} max={sortedD[n-1]!}"
  IO.println s!"\n=== Node count stats ==="
  IO.println s!"  min={sortedN[0]!} median={sortedN[n/2]!} mean={(sortedN.foldl (·+·) 0).toFloat / n.toFloat} max={sortedN[n-1]!}"
  IO.println s!"\n=== Output capabilities size ==="
  IO.println s!"  min={sortedC[0]!} median={sortedC[n/2]!} mean={(sortedC.foldl (·+·) 0).toFloat / n.toFloat} max={sortedC[n-1]!}"
  IO.println s!"\n=== Uniqueness: {s.uniqueExprs.size}/{n} distinct expressions ==="
  IO.println s!"\n=== Top-level constructor frequency ==="
  for i in List.range 12 do
    let count := s.topCtorCounts[i]!
    if count > 0 then
      IO.println s!"  {ctorName i.toUInt8}: {count} ({count.toFloat * 100.0 / n.toFloat}%)"
  IO.println s!"\n=== Overall constructor frequency (all nodes) ==="
  let totalNodes := s.nodeCounts.foldl (· + ·) 0
  for i in List.range 12 do
    let count := s.allCtorCounts[i]!
    if count > 0 then
      IO.println s!"  {ctorName i.toUInt8}: {count} ({count.toFloat * 100.0 / totalNodes.toFloat}%)"
  IO.println s!"\n=== Binary/Unary op breakdown ==="
  let opPairs := s.opCounts.toArray.qsort (fun a b => a.snd > b.snd)
  for (op, count) in opPairs do
    IO.println s!"  {op}: {count}"
  IO.println s!"\n=== Attribute access breakdown ==="
  let attrPairs := s.attrCounts.toArray.qsort (fun a b => a.snd > b.snd)
  for (attr, count) in attrPairs do
    IO.println s!"  {attr}: {count}"
  IO.println s!"\n=== Entity/variable usage ==="
  let entityPairs := s.entityCounts.toArray.qsort (fun a b => a.snd > b.snd)
  for (ent, count) in entityPairs do
    IO.println s!"  {ent}: {count}"
  IO.println s!"\n=== 2-paths (parent→child) ==="
  let mut pathList : Array (String × Nat) := #[]
  for pid in List.range 12 do
    for cid in List.range 12 do
      let count := s.pathCounts[pid * 12 + cid]!
      if count > 0 then
        pathList := pathList.push (s!"{ctorName pid.toUInt8}→{ctorName cid.toUInt8}", count)
  let sortedPaths := pathList.qsort (fun a b => a.snd > b.snd)
  for (path, count) in sortedPaths do
    IO.println s!"  {path}: {count}"


def propertyTest (n : Nat) (s : Nat) : IO Unit := do
  let caps : Capabilities := [
    (.var .principal, .attr "email"),
    (.var .principal, .attr "manager"),
    (.var .resource, .attr "score"),
    (.var .principal, .tag (.lit (.string "role"))),
    (.var .resource, .tag (.lit (.string "priority")))]
  let env := testEnv
  let types := #[
    .bool .anyBool]
    -- .record (Map.mk [("x", .required (.string))]),
    -- .string]
  let mut passed : Nat := 0
  let mut failed : Nat := 0
  let mut capsFailed : Nat := 0
  let mut genFailed : Nat := 0
  let mut slowCount : Nat := 0
  let mut stats : ExprStats := {}
  let sizes : Array Nat := #[s]
  let mut timings : Array (String × Nat × Nat × Float) := #[]
  for ty in types do
    for structSize in sizes do
      let iters := n / (types.size * sizes.size)
      let startNs ← IO.monoNanosNow
      for _ in List.range iters do
        try
          let genStartNs ← IO.monoNanosNow
          let (x, cout) ← Gen.runUntil (attempts := .some 1)
            (ArbitrarySizedSuchThat.arbitrarySizedST
              (fun (e, cout) => HasType e caps env ty cout) structSize)
            5
          let genElapsedNs := (← IO.monoNanosNow) - genStartNs
          if genElapsedNs > 200_000_000 then
            slowCount := slowCount + 1
            let ms := genElapsedNs.toFloat / 1_000_000.0
            IO.println s!"SLOW ({ms}ms): {repr x}"
          stats := stats.record x cout
          let funcResult := Cedar.Validation.typeOf x caps env
          match funcResult with
          | .ok (funcTx, funcCaps) =>
            if funcTx.typeOf != ty then
              failed := failed + 1
              if failed ≤ 5 then
                IO.println s!"FAIL type: {repr x}\n  expected={repr ty} got={repr funcTx.typeOf}"
            else if !capsEq cout funcCaps then
              capsFailed := capsFailed + 1
              if capsFailed ≤ 5 then
                IO.println s!"FAIL caps: {repr x}\n  relational={repr cout} functional={repr funcCaps}"
            else
              passed := passed + 1
          | .error e =>
            failed := failed + 1
            if failed ≤ 5 then
              IO.println s!"ERROR: {repr e} for {repr x}"
        catch _ =>
          genFailed := genFailed + 1
      let endNs ← IO.monoNanosNow
      let elapsedMs := (endNs - startNs).toFloat / 1000000.0
      timings := timings.push (s!"{repr ty}", structSize, iters, elapsedMs)
  IO.println s!"\n=== Timing breakdown ==="
  IO.println "type\tsize\titers\tms\tms/iter"
  for (tyStr, sz, iters, ms) in timings do
    let perIter := if iters > 0 then ms / iters.toFloat else 0.0
    IO.println s!"{tyStr}\t{sz}\t{iters}\t{ms}\t{perIter}"
  IO.println s!"\n=== Results ({passed + failed + capsFailed + genFailed} attempted) ==="
  IO.println s!"  Passed:        {passed}"
  IO.println s!"  Type failures: {failed}"
  IO.println s!"  Caps failures: {capsFailed}"
  IO.println s!"  Gen failures:  {genFailed}"
  IO.println s!"  Slow (>200ms): {slowCount}"
  stats.print

#time #eval propertyTest 300 12

def bugHunt (maxIters : Nat := 10000) : IO Unit := do
  let caps : Capabilities := []
  let env := testEnv
  let types := #[CedarType.int, .bool .anyBool, .bool .tt, .bool .ff, .string]
  let sizes := #[1, 2, 3, 4, 5]
  let mut attempts : Nat := 0
  for _ in List.range maxIters do
    for ty in types do
      for structSize in sizes do
        attempts := attempts + 1
        try
          let (x, cout) ← Gen.runUntil (attempts := .some 1)
            (ArbitrarySizedSuchThat.arbitrarySizedST
              (fun (e, cout) => HasType e caps env ty cout) structSize)
            1
          let funcResult := Cedar.Validation.typeOf x caps env
          match funcResult with
          | .ok (funcTx, funcCaps) =>
            if funcTx.typeOf != ty then
              IO.println s!"BUG (type) after {attempts} attempts:"
              IO.println s!"  expr={repr x}"
              IO.println s!"  expected={repr ty} got={repr funcTx.typeOf}"
              return
            else if !capsEq cout funcCaps then
              IO.println s!"BUG (caps) after {attempts} attempts:"
              IO.println s!"  expr={repr x}"
              IO.println s!"  relational={repr cout} functional={repr funcCaps}"
              return
          | .error e =>
            IO.println s!"BUG (error) after {attempts} attempts:"
            IO.println s!"  expr={repr x}"
            IO.println s!"  error={repr e}"
            return
        catch _ => pure ()
  IO.println s!"No bugs found after {attempts} attempts."

-- #time #eval bugHunt

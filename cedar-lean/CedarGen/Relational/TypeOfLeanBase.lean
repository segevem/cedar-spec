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

/-! # Shared infrastructure for relational typing generator variants

This file contains all the `Arbitrary`, `Enum`, and helper instances needed
by `derive_mutual` for `HasType`, plus parameterized test functions that
accept the derived instance as an argument.

Individual variant files (in `Variants/`) import this and add a scoped
`derive_mutual` with different Specimen options.
-/

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

/-! ## Deterministic Gen runners

`Gen.runWith` and `Gen.runUntilWith` use `runRandWith` to produce
deterministic results from a fixed seed. This enables reproducible
generation: storing `(seed, size)` is sufficient to regenerate the
same output without saving the full result bytes. -/

private def errorOfGenError {α : Type} : Except GenError α → IO α
  | .ok a => pure a
  | .error e => throw (.userError (toString (repr e)))

/-- SplitMix64 finalizer used as a seed diffuser.

`Plausible.runRandWith` builds its RNG via `mkStdGen`, whose initialization
does **no** scrambling for seeds below `2147483562` (`mkStdGen s = ⟨s+1, 1⟩`),
so contiguous integer seeds produce highly correlated initial RNG states and
hence structurally correlated generated expressions. We pass every seed through
this SplitMix64 mix first, so consecutive counter values (`seed`, `seed+1`, …)
map to well-spread, effectively-independent RNG streams across the full
`StdGen` state space. This makes both within-run diversity and between-run
independence sound (the latter matters for honest bootstrap CIs over repeated
runs). SplitMix64 is bijective, so distinct seeds still map to distinct streams. -/
def scrambleSeed (seed : Nat) : Nat :=
  let x := seed.toUInt64 + 0x9e3779b97f4a7c15
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  (x ^^^ (x >>> 31)).toNat

def Gen.runWith (seed : Nat) (x : Gen α) (size : Nat) : IO α :=
  letI : MonadLift (ReaderT (ULift Nat) (Except GenError)) IO :=
    ⟨fun m => errorOfGenError <| ReaderT.run m ⟨size⟩⟩
  Plausible.runRandWith (scrambleSeed seed) x

partial def Gen.runUntilWith (seed : Nat) (attempts : Option Nat := .none) (x : Gen α) (size : Nat) : IO α := do
  let mut currentSeed := seed
  let mut remaining := attempts
  repeat
    match ← tryCatch (do let r ← Gen.runWith currentSeed x size; pure (some r)) (fun _ => pure none) with
    | some result => return result
    | none =>
      currentSeed := currentSeed + 1
      match remaining with
      | .some 0 => throw (.userError "Gen.runUntilWith: Out of attempts")
      | .some n => remaining := .some (n - 1)
      | .none => pure ()
  throw (.userError "Gen.runUntilWith: unreachable")

/-! ## Shared typeclass instances -/

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

/-! ## Test environment -/

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

def defaultCaps : Capabilities := [
  (.var .principal, .attr "email"),
  (.var .principal, .attr "manager"),
  (.var .resource, .attr "score"),
  (.var .principal, .tag (.lit (.string "role"))),
  (.var .resource, .tag (.lit (.string "priority")))]

/-! ## Expression statistics infrastructure -/

private def capsSubset (c₁ c₂ : Capabilities) : Bool :=
  c₁.all (c₂.contains ·)

private def capsEq (c₁ c₂ : Capabilities) : Bool :=
  capsSubset c₁ c₂ && capsSubset c₂ c₁

private def numCtorIds : Nat := 18

private def exprCtorId : Expr → UInt8
  | .lit (.bool _)      => 0
  | .lit (.int _)       => 1
  | .lit (.string _)    => 2
  | .lit (.entityUID _) => 3
  | .var _              => 4
  | .ite ..             => 5
  | .and ..             => 6
  | .or ..              => 7
  | .unaryApp ..        => 8
  | .binaryApp ..       => 9
  | .hasAttr ..         => 10
  | .getAttr ..         => 11
  | .set ..             => 12
  | .record ..          => 13
  | .call (.decimal) ..   => 14
  | .call (.ip) ..        => 15
  | .call (.datetime) ..  => 16
  | .call (.duration) ..  => 17
  | .call ..              => 14  -- other ext calls grouped with decimal

private def ctorName : UInt8 → String
  | 0 => "litBool" | 1 => "litInt" | 2 => "litStr" | 3 => "litEntity"
  | 4 => "var" | 5 => "ite" | 6 => "and" | 7 => "or"
  | 8 => "unaryApp" | 9 => "binaryApp" | 10 => "hasAttr" | 11 => "getAttr"
  | 12 => "set" | 13 => "record" | 14 => "callDecimal" | 15 => "callIp"
  | 16 => "callDatetime" | 17 => "callDuration" | _ => "?"

private def binOpName : BinaryOp → String
  | .eq => "eq" | .mem => "mem" | .less => "less" | .lessEq => "lessEq"
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .contains => "contains" | .containsAll => "containsAll" | .containsAny => "containsAny"
  | .hasTag => "hasTag" | .getTag => "getTag"

private def unaryOpName : UnaryOp → String
  | .not => "not" | .neg => "neg" | .like _ => "like" | .isEmpty => "isEmpty" | .is _ => "is"

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

structure ExprStats where
  depths : Array Nat := #[]
  nodeCounts : Array Nat := #[]
  capsSizes : Array Nat := #[]
  topCtorCounts : Array Nat := (List.replicate numCtorIds 0).toArray
  allCtorCounts : Array Nat := (List.replicate numCtorIds 0).toArray
  pathCounts : Array Nat := (List.replicate (numCtorIds * numCtorIds) 0).toArray
  path3Counts : Array Nat := (List.replicate (numCtorIds * numCtorIds * numCtorIds) 0).toArray
  opCounts : Std.HashMap String Nat := {}
  attrCounts : Std.HashMap String Nat := {}
  entityCounts : Std.HashMap String Nat := {}
  uniqueExprs : Std.HashSet UInt64 := {}
  uniqueSkeletons : Std.HashSet UInt64 := {}

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

private partial def skeletonHash : Expr → UInt64
  | .lit (.bool _)      => 1
  | .lit (.int _)       => 2
  | .lit (.string _)    => 3
  | .lit (.entityUID _) => 4
  | .var v            => mixHash 5 (hash v)
  | .ite a b c        => mixHash 6 (mixHash (skeletonHash a) (mixHash (skeletonHash b) (skeletonHash c)))
  | .and a b          => mixHash 7 (mixHash (skeletonHash a) (skeletonHash b))
  | .or a b           => mixHash 8 (mixHash (skeletonHash a) (skeletonHash b))
  | .unaryApp op a    => mixHash 9 (mixHash (hash op) (skeletonHash a))
  | .binaryApp op a b => mixHash 10 (mixHash (hash op) (mixHash (skeletonHash a) (skeletonHash b)))
  | .hasAttr a attr   => mixHash 11 (mixHash (skeletonHash a) (hash attr))
  | .getAttr a attr   => mixHash 12 (mixHash (skeletonHash a) (hash attr))
  | .set xs           => mixHash 13 (xs.foldl (fun h x => mixHash h (skeletonHash x)) 0)
  | .record axs       => mixHash 14 (axs.foldl (fun h (a, x) => mixHash h (mixHash (hash a) (skeletonHash x))) 0)
  | .call fn xs       => mixHash 15 (mixHash (hash fn) (xs.foldl (fun h x => mixHash h (skeletonHash x)) 0))

private def incAt (arr : Array Nat) (i : UInt8) : Array Nat :=
  let idx := i.toNat
  if h : idx < arr.size then arr.set idx (arr[idx] + 1) else arr

private def incAt3 (arr : Array Nat) (gp p c : UInt8) : Array Nat :=
  let idx := gp.toNat * numCtorIds * numCtorIds + p.toNat * numCtorIds + c.toNat
  if h : idx < arr.size then arr.set idx (arr[idx] + 1) else arr

private partial def analyze (s : ExprStats) (grandparentId : Option UInt8) (parentId : Option UInt8) (x : Expr) : ExprStats :=
  let myId := exprCtorId x
  let s := { s with
    allCtorCounts := incAt s.allCtorCounts myId
    pathCounts := match parentId with
      | some pid => incAt s.pathCounts (pid * 18 + myId)
      | none => s.pathCounts
    path3Counts := match grandparentId, parentId with
      | some gid, some pid => incAt3 s.path3Counts gid pid myId
      | _, _ => s.path3Counts }
  match x with
  | .lit (.entityUID uid) =>
    { s with entityCounts := s.entityCounts.insert s!"entity:{uid.ty.id}" (s.entityCounts.getD s!"entity:{uid.ty.id}" 0 + 1) }
  | .var v =>
    let k := match v with | .principal => "var:principal" | .resource => "var:resource" | .action => "var:action" | .context => "var:context"
    { s with entityCounts := s.entityCounts.insert k (s.entityCounts.getD k 0 + 1) }
  | .lit _ => s
  | .ite a b c => analyze (analyze (analyze s parentId (some myId) a) parentId (some myId) b) parentId (some myId) c
  | .and a b => analyze (analyze s parentId (some myId) a) parentId (some myId) b
  | .or a b => analyze (analyze s parentId (some myId) a) parentId (some myId) b
  | .unaryApp op a =>
    let k := s!"unOp:{unaryOpName op}"
    analyze { s with opCounts := s.opCounts.insert k (s.opCounts.getD k 0 + 1) } parentId (some myId) a
  | .binaryApp op a b =>
    let k := s!"binOp:{binOpName op}"
    analyze (analyze { s with opCounts := s.opCounts.insert k (s.opCounts.getD k 0 + 1) } parentId (some myId) a) parentId (some myId) b
  | .hasAttr a attr =>
    let k := s!"hasAttr:{attr}"
    analyze { s with attrCounts := s.attrCounts.insert k (s.attrCounts.getD k 0 + 1) } parentId (some myId) a
  | .getAttr a attr =>
    let k := s!"getAttr:{attr}"
    analyze { s with attrCounts := s.attrCounts.insert k (s.attrCounts.getD k 0 + 1) } parentId (some myId) a
  | .set xs => xs.foldl (fun acc e => analyze acc parentId (some myId) e) s
  | .record axs => axs.foldl (fun acc (_, e) => analyze acc parentId (some myId) e) s
  | .call _ xs => xs.foldl (fun acc e => analyze acc parentId (some myId) e) s

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

def ExprStats.record (s : ExprStats) (x : Expr) (cout : Capabilities) : ExprStats :=
  let d := exprDepth x
  let nc := exprNodeCount x
  let topId := exprCtorId x
  let s := analyze { s with
    depths := s.depths.push d
    nodeCounts := s.nodeCounts.push nc
    capsSizes := s.capsSizes.push cout.length
    topCtorCounts := incAt s.topCtorCounts topId
    uniqueExprs := s.uniqueExprs.insert (exprHash x)
    uniqueSkeletons := s.uniqueSkeletons.insert (skeletonHash x) } none none x
  s

def ExprStats.print (s : ExprStats) : IO Unit := do
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
  IO.println s!"=== Skeleton uniqueness: {s.uniqueSkeletons.size}/{n} distinct structures (ignoring literal values) ==="
  IO.println s!"\n=== Top-level constructor frequency ==="
  for i in List.range numCtorIds do
    let count := s.topCtorCounts[i]!
    if count > 0 then
      IO.println s!"  {ctorName i.toUInt8}: {count} ({count.toFloat * 100.0 / n.toFloat}%)"
  IO.println s!"\n=== Overall constructor frequency (all nodes) ==="
  let totalNodes := s.nodeCounts.foldl (· + ·) 0
  for i in List.range numCtorIds do
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
  for pid in List.range numCtorIds do
    for cid in List.range numCtorIds do
      let count := s.pathCounts[pid * numCtorIds + cid]!
      if count > 0 then
        pathList := pathList.push (s!"{ctorName pid.toUInt8}→{ctorName cid.toUInt8}", count)
  let sortedPaths := pathList.qsort (fun a b => a.snd > b.snd)
  for (path, count) in sortedPaths do
    IO.println s!"  {path}: {count}"
  IO.println s!"\n=== 3-paths (grandparent→parent→child) ==="
  let mut path3List : Array (String × Nat) := #[]
  for gid in List.range numCtorIds do
    for pid in List.range numCtorIds do
      for cid in List.range numCtorIds do
        let count := s.path3Counts[gid * numCtorIds * numCtorIds + pid * numCtorIds + cid]!
        if count > 0 then
          path3List := path3List.push (s!"{ctorName gid.toUInt8}→{ctorName pid.toUInt8}→{ctorName cid.toUInt8}", count)
  let sortedPath3 := path3List.qsort (fun a b => a.snd > b.snd)
  IO.println s!"  (distinct 3-paths: {path3List.size})"
  for (path, count) in sortedPath3 do
    IO.println s!"  {path}: {count}"

/-! ## Parameterized test function

Uses the `ArbitrarySizedSuchThat` instance via typeclass resolution — the
caller controls which instance is in scope by opening the appropriate
variant namespace. -/

def propertyTest
    (env : TypeEnv) (caps : Capabilities) (ty : CedarType)
    (n : Nat) (structSize : Nat)
    [inst : ArbitrarySizedSuchThat (Expr × Capabilities) (fun (e, cout) => HasType e caps env ty cout)]
    : IO Unit := do
  let mut passed : Nat := 0
  let mut failed : Nat := 0
  let mut capsFailed : Nat := 0
  let mut genFailed : Nat := 0
  let mut slowCount : Nat := 0
  let mut stats : ExprStats := {}
  let startNs ← IO.monoNanosNow
  for _ in List.range n do
    try
      let genStartNs ← IO.monoNanosNow
      let (x, cout) ← Gen.runUntil (attempts := .some 1)
        (inst.arbitrarySizedST structSize) 5
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
  let perIter := if n > 0 then elapsedMs / n.toFloat else 0.0
  IO.println s!"\n=== Timing ==="
  IO.println s!"  type={repr ty} size={structSize} iters={n} ms={elapsedMs} ms/iter={perIter}"
  IO.println s!"\n=== Results ({passed + failed + capsFailed + genFailed} attempted) ==="
  IO.println s!"  Passed:        {passed}"
  IO.println s!"  Type failures: {failed}"
  IO.println s!"  Caps failures: {capsFailed}"
  IO.println s!"  Gen failures:  {genFailed}"
  IO.println s!"  Slow (>200ms): {slowCount}"
  stats.print

/-! ## Parameterized FFI generation function

Used by `CedarFFI/Generate.lean` to call whichever variant the Rust side requests.
The caller opens the appropriate variant namespace to bring the instance into scope. -/

def generateExprs
    (env : TypeEnv) (caps : Capabilities) (ty : CedarType)
    (size : Nat) (count : Nat) (seed : Option Nat := none)
    [inst : ArbitrarySizedSuchThat (Expr × Capabilities) (fun (e, cout) => HasType e caps env ty cout)]
    : IO (List Expr) := do
  let mut exprs : List Expr := []
  let mut currentSeed := seed.getD 0
  for _ in List.range count do
    try
      let result ← if seed.isSome then
          Gen.runUntilWith currentSeed (attempts := .some 3) (inst.arbitrarySizedST size) size
        else
          Gen.runUntil (attempts := .some 3) (inst.arbitrarySizedST size) size
      let (x, _cout) := result
      exprs := exprs ++ [x]
    catch _ => pure ()
    currentSeed := currentSeed + 1
  return exprs

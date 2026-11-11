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

import CedarGen.Relational.ExprGenWeights
import Specimen.Basalt

set_option maxHeartbeats 0

/-! Generator speed with Basalt emission off: the production expression
derivation (`CedarGen.Relational.ExprGen`) without its proofs, `specimen.emitBasalt := false`. -/

namespace Cedar.Validation.Relational.ExprGen
open Cedar.Spec Cedar.Data Cedar.Validation Scoring Schedules
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option specimen.autoDeriveDeps true
set_option specimen.emitBasalt false
set_option specimen.multiOutput true
set_option maxRecDepth 100000
set_option specimen.prefixSearch true
namespace Speed
set_option specimen.sizeSplit false in
set_option specimen.deriveFloors false in
set_option specimen.plainBinds true in
set_option specimen.parallelCodegen true in
set_option specimen.reportPhaseTimers true in
set_option specimen.scoreType "Scoring.InversionAwareScore" in
set_option specimen.weightModifier "Cedar.Validation.Relational.ExprGen.favorRequestVars" in
set_option specimen.precomputeWeights true in
scoped derive_mutual
  generator (fun env c ty => ∃ x cout, HasType true true x c env ty cout)
end Speed
end Cedar.Validation.Relational.ExprGen

open Cedar.Validation.Relational.ExprGen.Speed

/-! Claim 1, measured: for each expression sort, the fraction of generated terms of a given size
that contain it. Terms come from the `HasType` generator at a pool of target types. -/

open Cedar.Spec Cedar.Data Cedar.Validation Plausible
open Cedar.Validation.Relational

namespace ExprBench

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

def Gen.runWith (seed : Nat) (x : Plausible.Gen α) (size : Nat) : IO α :=
  letI : MonadLift (ReaderT (ULift Nat) (Except GenError)) IO :=
    ⟨fun m => errorOfGenError <| ReaderT.run m ⟨size⟩⟩
  Plausible.runRandWith (scrambleSeed seed) x

partial def Gen.runUntilWith (seed : Nat) (attempts : Option Nat := .none) (x : Plausible.Gen α) (size : Nat) : IO α := do
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


def act (eid : String) : EntityUID := ⟨⟨"Action", []⟩, eid⟩
def userT : EntityType := ⟨"User", []⟩
def groupT : EntityType := ⟨"Group", []⟩
def docT : EntityType := ⟨"Document", []⟩

def multiSchema : Schema :=
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
      (act "view", { appliesToPrincipal := Set.make [userT], appliesToResource := Set.make [docT],
                     ancestors := Set.empty,
                     context := Map.make [("ip", .required .string), ("mfa", .required (.bool .anyBool))] }),
      (act "edit", { appliesToPrincipal := Set.make [userT, groupT], appliesToResource := Set.make [docT],
                     ancestors := Set.make [act "view"],
                     context := Map.make [("ip", .required .string)] }),
      (act "share", { appliesToPrincipal := Set.make [userT], appliesToResource := Set.make [docT, groupT],
                      ancestors := Set.empty, context := Map.empty })] }

def kpLast (s : String) : String := (s.splitOn ".").getLast!

def kpLabel : Expr → String
  | .lit _ => "Lit" | .var _ => "Var" | .ite .. => "If" | .and .. => "And" | .or .. => "Or"
  | .unaryApp (.is _) _ => "Is" | .unaryApp (.like _) _ => "Like"
  | .unaryApp op _ => "Unary::" ++ kpLast (toString (repr op))
  | .binaryApp op _ _ => "Binary::" ++ kpLast (toString (repr op))
  | .getAttr .. => "GetAttr" | .hasAttr .. => "HasAttr"
  | .extHasAttr .. => "ExtHasAttr"
  | .set _ => "Set" | .record _ => "Record"
  | .call f _ => "ExtFun::" ++ kpLast (toString (repr f))

def kpChildren : Expr → List Expr
  | .lit _ | .var _ => []
  | .ite a b c => [a, b, c]
  | .and a b | .or a b | .binaryApp _ a b => [a, b]
  | .unaryApp _ a | .getAttr a _ | .hasAttr a _ => [a]
  | .extHasAttr a _ _ => [a]
  | .set xs | .call _ xs => xs
  | .record axs => axs.map (·.2)

def runGen (seed size : Nat) (g : Plausible.Gen α) : IO (Option α) := do
  try pure (some (← Gen.runWith seed g size)) catch _ => pure none



def ctorLabel : Expr → String
  | .lit _ => "lit" | .var _ => "var" | .ite .. => "ite" | .and .. => "and" | .or .. => "or"
  | .unaryApp .. => "unaryApp" | .binaryApp .. => "binaryApp" | .getAttr .. => "getAttr"
  | .hasAttr .. => "hasAttr" | .extHasAttr .. => "extHasAttr" | .set _ => "set"
  | .record _ => "record" | .call .. => "call"

partial def labels (fine : Bool) (x : Expr) : List String :=
  (if fine then kpLabel x else ctorLabel x) :: (kpChildren x).flatMap (labels fine)


def types : List CedarType :=
  [.bool .anyBool, .bool .tt, .bool .ff, .int, .string, .entity userT, .entity docT, .set .int,
   .set .string, .set (.entity userT), .ext .decimal, .ext .ipAddr, .ext .datetime, .ext .duration,
   .record (Map.make [("a", .required .int), ("b", .required .string)])]

def main (args : List String) : IO Unit := do
  let n := (args.headD "300").toNat!
  let size := (args.getD 1 "8").toNat!
  let env := (multiSchema.environments.head!)
  let t0 ← IO.monoMsNow
  let mut terms := 0
  let mut fails := 0
  for ty in types do
    for i in [0:n] do
      let r ← runGen (i * 7919 + size) size
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (p : Expr × Capabilities) => HasType true true p.1 [] env ty p.2) size)
      match r with
      | none => fails := fails + 1
      | some _ => terms := terms + 1
  let dt := (← IO.monoMsNow) - t0
  IO.println s!"size {size}: {terms} terms, {fails} failures in {dt} ms = {terms * 1000 / max dt 1} terms/s"

end ExprBench

def main (args : List String) : IO Unit := ExprBench.main args

import CedarGen.Relational.TypeOfLeanBase

/-! # Presence / type-distribution analyzer

Count-bounded generation that reports, for the exprs a variant actually produces:
* the distribution of `typeOf` results (what type each produced expr gets), and
* per-construct PRESENCE (% of produced exprs that contain each construct ≥1).

Pure analysis over `Expr` — no `derive_mutual`, so it rebuilds in seconds. The
`ArbitrarySizedSuchThat` instance is supplied by the runner via `open Variant.X`. -/

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

namespace PresenceTest

def tyKind : CedarType → String
  | .bool .anyBool => "bool anyBool  (on-target)"
  | .bool .tt      => "bool tt"
  | .bool .ff      => "bool ff"
  | .int           => "int"
  | .string        => "string"
  | .entity _      => "entity"
  | .set _         => "set"
  | .record _      => "record"
  | .ext _         => "ext"

partial def collect : Expr → List String
  | .lit (.bool _)      => ["litBool"]
  | .lit (.int _)       => ["litInt"]
  | .lit (.string _)    => ["litStr"]
  | .lit (.entityUID _) => ["litEntity"]
  | .var _              => ["var"]
  | .ite a b c          => "ite" :: (collect a ++ collect b ++ collect c)
  | .and a b            => "and" :: (collect a ++ collect b)
  | .or a b             => "or" :: (collect a ++ collect b)
  | .unaryApp _ a       => "unaryApp" :: collect a
  | .binaryApp _ a b    => "binaryApp" :: (collect a ++ collect b)
  | .hasAttr a _        => "hasAttr" :: collect a
  | .getAttr a _        => "getAttr" :: collect a
  | .set xs             => "set" :: (xs.foldl (fun acc e => acc ++ collect e) [])
  | .record axs         => "record" :: (axs.foldl (fun acc p => acc ++ collect p.2) [])
  | .call fn xs         => ("call:" ++ toString (reprStr fn)) :: (xs.foldl (fun acc e => acc ++ collect e) [])

def analyzeGen (env : TypeEnv) (caps : Capabilities) (sizes : Array Nat) (count : Nat)
    [ArbitrarySizedSuchThat (Expr × Capabilities) (fun (e, cout) => HasType e caps env (.bool .anyBool) cout)]
    : IO Unit := do
  let ty : CedarType := .bool .anyBool
  let mut tyDist : Std.HashMap String Nat := {}
  let mut presence : Std.HashMap String Nat := {}
  let mut produced : Nat := 0
  let mut genFail : Nat := 0
  let startNs ← IO.monoNanosNow
  let deadline := startNs + 120_000_000_000  -- 120s wall-clock safety
  for i in [0:count] do
    if (← IO.monoNanosNow) > deadline then break
    let structSize := sizes[i % sizes.size]!
    try
      let (x, _cout) ← Gen.runUntil (attempts := .some 1)
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (e, cout) => HasType e caps env ty cout) structSize) 5
      produced := produced + 1
      let k := match Cedar.Validation.typeOf x caps env with
        | .ok (tx, _) => tyKind tx.typeOf
        | .error _    => "ILL-TYPED (typeOf error)"
      tyDist := tyDist.insert k (tyDist.getD k 0 + 1)
      for c in (collect x).eraseDups do
        presence := presence.insert c (presence.getD c 0 + 1)
    catch _ =>
      genFail := genFail + 1
  let pf := produced.toFloat
  IO.println s!"\nproduced={produced}  genFail(threw)={genFail}"
  IO.println "\n=== TYPE of produced exprs (constraint asked for `bool anyBool`) ==="
  for (k, c) in (tyDist.toList).toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {k}: {c} ({c.toFloat * 100.0 / pf}%)"
  IO.println "\n=== CONSTRUCT PRESENCE (% of produced exprs containing it ≥1) ==="
  for (k, c) in (presence.toList).toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {k}: {c.toFloat * 100.0 / pf}%"

/-- Generate until `want` ill-typed exprs are found; print each expr + its `typeOf` error
    so we can see *why* it's rejected (e.g. made-up attributes / entity types / operand types). -/
def dumpIllTyped (env : TypeEnv) (caps : Capabilities) (sizes : Array Nat) (want : Nat)
    [ArbitrarySizedSuchThat (Expr × Capabilities) (fun (e, cout) => HasType e caps env (.bool .anyBool) cout)]
    : IO Unit := do
  let ty : CedarType := .bool .anyBool
  let mut found : Nat := 0
  let mut i : Nat := 0
  let startNs ← IO.monoNanosNow
  let deadline := startNs + 120_000_000_000
  repeat
    if found ≥ want then break
    if (← IO.monoNanosNow) > deadline then break
    let structSize := sizes[i % sizes.size]!
    i := i + 1
    try
      let (x, _cout) ← Gen.runUntil (attempts := .some 1)
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (e, cout) => HasType e caps env ty cout) structSize) 5
      match Cedar.Validation.typeOf x caps env with
      | .error e =>
        found := found + 1
        IO.println s!"\n[ill-typed #{found}]  typeOf error = {reprStr e}"
        IO.println s!"  expr = {reprStr x}"
      | .ok _ => pure ()
    catch _ => pure ()

end PresenceTest

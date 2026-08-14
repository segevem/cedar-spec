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

import CedarGen.Relational.SchemaTest

/-! # Forcing: surface underexplored features via bool-consumer wrappers

A Cedar policy condition must be `bool`. To exercise ops whose *result* type is not
`bool` — arithmetic (`add`/`sub`/`mul`/`neg`), extension calls (`decimal`/`ip`/…),
`getTag`/`getAttr`, set ops — we:

  1. generate a well-typed subexpression at a chosen **target type `T`** (this is
     where the `T`-producing ops live), then
  2. **wrap** it in a `bool`-returning consumer (`eq`, `less`, `isEmpty`, …).

The wrapped expression is a valid `bool` policy that is *guaranteed* to contain
`T`-typed subexpressions. Both operands are generated at `T` so the wrapper always
typechecks (`Long == Long`, `ext == ext`, `set == set`, …).

Everything runs at **empty caps** (matching real validation). Capability-gated ops
(`getTag`, optional `getAttr`) can't sit bare under a wrapper — they need their
`hasTag`/`hasAttr &&` guard, so see `forceGuardedGetTag`.

Reuses the `HasType` generator and `testEnv` from `SchemaTest`/`TypeOfLeanTest`.
Play by editing the `#eval`s at the bottom (target type, wrapper, size). -/

open CedarGen.Relational.Schema
open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

namespace CedarGen.Relational.Forcing

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ## Op tally (standalone) -/

private def binOpName : BinaryOp → String
  | .eq => "eq" | .mem => "mem" | .less => "less" | .lessEq => "lessEq"
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .contains => "contains" | .containsAll => "containsAll" | .containsAny => "containsAny"
  | .hasTag => "hasTag" | .getTag => "getTag"

private def unOpName : UnaryOp → String
  | .not => "not" | .neg => "neg" | .like _ => "like" | .isEmpty => "isEmpty" | .is _ => "is"

private def extFunName : ExtFun → String
  | .decimal => "decimal" | .ip => "ip" | .datetime => "datetime" | .duration => "duration"
  | .lessThan => "lessThan" | .lessThanOrEqual => "lessThanOrEqual"
  | .greaterThan => "greaterThan" | .greaterThanOrEqual => "greaterThanOrEqual"
  | .isIpv4 => "isIpv4" | .isIpv6 => "isIpv6" | .isLoopback => "isLoopback"
  | .isMulticast => "isMulticast" | .isInRange => "isInRange"
  | .toDate => "toDate" | .toTime => "toTime" | .offset => "offset" | .durationSince => "durationSince"
  | .toMilliseconds => "toMs" | .toSeconds => "toSec" | .toMinutes => "toMin"
  | .toHours => "toHr" | .toDays => "toDay"

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
  | .call fn xs       => let k := s!"call:{extFunName fn}"; xs.foldl tally (m.insert k (m.getD k 0 + 1))

private def printOps (ops : Std.HashMap String Nat) : IO Unit := do
  IO.print "  ops:"
  for (op, cnt) in ops.toArray.qsort (fun a b => a.snd > b.snd) do IO.print s!" {op}={cnt}"
  IO.println ""

/-! ## Subexpression generator (target type `T`, given caps) -/

/-- Generate one well-typed subexpression of type `T` under `caps` (default empty). -/
def genSub (env : TypeEnv) (T : CedarType) (size : Nat) (caps : Capabilities := []) : IO (Option Expr) := do
  try
    let (x, _cout) ← Gen.runUntil (attempts := .some 100)
      (ArbitrarySizedSuchThat.arbitrarySizedST (fun (e, cout) => HasType e caps env T cout) size) 3
    pure (some x)
  catch _ => pure none

/-! ## Bool-consumer wrappers (both operands must be type `T`) -/

def wEq         (a b : Expr) : Expr := .binaryApp .eq a b            -- any T
def wLess       (a b : Expr) : Expr := .binaryApp .less a b          -- T = .int
def wLessEq     (a b : Expr) : Expr := .binaryApp .lessEq a b        -- T = .int
def wContainsAll (a b : Expr) : Expr := .binaryApp .containsAll a b  -- T = .set _
def wIsEmpty    (a _ : Expr) : Expr := .unaryApp .isEmpty a          -- T = .set _ (unary: ignores b)

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

/-! ## Driver -/

/-- Generate `n` policies of the form `wrap (e₁ : T) (e₂ : T)` and report how many
typecheck to `bool`, the op distribution, and a few samples.

Each subexpr pair is wall-clock timed: any pair taking longer than `slowMs` (a slow
generation OR a slow `gen-fail` = both `genSub`s exhausting their 100-attempt budget,
which flags an infeasible target for this env) is logged with `repr`, so the slow
tail is visible instead of silently bogging the run. -/
def forceExplore (T : CedarType) (wrap : Expr → Expr → Expr) (n size : Nat)
    (env : TypeEnv := testEnv) (label : String := "") (sample : Nat := 3)
    (slowMs : Float := 200.0) (maxSlowLogs : Nat := 8) : IO Unit := do
  IO.println s!"\n=== Force T={repr T} {label} (n={n}, size={size}) ==="
  let mut gen := 0
  let mut valid := 0
  let mut notBool := 0
  let mut err := 0
  let mut genFail := 0
  let mut printed := 0
  let mut slow := 0
  let mut slowLogged := 0
  let mut maxMs : Float := 0.0
  let mut ops : Std.HashMap String Nat := {}
  for _ in List.range n do
    let t0 ← IO.monoNanosNow
    let oa ← genSub env T size
    let ob ← genSub env T size
    let ms := ((← IO.monoNanosNow) - t0).toFloat / 1_000_000.0
    if ms > maxMs then maxMs := ms
    match oa, ob with
    | some a, some b =>
      gen := gen + 1
      let policy := wrap a b
      ops := tally ops policy
      if ms > slowMs then
        slow := slow + 1
        if slowLogged < maxSlowLogs then
          slowLogged := slowLogged + 1
          IO.println s!"  SLOW-OK ({ms}ms) depth={depth policy} nodes={nodes policy}: {repr policy}"
      match Cedar.Validation.typeOf policy [] env with
      | .ok (tx, _) =>
        match tx.typeOf with
        | .bool _ => valid := valid + 1
        | other =>
          notBool := notBool + 1
          if notBool ≤ 2 then IO.println s!"  NOT-BOOL got={repr other}\n    {repr policy}"
        if printed < sample then
          printed := printed + 1
          IO.println s!"  e.g. {repr policy}"
      | .error e =>
        err := err + 1
        if err ≤ 2 then IO.println s!"  ERROR {repr e}\n    {repr policy}"
    | _, _ =>
      genFail := genFail + 1
      if ms > slowMs then
        slow := slow + 1
        if slowLogged < maxSlowLogs then
          slowLogged := slowLogged + 1
          IO.println s!"  SLOW-FAIL ({ms}ms): genSub exhausted its attempts (T={repr T} likely infeasible for this env)"
  IO.println s!"  generated={gen}/{n} | bool={valid} not-bool={notBool} error={err} gen-fail={genFail} slow(>{slowMs}ms)={slow} maxMs={maxMs}"
  printOps ops

/-- Deterministically force a **guarded `getTag`** into a valid `bool` policy:
`hasTag entity k && (getTag entity k) == (rhs : tagTy)`. The `hasTag` produces the
capability, `&&` threads it, `getTag` consumes it. `entity` must be an entity-typed
expr whose entity type declares `tags tagTy` in `env` (e.g. in `testEnv`,
`principal : User tags String`, `resource : Document tags Int`). -/
def forceGuardedGetTag (entity : Expr) (tagKey : String) (tagTy : CedarType)
    (n size : Nat) (env : TypeEnv := testEnv) (sample : Nat := 3) : IO Unit := do
  IO.println s!"\n=== Force guarded getTag {repr entity}[{tagKey}] : {repr tagTy} (n={n}, size={size}) ==="
  let mut valid := 0
  let mut bad := 0
  let mut printed := 0
  for _ in List.range n do
    let rhsO ← genSub env tagTy size   -- comparison partner (empty caps is fine)
    match rhsO with
    | none => bad := bad + 1
    | some rhs =>
      let key := Expr.lit (.string tagKey)
      let gt := Expr.binaryApp .getTag entity key
      let policy := Expr.and (.binaryApp .hasTag entity key) (.binaryApp .eq gt rhs)
      match Cedar.Validation.typeOf policy [] env with
      | .ok (tx, _) =>
        match tx.typeOf with
        | .bool _ => valid := valid + 1
        | other => bad := bad + 1; if bad ≤ 2 then IO.println s!"  NOT-BOOL got={repr other}\n    {repr policy}"
        if printed < sample then printed := printed + 1; IO.println s!"  e.g. {repr policy}"
      | .error e => bad := bad + 1; if bad ≤ 2 then IO.println s!"  ERROR {repr e}\n    {repr policy}"
  IO.println s!"  bool={valid}/{n} bad={bad}"

/-! ## Playground — edit target type / wrapper / size and re-run -/

-- Arithmetic and Long-typed getAttr/getTag surface under a Long target:
#eval forceExplore .int wEq 40 15 (label := "Long via ==")
#eval forceExplore .int wLess 40 15 (label := "Long via <")

-- Extension constructors (near-zero at a bool target) surface under an ext target:
-- #eval forceExplore (.ext .decimal) wEq 1 20 (label := "decimal via ==")
-- #eval forceExplore (.ext .ipAddr) wEq 40 15 (label := "ip via ==")

-- -- Set ops / set constructors surface under a set target:
-- #eval forceExplore (.set (.set .string)) wIsEmpty 40 30 (label := "set<string> via isEmpty")
-- #eval forceExplore (.set .int) wContainsAll 40 15 (label := "set<int> via containsAll")

-- -- Guaranteed guarded getTag (testEnv: principal:User tags String, resource:Document tags Int):
#eval forceGuardedGetTag (.var .principal) "role" .string 20 15
#eval forceGuardedGetTag (.var .resource) "priority" (.set .string) 20 15

end CedarGen.Relational.Forcing

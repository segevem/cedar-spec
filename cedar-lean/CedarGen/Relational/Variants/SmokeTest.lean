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

import CedarGen.Relational.Variants.BudgetAware
import CedarGen.Relational.Variants.Default
import CedarGen.Relational.Variants.Flat
import CedarGen.Relational.TypeOfLeanBase

/-! # Smoke test: compare strategy variants (time-bounded)

Each variant gets a fixed wall-clock budget. Reports how many valid+correct
outputs each produced, plus diversity stats. The process exits hard at the
deadline so a single slow generation can't cause overrun.
-/

open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

def timeLimitNs : Nat := 30_000_000_000  -- 30 seconds

/-- Run a strategy until the time limit. Checks deadline before AND after
    each generation attempt; prints results and exits if over. -/
def timedTest
    (env : TypeEnv) (caps : Capabilities)
    (sizes : Array Nat)
    [ArbitrarySizedSuchThat (Expr × Capabilities) (fun (e, cout) => HasType e caps env (.bool .anyBool) cout)]
    : IO Unit := do
  let ty : CedarType := .bool .anyBool
  let mut passed : Nat := 0
  let mut failed : Nat := 0
  let mut genFailed : Nat := 0
  let mut stats : ExprStats := {}
  let startNs ← IO.monoNanosNow
  let mut iters : Nat := 0
  let deadline := startNs + timeLimitNs
  -- Timing buckets (in ms): <1, 1-10, 10-100, 100-1000, >1000
  let mut bucket0 : Nat := 0  -- < 1ms
  let mut bucket1 : Nat := 0  -- 1-10ms
  let mut bucket2 : Nat := 0  -- 10-100ms
  let mut bucket3 : Nat := 0  -- 100ms-1s
  let mut bucket4 : Nat := 0  -- > 1s
  let mut totalGenNs : Nat := 0
  let mut maxGenMs : Float := 0.0
  let mut slowExprs : Array (Float × String) := #[]  -- (ms, repr) for >100ms
  repeat
    let nowNs ← IO.monoNanosNow
    if nowNs > deadline then break
    let structSize := sizes[iters % sizes.size]!
    iters := iters + 1
    let genStart ← IO.monoNanosNow
    try
      let (x, cout) ← Gen.runUntil (attempts := .some 1)
        (ArbitrarySizedSuchThat.arbitrarySizedST
          (fun (e, cout) => HasType e caps env ty cout) structSize)
        5
      let genEnd ← IO.monoNanosNow
      let genNs := genEnd - genStart
      totalGenNs := totalGenNs + genNs
      let genMs := genNs.toFloat / 1_000_000.0
      if genMs > maxGenMs then maxGenMs := genMs
      if genMs < 1.0 then bucket0 := bucket0 + 1
      else if genMs < 10.0 then bucket1 := bucket1 + 1
      else if genMs < 100.0 then bucket2 := bucket2 + 1
      else if genMs < 1000.0 then
        bucket3 := bucket3 + 1
        if slowExprs.size < 10 then
          slowExprs := slowExprs.push (genMs, toString (repr x))
      else
        bucket4 := bucket4 + 1
        if slowExprs.size < 10 then
          slowExprs := slowExprs.push (genMs, toString (repr x))
      if genEnd > deadline then
        stats := stats.record x cout
        let funcResult := Cedar.Validation.typeOf x caps env
        match funcResult with
        | .ok (funcTx, _) => if funcTx.typeOf == ty then passed := passed + 1 else failed := failed + 1
        | .error _ => failed := failed + 1
        break
      stats := stats.record x cout
      let funcResult := Cedar.Validation.typeOf x caps env
      match funcResult with
      | .ok (funcTx, _funcCaps) =>
        if funcTx.typeOf == ty then
          passed := passed + 1
        else
          failed := failed + 1
      | .error _ =>
        failed := failed + 1
    catch _ =>
      let genEnd ← IO.monoNanosNow
      let genNs := genEnd - genStart
      totalGenNs := totalGenNs + genNs
      let genMs := genNs.toFloat / 1_000_000.0
      if genMs > maxGenMs then maxGenMs := genMs
      if genMs < 1.0 then bucket0 := bucket0 + 1
      else if genMs < 10.0 then bucket1 := bucket1 + 1
      else if genMs < 100.0 then bucket2 := bucket2 + 1
      else if genMs < 1000.0 then bucket3 := bucket3 + 1
      else bucket4 := bucket4 + 1
      genFailed := genFailed + 1
  let endNs ← IO.monoNanosNow
  let elapsedMs := (endNs - startNs).toFloat / 1_000_000.0
  let elapsedSec := elapsedMs / 1000.0
  let totalAttempts := passed + failed + genFailed
  let throughput := if elapsedSec > 0 then totalAttempts.toFloat / elapsedSec else 0.0
  let meanGenMs := if totalAttempts > 0 then totalGenNs.toFloat / 1_000_000.0 / totalAttempts.toFloat else 0.0
  IO.println s!"\n=== Results ({elapsedSec}s, {totalAttempts} attempts, {throughput} attempts/sec) ==="
  IO.println s!"  Passed:       {passed}"
  IO.println s!"  Failed:       {failed}"
  IO.println s!"  Gen failures: {genFailed}"
  IO.println s!"  Valid rate:   {if totalAttempts > 0 then passed.toFloat * 100.0 / totalAttempts.toFloat else 0.0}%"
  IO.println s!"\n=== Generation timing ==="
  IO.println s!"  Mean: {meanGenMs}ms  Max: {maxGenMs}ms"
  IO.println s!"  < 1ms:      {bucket0} ({bucket0.toFloat * 100.0 / totalAttempts.toFloat}%)"
  IO.println s!"  1-10ms:     {bucket1} ({bucket1.toFloat * 100.0 / totalAttempts.toFloat}%)"
  IO.println s!"  10-100ms:   {bucket2} ({bucket2.toFloat * 100.0 / totalAttempts.toFloat}%)"
  IO.println s!"  100ms-1s:   {bucket3} ({bucket3.toFloat * 100.0 / totalAttempts.toFloat}%)"
  IO.println s!"  > 1s:       {bucket4} ({bucket4.toFloat * 100.0 / totalAttempts.toFloat}%)"
  if !slowExprs.isEmpty then
    IO.println s!"\n=== Slow generations (>100ms, up to 10) ==="
    let sorted := slowExprs.qsort (fun a b => a.fst > b.fst)
    for (ms, expr) in sorted do
      IO.println s!"  [{ms}ms] {expr.take 200}"
  stats.print

def testSizes : Array Nat := #[10, 12, 15]

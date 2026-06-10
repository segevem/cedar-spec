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

import CedarGenFaithful.ExprTest
import CedarGenFaithful.ExprPrint

open CedarGenFaithful
open Cedar.Spec

/-- Output format: one JSON object per line.
    {"bytes":[b0,b1,...],"expr":"...", "depth":N}
    Rust PBT test reads these, replays bytes at the given depth, and asserts match. -/
def main : IO Unit := do
  let numTrials := 100000

  -- Use a random base seed
  let baseSeed ← IO.monoNanosNow

  for i in List.range numTrials do
    let seed := baseSeed + i
    -- Vary depth: 0 through 7
    let maxDepth := i % 8
    let (expr, bytes) ← runAndRecord maxDepth seed
    let bytesList := bytes.toList.map (fun b => toString b.toNat)
    let exprStr := printExpr expr
    -- Escape quotes in exprStr for JSON
    let exprJson := exprStr.replace "\\" "\\\\" |>.replace "\"" "\\\""
    IO.println s!"\{\"bytes\":[{String.intercalate "," bytesList}],\"expr\":\"{exprJson}\",\"depth\":{maxDepth}}"

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

open CedarGen.Relational.Schema
open CedarGen.Relational.Lean
open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

/-! # Per-schema policy analysis

For each of `numSchemas` random well-formed schemas, generate `exprsPerSchema`
well-typed (`anyBool`, empty-caps) expressions and report how the generated
policies differ across schemas (op distribution, tag usage, depth, and agreement
with the functional validator), plus a cross-schema comparison table.

Reuses the precompiled `WfTypeEnv` and `HasType` generators from `SchemaTest`.
Run with e.g. `#eval schemaPolicyAnalysis 5 20 15`. -/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-! ## Pretty-printing schemas -/

private def ppName (n : EntityType) : String :=
  if n.path.isEmpty then n.id else String.intercalate "::" (n.path ++ [n.id])

mutual
private partial def ppTy : CedarType → String
  | .bool _    => "Bool"
  | .int       => "Long"
  | .string    => "String"
  | .entity et => ppName et
  | .set t     => s!"Set<{ppTy t}>"
  | .record rty =>
    "{" ++ String.intercalate ", " (rty.toList.map (fun (a, q) => s!"{a}: {ppQual q}")) ++ "}"
  | .ext _     => "ext"
private partial def ppQual : Qualified CedarType → String
  | .required t => ppTy t
  | .optional t => s!"{ppTy t}?"
end

private def ppEntry (et : EntityType) : EntitySchemaEntry → String
  | .standard s =>
    let ancs := s.ancestors.toList.map ppName
    let ancStr := if ancs.isEmpty then "" else s!" in [{String.intercalate ", " ancs}]"
    let attrs := s.attrs.toList.map (fun (a, q) => s!"{a}: {ppQual q}")
    let tagStr := match s.tags with | some t => s!" tags {ppTy t}" | none => ""
    "    entity " ++ ppName et ++ ancStr ++ " {" ++ String.intercalate ", " attrs ++ "}" ++ tagStr ++ ";"
  | .enum eids => s!"    entity {ppName et} enum [{String.intercalate ", " eids.toList}];"

private def ppAction (uid : EntityUID) (e : ActionSchemaEntry) : String :=
  let ps := e.appliesToPrincipal.toList.map ppName
  let rs := e.appliesToResource.toList.map ppName
  let ancs := e.ancestors.toList.map (fun u => s!"{ppName u.ty}::\"{u.eid}\"")
  let applies := if ps.isEmpty && rs.isEmpty then ""
    else " appliesTo {principal: [" ++ String.intercalate ", " ps ++ "], resource: [" ++ String.intercalate ", " rs ++ "]}"
  let inStr := if ancs.isEmpty then "" else s!" in [{String.intercalate ", " ancs}]"
  s!"    action \"{uid.eid}\"{applies}{inStr};"

/-- Pretty-print a `TypeEnv` as a (roughly Cedar-schema-shaped) multi-line string. -/
private def ppSchema (env : TypeEnv) : String :=
  let ents := env.ets.toList.map (fun (et, e) => ppEntry et e)
  let acts := env.acts.toList.map (fun (uid, e) => ppAction uid e)
  let r := env.reqty
  let req := "    request {principal: " ++ ppName r.principal ++ ", action: \"" ++ r.action.eid ++ "\", resource: " ++ ppName r.resource ++ ", context: " ++ ppTy (.record r.context) ++ "}"
  String.intercalate "\n" (ents ++ acts ++ [req])

private def binOpName' : BinaryOp → String
  | .eq => "eq" | .mem => "mem" | .less => "less" | .lessEq => "lessEq"
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .contains => "contains" | .containsAll => "containsAll" | .containsAny => "containsAny"
  | .hasTag => "hasTag" | .getTag => "getTag"

private def unOpName' : UnaryOp → String
  | .not => "not" | .neg => "neg" | .like _ => "like" | .isEmpty => "isEmpty" | .is _ => "is"

/-- Accumulate `binOp:<name>` / `unOp:<name>` occurrence counts over an expr. -/
private partial def tallyOps (m : Std.HashMap String Nat) (e : Expr) : Std.HashMap String Nat :=
  match e with
  | .lit _ | .var _  => m
  | .ite a b c       => tallyOps (tallyOps (tallyOps m a) b) c
  | .and a b | .or a b => tallyOps (tallyOps m a) b
  | .unaryApp op a   => let k := s!"unOp:{unOpName' op}"; tallyOps (m.insert k (m.getD k 0 + 1)) a
  | .binaryApp op a b => let k := s!"binOp:{binOpName' op}"; tallyOps (tallyOps (m.insert k (m.getD k 0 + 1)) a) b
  | .hasAttr a _ | .getAttr a _ => tallyOps m a
  | .set xs          => xs.foldl tallyOps m
  | .record axs      => axs.foldl (fun acc (_, x) => tallyOps acc x) m
  | .call _ xs       => xs.foldl tallyOps m

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

/-- Does the expression contain a `getTag` anywhere? -/
private partial def containsGetTag : Expr → Bool
  | .binaryApp .getTag _ _ => true
  | .binaryApp _ a b       => containsGetTag a || containsGetTag b
  | .ite a b c             => containsGetTag a || containsGetTag b || containsGetTag c
  | .and a b | .or a b     => containsGetTag a || containsGetTag b
  | .unaryApp _ a | .hasAttr a _ | .getAttr a _ => containsGetTag a
  | .set xs                => xs.any containsGetTag
  | .record axs            => axs.any (fun (_, e) => containsGetTag e)
  | .call _ xs             => xs.any containsGetTag
  | _                      => false

/-- Generate one well-typed (`anyBool`, empty-caps) expression for a fixed env. -/
private def genExprForEnv (env : TypeEnv) (size : Nat) (ty : CedarType) : IO (Option Expr) := do
  try
    let (x, _cout) ← Gen.runUntil (attempts := .none)
      (ArbitrarySizedSuchThat.arbitrarySizedST
        (fun (e, cout) => HasType e [] env ty cout) size)
      3
    pure (some x)
  catch _ => pure none

/-- Does the schema have at least one tagged (standard) entity? -/
private def envHasTag (env : TypeEnv) : Bool :=
  env.ets.toList.any (fun (_, e) => match e with | .standard s => s.tags.isSome | .enum _ => false)

/-- Keep generating schemas until one has a tagged entity (bounded by `fuel`). -/
private partial def generateTaggedSchema (schemaSize fuel : Nat) : IO (Option TypeEnv) := do
  if fuel == 0 then return none
  match ← generateSchema schemaSize with
  | some env => if envHasTag env then return some env else generateTaggedSchema schemaSize (fuel - 1)
  | none     => generateTaggedSchema schemaSize (fuel - 1)

structure SchemaRow where
  idx : Nat
  nEts : Nat
  nTagged : Nat
  nActs : Nat
  gen : Nat
  pass : Nat
  fail : Nat
  avgDepth : Float
  avgNodes : Float
  hasTag : Nat
  getTag : Nat
  mem : Nat

/-- Analyze how generated policies differ across `numSchemas` random schemas,
running `exprsPerSchema` expressions per schema. `sample` = how many example
expressions to print per schema. -/
def schemaPolicyAnalysis (ty : CedarType) (numSchemas exprsPerSchema schemaSize size : Nat) (sample : Nat := 2) : IO Unit := do
  let mut rows : Array SchemaRow := #[]
  for sIdx in List.range numSchemas do
    match ← generateTaggedSchema schemaSize 100000 with
    | none => IO.println s!"[schema {sIdx}] schema generation failed"
    | some env =>
      let nEts := env.ets.size
      let nActs := env.acts.size
      let nTagged := env.ets.toList.foldl (fun acc (_, e) =>
        acc + (match e with | .standard s => (if s.tags.isSome then 1 else 0) | .enum _ => 0)) 0
      let mut gen := 0
      let mut pass := 0
      let mut fail := 0
      let mut ops : Std.HashMap String Nat := {}
      let mut depthSum := 0
      let mut nodeSum := 0
      let mut printed := 0
      IO.println s!"\n=== Schema {sIdx}: {nEts} entity types ({nTagged} tagged), {nActs} actions ==="
      IO.println (ppSchema env)
      for _ in List.range exprsPerSchema do
        match ← genExprForEnv env size ty with
        | none => pure ()
        | some x =>
          gen := gen + 1
          ops := tallyOps ops x
          depthSum := depthSum + depth x
          nodeSum := nodeSum + nodes x
          match Cedar.Validation.typeOf x [] env with
          | .ok (tx, _) =>
            if tx.typeOf == ty then pass := pass + 1
            else
              fail := fail + 1
              IO.println s!"  MISMATCH:\n relational={repr ty} \nfunctional={repr tx.typeOf}\n    {repr x}\n"
          | .error e =>
            fail := fail + 1
            IO.println s!"  ERROR: {repr e}\n    {repr x}"
          if printed < sample && containsGetTag x then
            printed := printed + 1
            IO.println s!"  getTag e.g. {repr x}"
      let avgDepth := if gen > 0 then depthSum.toFloat / gen.toFloat else 0.0
      let avgNodes := if gen > 0 then nodeSum.toFloat / gen.toFloat else 0.0
      IO.println s!"\n  exprs: {gen}/{exprsPerSchema} generated | {pass} agree, {fail} disagree | avgDepth={avgDepth} avgNodes={avgNodes}"
      let opPairs := ops.toArray.qsort (fun a b => a.snd > b.snd)
      IO.print "  ops:"
      for (op, cnt) in opPairs do IO.print s!" {op}={cnt}"
      IO.println ""
      rows := rows.push {
        idx := sIdx, nEts := nEts, nTagged := nTagged, nActs := nActs,
        gen := gen, pass := pass, fail := fail, avgDepth := avgDepth, avgNodes := avgNodes,
        hasTag := ops.getD "binOp:hasTag" 0, getTag := ops.getD "binOp:getTag" 0,
        mem := ops.getD "binOp:mem" 0 }
  IO.println s!"\n=== Cross-schema comparison ({rows.size} schemas, {exprsPerSchema} exprs each) ==="
  IO.println "schema\tets\ttagged\tacts\tgen\tpass\tfail\tavgDepth\tavgNodes\thasTag\tgetTag\tmem"
  for r in rows do
    IO.println s!"{r.idx}\t{r.nEts}\t{r.nTagged}\t{r.nActs}\t{r.gen}\t{r.pass}\t{r.fail}\t{r.avgDepth}\t{r.avgNodes}\t{r.hasTag}\t{r.getTag}\t{r.mem}"

#eval schemaPolicyAnalysis (.bool .ff) 5 600 15 25

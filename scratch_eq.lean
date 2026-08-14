import CedarGen.Relational.SchemaTest
import CedarGen.Relational.PolicyGen
import CedarGen.Relational.Variants.BudgetAware

open CedarGen.Relational
open Variant.BudgetAware
open CedarGen.Relational.PolicyGen
open Cedar.Spec
open Std

def kindOf : Expr → String
  | .lit _ => "Lit"
  | .var _ => "Var"
  | .ite _ _ _ => "Ite"
  | .and _ _ => "And"
  | .or _ _ => "Or"
  | .unaryApp _ _ => "Unary"
  | .binaryApp _ _ _ => "Binary"
  | .getAttr _ _ => "GetAttr"
  | .hasAttr _ _ => "HasAttr"
  | .set _ => "Set"
  | .record _ => "Record"
  | .call _ _ => "ExtFun"

def childrenOf : Expr → List Expr
  | .ite c t e => [c, t, e]
  | .and a b => [a, b]
  | .or a b => [a, b]
  | .unaryApp _ x => [x]
  | .binaryApp _ a b => [a, b]
  | .getAttr x _ => [x]
  | .hasAttr x _ => [x]
  | .set xs => xs
  | .record m => m.map (·.2)
  | .call _ xs => xs
  | _ => []

partial def eqOperandTags : Expr → List String
  | e =>
    let here := match e with
      | .binaryApp .eq a b => ["Eq→" ++ kindOf a, "Eq→" ++ kindOf b]
      | _ => []
    here ++ (childrenOf e).flatMap eqOperandTags

partial def countIf (f : Expr → Bool) (e : Expr) : Nat :=
  (if f e then 1 else 0) + (childrenOf e).foldl (fun acc c => acc + countIf f c) 0

def isNot : Expr → Bool | .unaryApp .not _ => true | _ => false
def isIs  : Expr → Bool | .unaryApp (.is _) _ => true | _ => false

def measureEq (sz : Nat) (nSeeds cnt : Nat) : IO Unit := do
  let mut tally : HashMap String Nat := {}
  let mut npol := 0; let mut nodes := 0; let mut nEq := 0; let mut nIs := 0; let mut nNot := 0
  for seed in [0:nSeeds] do
    match ← generateSchemaOnly seed sz with
    | none => pure ()
    | some env =>
      let ps ← generatePolicies env sz cnt (some seed)
      for p in ps do
        let e := p.toExpr
        npol := npol + 1
        nodes := nodes + countIf (fun _ => true) e
        nIs := nIs + countIf isIs e
        nNot := nNot + countIf isNot e
        for t in eqOperandTags e do
          nEq := nEq + 1
          tally := tally.insert t ((tally.getD t 0) + 1)
  IO.println s!"\n=== sz={sz}  policies={npol}  nodes/pol={(nodes.toFloat / npol.toFloat)} ==="
  IO.println s!"  VALIDATE harness: Is/pol={(nIs.toFloat/npol.toFloat)}  Not/pol={(nNot.toFloat/npol.toFloat)}  (expect Is~1.0, Not~0.75)"
  IO.println s!"  Eq operand-tags total={nEq}  (={(nEq.toFloat/npol.toFloat)}/pol, 2 per == node)"
  let sorted := tally.toList.toArray.qsort (fun a b => a.2 > b.2)
  IO.println "  Eq→<operand kind>  count  (share of all Eq operands):"
  for (k, v) in sorted do
    IO.println s!"    {k}  {v}   {(v.toFloat / nEq.toFloat * 100.0)}%"

#eval! show IO Unit from do
  measureEq 12 150 8
  measureEq 20 150 8

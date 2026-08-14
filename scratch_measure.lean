import CedarGen.Relational.SchemaTest
import CedarGen.Relational.PolicyGen

open CedarGen.Relational.PolicyGen Cedar.Spec Cedar.Data

-- record-ish = record-TYPED at the AST level we can see without full inference:
-- a record literal, or `context` (always record-typed). Misses getAttr-of-record, so it's a
-- lower bound — but it captures the two ways `Lub.record` gets its operands.
def isRecordish : Expr → Bool
  | .record _ => true
  | .var .context => true
  | _ => false

def isLitBool : Expr → Bool
  | .lit (.bool _) => true
  | _ => false

-- Count LubRecord-triggering SITES: (ite with non-literal guard & a record-ish branch),
-- (eq, not-both-lit, with a record-ish operand). Both force `Lub` on two record types.
partial def countLub (acc : Nat × Nat × Nat × Nat) (e : Expr) : Nat × Nat × Nat × Nat := Id.run do
  let mut a := acc          -- (iteLub, eqLub, recLits, recFields)
  match e with
  | .record fs => a := (a.1, a.2.1, a.2.2.1 + 1, a.2.2.2 + fs.length)
  | _ => pure ()
  match e with
  | .ite c t f =>
      if (!isLitBool c) && (isRecordish t || isRecordish f) then a := (a.1 + 1, a.2.1, a.2.2.1, a.2.2.2)
      a := countLub (countLub (countLub a c) t) f
  | .binaryApp .eq x y =>
      let bothLit := (match x with | .lit _ => true | _ => false) && (match y with | .lit _ => true | _ => false)
      if (!bothLit) && (isRecordish x || isRecordish y) then a := (a.1, a.2.1 + 1, a.2.2.1, a.2.2.2)
      a := countLub (countLub a x) y
  | .binaryApp _ x y => a := countLub (countLub a x) y
  | .and x y => a := countLub (countLub a x) y
  | .or x y => a := countLub (countLub a x) y
  | .unaryApp _ x => a := countLub a x
  | .getAttr x _ => a := countLub a x
  | .hasAttr x _ => a := countLub a x
  | .set es => for x in es do a := countLub a x
  | .record fs => for kv in fs do a := countLub a kv.2
  | .call _ args => for x in args do a := countLub a x
  | _ => pure ()
  return a

partial def countIsEmpty (acc : Nat) (e : Expr) : Nat := Id.run do
  let mut a := acc
  match e with
  | .unaryApp .isEmpty _ => a := a + 1
  | _ => pure ()
  match e with
  | .ite c t f => a := countIsEmpty (countIsEmpty (countIsEmpty a c) t) f
  | .and x y | .or x y | .binaryApp _ x y => a := countIsEmpty (countIsEmpty a x) y
  | .unaryApp _ x | .getAttr x _ | .hasAttr x _ => a := countIsEmpty a x
  | .set es => for x in es do a := countIsEmpty a x
  | .record fs => for kv in fs do a := countIsEmpty a kv.2
  | .call _ args => for x in args do a := countIsEmpty a x
  | _ => pure ()
  return a

def measureAt (size nEnvs perEnv : Nat) : IO Unit := do
  let mut lub : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
  let mut iem := 0
  let mut np := 0
  let mut polMs := 0
  for s in List.range nEnvs do
    match ← generateSchemaOnly (s * 131 + 7) size with
    | none => pure ()
    | some env =>
      let tp0 ← IO.monoMsNow
      let policies ← generatePolicies env size perEnv (some (s * 977 + 13))
      let tp1 ← IO.monoMsNow
      polMs := polMs + (tp1 - tp0)
      for p in policies do
        np := np + 1
        let full := p.toExpr
        lub := countLub lub full
        iem := countIsEmpty iem full
  let f := fun (n : Nat) => (Float.ofNat n) / (Float.ofNat (max np 1))
  let polSec := (Float.ofNat np) / (Float.ofNat (max polMs 1) / 1000.0)
  IO.println s!"=== size {size}: {np} policies, {polSec} pol/s ==="
  IO.println s!"  recLits/pol   {f lub.2.2.1}   fields/record {(Float.ofNat lub.2.2.2) / (Float.ofNat (max lub.2.2.1 1))}"
  IO.println s!"  LubRecord sites/pol {f (lub.1 + lub.2.1)}  (ite-lub {f lub.1}, eq-lub {f lub.2.1})"
  IO.println s!"  isEmpty/pol   {f iem}\n"

#eval show IO Unit from do
  measureAt 12 60 60
  measureAt 20 50 50

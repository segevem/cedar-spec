import CedarGen.Relational.RaceChallenge2

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! Manual counterexample disproving `complexThm`.

P1 = (a ∧ b) ∨ (c ∧ d)
P2 = (a ∨ c) ∧ (b ∨ d)

Choose a=true, b=false, c=false, d=true:
  P1 = (true ∧ false) ∨ (false ∧ true) = false  ⇒ deny
  P2 = (true ∨ false) ∧ (false ∨ true) = true    ⇒ allow
-/

def bt : Value := .prim (.bool true)
def bf : Value := .prim (.bool false)

def principalUID : EntityUID := ⟨userTy, "alice"⟩
def resourceUID  : EntityUID := ⟨docTy, "doc1"⟩

def req : Request :=
  { principal := principalUID
    action := viewAction
    resource := resourceUID
    context := Map.empty }

def es : Entities :=
  Map.make [
    (principalUID, { attrs := Map.make [("a", bt), ("b", bf)], ancestors := Set.empty, tags := Map.empty }),
    (resourceUID,  { attrs := Map.make [("c", bf), ("d", bt)], ancestors := Set.empty, tags := Map.empty }),
    (viewAction,   { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty })]

#eval (isAuthorized req es policyP1).decision  -- expect deny
#eval (isAuthorized req es policyP2).decision  -- expect allow
#eval (isAuthorized req es policyP1).decision ≠ (isAuthorized req es policyP2).decision

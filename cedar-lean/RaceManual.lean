import CedarGen.Relational.RaceChallenge

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- An `E`-typed entity carrying both `foo` and `bar` as Bool attributes. -/
def mkE (eid : String) (foo bar : Bool) : EntityUID × EntityData :=
  (⟨eTy, eid⟩,
   { attrs := Map.make [("foo", .prim (.bool foo)), ("bar", .prim (.bool bar))],
     ancestors := Set.empty,
     tags := Map.empty })

/-- Principal has `foo = true`, resource has `bar = false`.
    So `foo || bar = true` (allow) but `foo && bar = false` (deny). -/
def req : Request :=
  { principal := ⟨eTy, "p"⟩, action := aAction, resource := ⟨eTy, "r"⟩,
    context := Map.empty }

def es : Entities :=
  Map.make [ mkE "p" true false, mkE "r" false false,
             (aAction, { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }) ]

#eval (isAuthorized req es policyOrs).decision       -- expect allow
#eval (isAuthorized req es policyTwoWhens).decision   -- expect deny
#eval decide ((isAuthorized req es policyOrs).decision = (isAuthorized req es policyTwoWhens).decision)  -- expect false

import CedarGen.Relational.RaceChallenge3

open Cedar.Spec
open Cedar.Data

/-- Witness: availStart=5, availEnd=10, reqStart=0, reqEnd=7.
    Doc interval [0,7] overlaps User window [5,10] (they share [5,7]),
    but the Doc's *start* (0) is outside the User window, so the buggy
    policy's `availStart <= reqStart` (5 <= 0) fails. -/

def alice : EntityUID := ⟨userTy, "alice"⟩
def doc1  : EntityUID := ⟨docTy, "doc1"⟩

def req : Request :=
  { principal := alice, action := viewAction, resource := doc1, context := Map.empty }

def aliceData : EntityData :=
  { attrs := Map.make [("availStart", .prim (.int 5)), ("availEnd", .prim (.int 10))],
    ancestors := Set.empty, tags := Map.empty }

def doc1Data : EntityData :=
  { attrs := Map.make [("reqStart", .prim (.int 0)), ("reqEnd", .prim (.int 7))],
    ancestors := Set.empty, tags := Map.empty }

def actionData : EntityData :=
  { attrs := Map.empty, ancestors := Set.empty, tags := Map.empty }

def es : Entities :=
  Map.make [(alice, aliceData), (doc1, doc1Data), (viewAction, actionData)]

#eval (isAuthorized req es policyOverlap).decision  -- expect .allow
#eval (isAuthorized req es policyBuggy).decision     -- expect .deny

-- Confirm they DIFFER:
#eval (isAuthorized req es policyOverlap).decision != (isAuthorized req es policyBuggy).decision

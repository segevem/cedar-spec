import CedarProto.Encode
import CedarProto.PolicySet

/-! # Round-trip tests for the full-Policy encoder (`CedarProto.Encode.encodePolicies`)

Encode a `Cedar.Spec.Policy` (with real principal/action/resource scope constraints) to
protobuf, decode it back with CedarProto's `PolicySet` `Message` instance, link templates,
and check the recovered `Policy` matches. This exercises the scope-constraint encoding
(`.eq`/`.mem`/`.is`/`.isMem`) that `encodePolicySet` (expr-only, all-`Any`) could not emit. -/

open Cedar.Spec Cedar.Data CedarProto.Encode Proto

namespace EncodePolicyRoundtripTest

private def roundtrip (ps : List Cedar.Spec.Policy) : Except String Policies :=
  (Message.interpret? (encodePolicies ps) : Except String Cedar.Spec.Proto.PolicySet).map (·.toPolicies)

private def uid (ty eid : String) : EntityUID := ⟨{ id := ty, path := [] }, eid⟩
private def ety (ty : String) : EntityType := { id := ty, path := [] }

private def mk (pS : Scope) (aS : ActionScope) (rS : Scope) (cond : Expr) : Cedar.Spec.Policy :=
  { id := "p", effect := .permit,
    principalScope := .principalScope pS, actionScope := aS,
    resourceScope := .resourceScope rS, condition := [⟨.when, cond⟩] }

/-- `encodePolicies` renumbers ids to `policy{idx}`, so the expected policy uses `policy0`. -/
private def check (name : String) (p : Cedar.Spec.Policy) : IO Unit :=
  let expect := { p with id := "policy0" }
  match roundtrip [p] with
  | .ok [d] =>
    if d == expect then IO.println s!"  PASS: {name}"
    else IO.println s!"  FAIL: {name}\n    expected: {repr expect}\n    decoded:  {repr d}"
  | .ok other => IO.println s!"  FAIL: {name} (expected 1 policy, got {other.length})"
  | .error e => IO.println s!"  FAIL: {name} (decode error: {e})"

#eval do
  IO.println "=== Encode Policy scope roundtrip ==="
  let t : Expr := .lit (.bool true)
  -- principal / resource scopes round-trip structurally
  check "any/any/any"       (mk .any (.actionScope .any) .any t)
  check "principal eq"      (mk (.eq (uid "User" "alice")) (.actionScope .any) .any t)
  check "principal mem"     (mk (.mem (uid "Grp" "g")) (.actionScope .any) .any t)
  check "principal is"      (mk (.is (ety "User")) (.actionScope .any) .any t)
  check "principal isMem"   (mk (.isMem (ety "User") (uid "Grp" "g")) (.actionScope .any) .any t)
  check "resource eq"       (mk .any (.actionScope .any) (.eq (uid "Doc" "d")) t)
  check "resource is"       (mk .any (.actionScope .any) (.is (ety "Doc")) t)
  -- action: eq and inAny round-trip structurally
  check "action eq"         (mk .any (.actionScope (.eq (uid "Action" "view"))) .any t)
  check "action inAny"      (mk .any (.actionInAny [uid "Action" "a", uid "Action" "b"]) .any t)
  -- full combination + a non-trivial condition
  check "combo"             (mk (.eq (uid "User" "alice"))
                               (.actionScope (.eq (uid "Action" "view")))
                               (.mem (uid "Folder" "f"))
                               (.binaryApp .eq (.var .principal) (.var .resource)))

end EncodePolicyRoundtripTest

import CedarGen.Relational.RaceChallenge4
open CedarGen.Relational.ReqEnt
open Cedar.Spec Cedar.Data Cedar.Validation Plausible
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

macro "cedar_unfold" : tactic =>
  `(tactic| simp only [
      Cedar.Spec.isAuthorized, Cedar.Spec.satisfiedPolicies, Cedar.Spec.satisfiedWithEffect,
      Cedar.Spec.satisfied, Cedar.Spec.errorPolicies, Cedar.Spec.errored, Cedar.Spec.hasError,
      Cedar.Spec.evaluate, Cedar.Spec.apply₁, Cedar.Spec.apply₂, Cedar.Spec.Result.as,
      Cedar.Spec.Policy.toExpr, Cedar.Spec.Conditions.toExpr, Cedar.Spec.Condition.toExpr,
      Cedar.Spec.Scope.toExpr, Cedar.Spec.PrincipalScope.toExpr, Cedar.Spec.ResourceScope.toExpr,
      Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Var.eqEntityUID, Cedar.Spec.Var.inEntityUID,
      Cedar.Spec.Var.isEntityType, List.filterMap, List.isEmpty, List.reverse, List.reverseAux,
      List.foldl, List.map, Bool.and, Bool.not])

theorem distrib_proof : distribThm := by
  intro req es hwt
  simp only [policyLeft, policyRight]
  cedar_unfold
  generalize evaluate ea req es = A
  generalize evaluate eb req es = B
  generalize evaluate ec req es = C
  cases A <;> cases B <;> cases C <;>
    simp only [Value.asBool, Except.bind_ok, Except.bind_err] <;>
    (repeat' split) <;> rfl

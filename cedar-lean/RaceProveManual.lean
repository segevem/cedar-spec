import CedarGen.Relational.RaceChallenge4
open Cedar.Spec Cedar.Data Cedar.Validation
set_option maxHeartbeats 4000000

/-- The core boolean-algebra identity, stated purely on the evaluator and
    independent of the request/entities: `and x (or y z) ≡ or (and x y) (and x z)`
    even under short-circuit / error semantics, because re-evaluating `x`, `y`, `z`
    is deterministic. -/
theorem eval_distrib (x y z : Expr) (req : Request) (es : Entities) :
    evaluate (.and x (.or y z)) req es =
    evaluate (.or (.and x y) (.and x z)) req es := by
  simp only [evaluate, Result.as]
  cases hx : evaluate x req es with
  | error e => rfl
  | ok vx =>
    cases vx with
    | prim p =>
      cases p with
      | bool bx =>
        cases bx with
        | false => rfl
        | true =>
          cases hy : evaluate y req es with
          | error e => rfl
          | ok vy =>
            cases vy with
            | prim py =>
              cases py with
              | bool by_ => cases by_ <;> rfl
              | int i => rfl
              | string s => rfl
              | entityUID u => rfl
            | set s => rfl
            | record r => rfl
            | ext e => rfl
      | int i => rfl
      | string s => rfl
      | entityUID u => rfl
    | set s => rfl
    | record r => rfl
    | ext e => rfl

/-- Congruence: `and`'s second operand can be replaced by an expression that
    evaluates identically. -/
theorem and_cong (x y₁ y₂ : Expr) (req : Request) (es : Entities)
    (h : evaluate y₁ req es = evaluate y₂ req es) :
    evaluate (.and x y₁) req es = evaluate (.and x y₂) req es := by
  simp only [evaluate, h]

/-- The generic single-permit policy record parameterized by the condition body. -/
def Pbody (body : Expr) : Policy :=
  ⟨"p", .permit, .principalScope .any, .actionScope .any, .resourceScope .any,
    [⟨.when, body⟩]⟩

/-- `evaluate` of the two policies' full `toExpr` agrees whenever the condition
    bodies evaluate identically (the scope prefix `true && true && true && …` is
    shared). -/
theorem eval_toExpr_cong (b₁ b₂ : Expr) (req : Request) (es : Entities)
    (h : evaluate b₁ req es = evaluate b₂ req es) :
    evaluate (Pbody b₁).toExpr req es = evaluate (Pbody b₂).toExpr req es := by
  simp only [Pbody, Policy.toExpr, Conditions.toExpr, Condition.toExpr,
    PrincipalScope.toExpr, ActionScope.toExpr, ResourceScope.toExpr, Scope.toExpr,
    List.reverse, List.reverseAux, List.foldl]
  exact and_cong _ _ _ req es (and_cong _ _ _ req es (and_cong _ _ _ req es h))

/-- If two single-permit policies' conditions evaluate identically, they yield the
    same authorization response. -/
theorem isAuthorized_cong (b₁ b₂ : Expr) (req : Request) (es : Entities)
    (h : evaluate (Pbody b₁).toExpr req es = evaluate (Pbody b₂).toExpr req es) :
    isAuthorized req es [Pbody b₁] = isAuthorized req es [Pbody b₂] := by
  simp only [isAuthorized, satisfiedPolicies, satisfiedWithEffect, satisfied,
    errorPolicies, errored, hasError, List.filterMap, h]
  simp only [Pbody]

/-- `distribThm` is TRUE. -/
theorem distrib : distribThm := by
  intro req es _hwt
  have hpl : policyLeft = [Pbody (.and ea (.or eb ec))] := rfl
  have hpr : policyRight = [Pbody (.or (.and ea eb) (.and ea ec))] := rfl
  rw [hpl, hpr]
  exact isAuthorized_cong _ _ req es
    (eval_toExpr_cong _ _ req es (eval_distrib ea eb ec req es))

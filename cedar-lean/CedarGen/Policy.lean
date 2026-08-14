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

import Cedar.Spec
import Specimen
import CedarGen.Prim
import CedarGen.Expr

/-! Arbitrary instances for Cedar.Spec.Policy and related types -/

namespace CedarGen

open Cedar.Spec
open Plausible

/-! ## Effect -/

instance : Arbitrary Effect where
  arbitrary := Gen.elements [.permit, .forbid] (by decide)

/-! ## Scope -/

instance arbScope : Arbitrary Scope where
  arbitrary :=
    Gen.oneOfWithDefault
      (pure .any)
      [ (do return .eq (← Arbitrary.arbitrary)),
        (do return .mem (← Arbitrary.arbitrary)),
        (do return .is (← Arbitrary.arbitrary)),
        (do
          let ety ← Arbitrary.arbitrary
          let uid ← Arbitrary.arbitrary
          return .isMem ety uid) ]

/-! ## PrincipalScope / ResourceScope / ActionScope -/

instance : Arbitrary PrincipalScope where
  arbitrary := do return .principalScope (← arbScope.arbitrary)

instance : Arbitrary ResourceScope where
  arbitrary := do return .resourceScope (← arbScope.arbitrary)

instance : Arbitrary ActionScope where
  arbitrary :=
    Gen.oneOfWithDefault
      (do return .actionScope (← arbScope.arbitrary))
      [ (do
          let ⟨len, _⟩ ← Gen.choose Nat 1 4 (by omega)
          let mut uids : List EntityUID := []
          for _ in List.range len do
            uids := (← Arbitrary.arbitrary) :: uids
          return .actionInAny uids) ]

/-! ## ConditionKind / Condition -/

instance : Arbitrary ConditionKind where
  arbitrary := Gen.elements [.when, .unless] (by decide)

instance : Arbitrary Condition where
  arbitrary := do
    let kind ← Arbitrary.arbitrary
    let body ← Arbitrary.arbitrary (α := Expr)
    return { kind, body }

/-! ## Policy -/

private def genPolicyId : Gen PolicyID := do
  let ⟨n, _⟩ ← Gen.choose Nat 0 99 (by omega)
  return s!"policy{n}"

instance : Arbitrary Policy where
  arbitrary := do
    let id ← genPolicyId
    let effect ← Arbitrary.arbitrary
    let principalScope ← Arbitrary.arbitrary
    let actionScope ← Arbitrary.arbitrary
    let resourceScope ← Arbitrary.arbitrary
    let ⟨numConditions, _⟩ ← Gen.choose Nat 0 3 (by omega)
    let mut conditions : List Condition := []
    for _ in List.range numConditions do
      conditions := (← Arbitrary.arbitrary) :: conditions
    return {
      id
      effect
      principalScope
      actionScope
      resourceScope
      condition := conditions
    }

end CedarGen

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
import CedarGen.ExtFun

/-! Arbitrary instances for Cedar.Spec.Expr and its sub-types -/

namespace CedarGen

open Cedar.Spec
open Cedar.Data
open Plausible

/-! ## Wildcard / Pattern -/

instance : Arbitrary PatElem where
  arbitrary :=
    Gen.oneOfWithDefault
      (pure .star)
      [ (do
          let c ← Gen.elements ['a', 'b', 'c', '*', '?', '.'] (by decide)
          return .justChar c) ]

instance arbPattern : Arbitrary Cedar.Spec.Pattern where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 5 (by omega)
    let mut pat : List PatElem := []
    for _ in List.range len do
      pat := (← Arbitrary.arbitrary (α := PatElem)) :: pat
    return pat

/-! ## UnaryOp -/

instance : Arbitrary UnaryOp where
  arbitrary :=
    Gen.oneOfWithDefault
      (pure .not)
      [ pure .neg,
        pure .isEmpty,
        (do return .like (← arbPattern.arbitrary)),
        (do return .is (← Arbitrary.arbitrary (α := EntityType))) ]

/-! ## BinaryOp -/

instance : Arbitrary BinaryOp where
  arbitrary := Gen.elements
    [ .eq, .mem, .hasTag, .getTag, .less, .lessEq,
      .add, .sub, .mul, .contains, .containsAll, .containsAny ]
    (by decide)

/-! ## Expr

Expr is recursive. We use explicit fuel to bound depth.
The generation is weighted: leaves (lit, var) are more likely at lower fuel.
-/

private partial def genExpr (fuel : Nat) : Gen Expr := do
  if fuel = 0 then
    Gen.oneOfWithDefault
      (do return .lit (← Arbitrary.arbitrary))
      [ (do return .var (← Arbitrary.arbitrary)) ]
  else
    let ⟨choice, _⟩ ← Gen.choose Nat 0 19 (by omega)
    match choice with
    -- Leaves (higher probability)
    | 0 | 1 | 2 | 3 => return .lit (← Arbitrary.arbitrary)
    | 4 | 5 => return .var (← Arbitrary.arbitrary)
    -- Unary
    | 6 => do
      let op ← Arbitrary.arbitrary
      let e ← genExpr (fuel - 1)
      return .unaryApp op e
    -- Binary
    | 7 | 8 => do
      let op ← Arbitrary.arbitrary
      let a ← genExpr (fuel - 1)
      let b ← genExpr (fuel - 1)
      return .binaryApp op a b
    -- ite
    | 9 => do
      let c ← genExpr (fuel - 1)
      let t ← genExpr (fuel - 1)
      let e ← genExpr (fuel - 1)
      return .ite c t e
    -- and / or
    | 10 => do
      let a ← genExpr (fuel - 1)
      let b ← genExpr (fuel - 1)
      return .and a b
    | 11 => do
      let a ← genExpr (fuel - 1)
      let b ← genExpr (fuel - 1)
      return .or a b
    -- getAttr / hasAttr
    | 12 => do
      let e ← genExpr (fuel - 1)
      let attr ← Arbitrary.arbitrary (α := String)
      return .getAttr e attr
    | 13 => do
      let e ← genExpr (fuel - 1)
      let attr ← Arbitrary.arbitrary (α := String)
      return .hasAttr e attr
    -- set
    | 14 | 15 => do
      let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
      let mut elems : List Expr := []
      for _ in List.range len do
        elems := (← genExpr (fuel - 1)) :: elems
      return .set elems
    -- record
    | 16 | 17 => do
      let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
      let mut pairs : List (Attr × Expr) := []
      for _ in List.range len do
        let k ← Arbitrary.arbitrary (α := String)
        let v ← genExpr (fuel - 1)
        pairs := (k, v) :: pairs
      return .record pairs
    -- call (extension function)
    | 18 => do
      let xfn ← Arbitrary.arbitrary (α := ExtFun)
      let ⟨nargs, _⟩ ← Gen.choose Nat 1 3 (by omega)
      let mut args : List Expr := []
      for _ in List.range nargs do
        args := (← genExpr (fuel - 1)) :: args
      return .call xfn args
    -- fallback
    | _ => return .lit (← Arbitrary.arbitrary)

instance : Arbitrary Expr where
  arbitrary := genExpr 4

end CedarGen

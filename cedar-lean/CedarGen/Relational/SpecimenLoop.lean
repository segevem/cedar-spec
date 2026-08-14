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

import CedarGen.Relational.RequestEntities
import Specimen

/-! # Support module for using `specimen` in __INTERNAL_ANALYZER__'s `--prove` loop

A deep-backend scratch file `import`s this module to make the `specimen` tactic
usable on Cedar authorization goals. It bundles, in one importable place:

* the `Arbitrary` / `Enum` / `Shrinkable` instances Specimen needs for the
  `Cedar.Spec` value types (`Request`, `Entities`, `Value`, …), and
* (transitively, via `CedarGen.Relational.RequestEntities`) the
  `WellTypedRequestAndEntities` relation whose derived generator samples
  *well-typed* `(req, es)` pairs.

Instances propagate through `import`; the `set_option`s that `specimen` needs
(`match.ignoreUnusedAlts`, `specimen.autoDeriveDeps`, `specimen.multiOutput`) do
**not**, so `prove.rs` splices those into the scratch file itself.

`WellTypedRequestAndEntities` is re-exported (its namespace is opened by the
scratch preamble) so the agent can write, e.g.,
`have h : ∀ req es, WellTypedRequestAndEntities env req es → … := by specimen`.
-/

open Cedar.Spec Cedar.Data Cedar.Validation Plausible

/-! ## Arbitrary / Enum instances for `Map` (element instances derived below) -/

instance [Arbitrary α] [Arbitrary β] [LT α] [DecidableLT α] : Arbitrary (Map α β) where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 3 (by omega)
    let mut pairs : List (α × β) := []
    for _ in List.range len do
      pairs := (← Arbitrary.arbitrary, ← Arbitrary.arbitrary) :: pairs
    return Map.make pairs

instance [Enum α] [Enum β] [LT α] [DecidableLT α] : Enum (Map α β) where
  enum := do let pairs ← Enum.enum (α := List (α × β)); return Map.make pairs

deriving instance Plausible.Arbitrary for Attr
deriving instance Plausible.Arbitrary for
  Var, ExtFun, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
  Qualified, CedarType

deriving instance Enum for
  Var, ExtFun, UInt64, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp,
  Qualified
deriving instance Enum for EntityType

deriving instance Shrinkable for Name, EntityUID
deriving instance Shrinkable for Map, Int64, Prim, Set
deriving instance Shrinkable for Ext.IPAddr.IPNetAddr
deriving instance Shrinkable for Ext.IPAddr.CIDR
deriving instance Shrinkable for Ext.IPAddr.IPNet, Ext.Datetime, Ext.Datetime.Duration
deriving instance Shrinkable for Duration
deriving instance Shrinkable for Ext
deriving instance Shrinkable for Value
deriving instance Shrinkable for Request
deriving instance Shrinkable for EntityData
deriving instance Shrinkable for Entities

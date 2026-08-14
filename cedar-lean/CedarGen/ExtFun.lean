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

/-! Arbitrary instances for Cedar extension types and extension functions -/

namespace CedarGen

open Cedar.Spec
open Cedar.Spec.Ext
open Plausible

/-! ## Extension Functions -/

instance : Arbitrary ExtFun where
  arbitrary := Gen.elements
    [ .decimal, .lessThan, .lessThanOrEqual, .greaterThan, .greaterThanOrEqual,
      .ip, .isIpv4, .isIpv6, .isLoopback, .isMulticast, .isInRange,
      .datetime, .duration, .offset, .durationSince,
      .toDate, .toTime, .toMilliseconds, .toSeconds, .toMinutes, .toHours, .toDays ]
    (by decide)

/-! ## Ext.Decimal (alias for Int64) -/

instance arbDecimal : Arbitrary Ext.Decimal where
  arbitrary := do
    let ⟨i, _⟩ ← Gen.choose Int (-10000_0000) 10000_0000 (by omega)
    return Int64.ofInt i

/-! ## Ext.IPAddr -/

private def genIPv4Addr : Gen Ext.IPAddr.IPv4Addr := do
  let ⟨bits, _⟩ ← Gen.choose Nat 0 (2^32 - 1) (by omega)
  return BitVec.ofNat _ bits

private def genIPv6Addr : Gen Ext.IPAddr.IPv6Addr := do
  let ⟨bits, _⟩ ← Gen.choose Nat 0 (2^128 - 1) (by omega)
  return BitVec.ofNat _ bits

private def genIPv4Prefix : Gen Ext.IPAddr.IPv4Prefix := do
  let usePrefix ← Gen.chooseAny Bool
  if usePrefix then
    let ⟨p, _⟩ ← Gen.choose Nat 0 32 (by omega)
    return some (BitVec.ofNat _ p)
  else
    return none

private def genIPv6Prefix : Gen Ext.IPAddr.IPv6Prefix := do
  let usePrefix ← Gen.chooseAny Bool
  if usePrefix then
    let ⟨p, _⟩ ← Gen.choose Nat 0 128 (by omega)
    return some (BitVec.ofNat _ p)
  else
    return none

instance : Arbitrary Ext.IPAddr.IPNet where
  arbitrary := do
    let useV4 ← Gen.chooseAny Bool
    if useV4 then
      let addr ← genIPv4Addr
      let pfx ← genIPv4Prefix
      return .V4 ⟨addr, pfx⟩
    else
      let addr ← genIPv6Addr
      let pfx ← genIPv6Prefix
      return .V6 ⟨addr, pfx⟩

/-! ## Ext.Datetime and Duration -/

instance : Arbitrary Ext.Datetime where
  arbitrary := do
    let ⟨ms, _⟩ ← Gen.choose Int 0 253402300799999 (by omega)
    return ⟨Int64.ofInt ms⟩

instance : Arbitrary Ext.Datetime.Duration where
  arbitrary := do
    let ⟨ms, _⟩ ← Gen.choose Int (-86400000) 86400000 (by omega)
    return ⟨Int64.ofInt ms⟩

/-! ## Ext (the sum type) -/

instance : Arbitrary Ext where
  arbitrary :=
    Gen.oneOfWithDefault
      (do return .decimal (← arbDecimal.arbitrary))
      [ (do return .ipaddr (← Arbitrary.arbitrary)),
        (do return .datetime (← Arbitrary.arbitrary)),
        (do return .duration (← Arbitrary.arbitrary)) ]

end CedarGen

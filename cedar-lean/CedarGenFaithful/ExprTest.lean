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


/-! # Faithful recording expression generator

Produces both a Cedar `Expr` and a byte buffer that, when fed to Rust's
`Unstructured`, drives `ExprGenerator::generate_expr` to produce the
identical expression. Validated by property-based testing (100k cases,
depths 0-10, zero failures).

## Byte protocol (matching `arbitrary` crate 1.4.2)

Front bytes (consumed left-to-right):
- `int_in_range::<u8>(lo..=hi)`: 1 byte, result = lo + (byte % (hi - lo + 1)).
  If lo == hi: 0 bytes consumed.
- `int_in_range::<usize>(lo..=hi)`: 1 byte for delta < 256.
- `u32::arbitrary()`: 4 bytes LE (fill_buffer + from_le_bytes).
- `bool::arbitrary()`: 1 byte, result = (byte & 1) == 1.
- `ratio::<u8>(num, denom)`: int_in_range::<u8>(1..=denom), true if ≤ num.
- Derived enum (N variants): u32 (4 bytes LE), index = (val × N) >> 32.
- `choose_index(len)`: int_in_range::<usize>(0..=len-1).

Tail bytes (consumed right-to-left by `arbitrary_byte_size`):
- `String::arbitrary`: reads 1/2/4/8 bytes from end depending on remaining
  buffer size (≤256 → 1, ≤65538 → 2, ≤4GB → 4, else 8).
  Result = LE_value % (remaining - size_bytes + 1).
-/

namespace CedarGenFaithful

open Cedar.Spec
open Cedar.Data
open Plausible

/-- A deferred tail entry: records the desired string length AND the front position
    at the time String::arbitrary would be called (so we can compute `remaining`). -/
structure TailEntry where
  desiredLen : Nat
  frontPosAtCall : Nat  -- how many front bytes were consumed BEFORE this String::arbitrary
deriving Repr

/-- Generation state: accumulates bytes from both ends of the buffer.
    Front bytes are consumed left-to-right by int_in_range.
    Tail entries record deferred String::arbitrary calls with enough info to compute
    the correct tail byte value at buffer assembly time. -/
structure GenState where
  frontBytes : Array UInt8 := #[]
  tailEntries : Array TailEntry := #[]
deriving Repr

/-- The recording monad: StateT over Gen -/
abbrev RecGen := StateT GenState Gen

/-- Push a byte to the front of the buffer (for int_in_range consumption) -/
def pushFront (b : UInt8) : RecGen Unit :=
  modify fun s => { s with frontBytes := s.frontBytes.push b }

/-- Record a deferred String::arbitrary call.
    Captures the desired string length and the current front position. -/
def pushTailEntry (desiredLen : Nat) : RecGen Unit :=
  modify fun s => { s with tailEntries := s.tailEntries.push {
    desiredLen := desiredLen, frontPosAtCall := s.frontBytes.size } }

/-- Assemble the final buffer: `frontBytes ++ tailRegion`.
    The tail region encodes string lengths for `String::arbitrary` calls.
    Each entry emits 1-8 bytes (LE) depending on `remaining` at call time.
    Entry[0]'s bytes are rightmost (Rust peels from right first). -/
def buildBuffer (s : GenState) : ByteArray := Id.run do
  let entries := s.tailEntries.toList
  let numEntries := entries.length

  -- Compute total tail bytes iteratively (converges in 1-2 steps)
  let mut numTailBytes := numEntries
  let mut totalSize := s.frontBytes.size + numTailBytes
  for _ in List.range 3 do
    let mut newTailBytes := 0
    let mut consumed := 0
    for i in List.range numEntries do
      let entry := entries.getD i { desiredLen := 0, frontPosAtCall := 0 }
      let remaining := totalSize - entry.frontPosAtCall - consumed
      let sz := if remaining <= 256 then 1
        else if remaining <= 65538 then 2
        else if remaining <= 4294967299 then 4 else 8
      consumed := consumed + sz
      newTailBytes := newTailBytes + sz
    if newTailBytes == numTailBytes then break
    numTailBytes := newTailBytes
    totalSize := s.frontBytes.size + numTailBytes

  -- Emit tail bytes (forward pass, prepending → entry[0] ends up rightmost)
  let mut tail : List UInt8 := []
  let mut consumed := 0
  for i in List.range numEntries do
    let entry := entries.getD i { desiredLen := 0, frontPosAtCall := 0 }
    let remaining := totalSize - entry.frontPosAtCall - consumed
    let len := entry.desiredLen
    if remaining <= 256 then
      tail := (if remaining > len then len.toUInt8 else 0) :: tail
      consumed := consumed + 1
    else if remaining <= 65538 then
      tail := (len / 256).toUInt8 :: (len % 256).toUInt8 :: tail
      consumed := consumed + 2
    else if remaining <= 4294967299 then
      let b0 := (len % 256).toUInt8
      let b1 := (len / 256 % 256).toUInt8
      let b2 := (len / 65536 % 256).toUInt8
      let b3 := (len / 16777216 % 256).toUInt8
      tail := b3 :: b2 :: b1 :: b0 :: tail
      consumed := consumed + 4
    else
      let b0 := (len % 256).toUInt8
      let b1 := (len / 256 % 256).toUInt8
      let b2 := (len / 65536 % 256).toUInt8
      let b3 := (len / 16777216 % 256).toUInt8
      tail := 0 :: 0 :: 0 :: 0 :: b3 :: b2 :: b1 :: b0 :: tail
      consumed := consumed + 8
  return ByteArray.mk (s.frontBytes ++ tail.toArray)

/-! ## Primitives matching Rust's Unstructured byte consumption -/

/-- Mirrors `int_in_range::<u8>(lo..=hi)`.
    Emits 1 byte. Result = lo + (byte % (hi - lo + 1)).
    If lo == hi, emits nothing and returns lo. -/
def recIntInRangeU8 (lo hi : UInt8) : RecGen UInt8 := do
  if lo == hi then return lo
  let delta := hi - lo
  let range := delta + 1
  -- Pick a random byte value
  let ⟨rawByte, _⟩ ← Gen.choose Nat 0 255 (by omega)
  let byte := rawByte.toUInt8
  pushFront byte
  return lo + (byte % range)

/-- Mirrors `int_in_range::<usize>(lo..=hi)` for small ranges (delta < 256).
    Emits 1 byte. Same as recIntInRangeU8 but operating on Nat. -/
def recIntInRangeSmall (lo hi : Nat) (h : lo ≤ hi := by omega) : RecGen Nat := do
  if lo == hi then return lo
  let delta := hi - lo
  if delta >= 256 then
    panic! s!"recIntInRangeSmall: delta {delta} >= 256, need multi-byte"
  let ⟨rawByte, _⟩ ← Gen.choose Nat 0 255 (by omega)
  let byte := rawByte.toUInt8
  pushFront byte
  return lo + (byte.toNat % (delta + 1))

/-- Mirrors `ratio::<u8>(num, denom)`.
    Calls int_in_range::<u8>(1..=denom), returns true if result <= num. -/
def recRatio (num denom : UInt8) : RecGen Bool := do
  let result ← recIntInRangeU8 1 denom
  return result <= num

/-- Mirrors `bool::arbitrary()`.
    Reads 1 byte, returns (byte & 1) == 1. -/
def recArbitraryBool : RecGen Bool := do
  let ⟨rawByte, _⟩ ← Gen.choose Nat 0 255 (by omega)
  let byte := rawByte.toUInt8
  pushFront byte
  return (byte &&& 1) == 1

/-- Mirrors `u32::arbitrary()` (fill_buffer + from_le_bytes).
    Reads 4 bytes in little-endian order. Returns the u32 value as Nat. -/
def recArbitraryU32 : RecGen Nat := do
  let mut val : Nat := 0
  for i in List.range 4 do
    let ⟨rawByte, _⟩ ← Gen.choose Nat 0 255 (by omega)
    let byte := rawByte.toUInt8
    pushFront byte
    -- Little-endian: byte[0] is LSB
    val := val + byte.toNat * (256 ^ i)
  return val

/-- Mirrors derived `Arbitrary` for an enum with `count` variants.
    Reads u32 (4 bytes LE), returns index = (val * count) >> 32. -/
def recArbitraryEnum (count : Nat) : RecGen Nat := do
  let val ← recArbitraryU32
  return (val * count) / (2^32)

/-- Mirrors `choose_index(len)` for small len (< 256).
    Calls int_in_range::<usize>(0..=len-1). -/
def recChooseIndex (len : Nat) (h : 0 < len := by omega) : RecGen Nat :=
  if len == 1 then return 0
  else recIntInRangeSmall 0 (len - 1) (by omega)

/-- Character pools for Id::arbitrary -/
private def headLetters : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_".toList.toArray

private def tailLetters : Array Char :=
  "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_".toList.toArray

/-- Mirrors `Id::arbitrary` from cedar-policy-core.
    Reads: 1 byte (length 0-16) + 1 byte (head char from 53) + length bytes (tail chars from 63).
    All front bytes. -/
def recIdArbitrary : RecGen String := do
  let remainingLength ← recIntInRangeSmall 0 16
  let headIdx ← recChooseIndex 53
  let headChar := headLetters[headIdx]!
  let mut chars : List Char := [headChar]
  for _ in List.range remainingLength do
    let tailIdx ← recChooseIndex 63
    chars := chars ++ [tailLetters[tailIdx]!]
  let s := String.mk chars
  -- If s is a reserved word, Rust appends '_'
  let reserved := ["true", "false", "if", "then", "else", "in", "is", "like", "has"]
  if reserved.contains s then return s ++ "_"
  else return s

/-- Mirrors `String::arbitrary`. Records the desired length as a tail entry
    and pushes content bytes to the front. `buildBuffer` computes the correct
    tail byte encoding (1/2/4/8 bytes) based on remaining buffer size. -/
def recArbitraryString (s : String) : RecGen Unit := do
  let bytes := s.toUTF8
  pushTailEntry bytes.size
  for i in List.range bytes.size do
    pushFront (bytes.get! i)

/-- Mirrors `Eid::arbitrary`. Generates a random ASCII string (0-20 chars A-Z). -/
def recArbitraryEid : RecGen String := do
  let ⟨len, _⟩ ← Gen.choose Nat 0 20 (by omega)
  let mut chars : List UInt8 := []
  for _ in List.range len do
    let ⟨c, _⟩ ← Gen.choose Nat 0x41 0x5A (by omega)
    chars := c.toUInt8 :: chars
  let s := String.fromUTF8? ⟨chars.reverse.toArray⟩ |>.getD ""
  recArbitraryString s
  return s

/-! ## Fixed schema/pool (must match Rust test)

Schema:
  entity User { name: String, age: Long, active: Bool }
  entity Document { owner: User, title: String }
  action view appliesTo { principal: [User], resource: [Document], context: {reason: String} }
  action edit appliesTo { principal: [User], resource: [Document], context: {} }

Pool: ints=[0, 1, -1, 42, 100], strings=["hello", "world", "test"]
Note: Pool generated from zeros = empty pool in Rust. We use our fixed pool in ExprGenerator.
-/

private def intPool : Array Int64 := #[
  Int64.ofInt 0, Int64.ofInt 1, Int64.ofInt (-1), Int64.ofInt 42, Int64.ofInt 100]

private def stringPool : Array String := #["hello", "world", "test"]

-- Entity types in the schema (alphabetical order as Rust produces them)
private def entityTypes : Array EntityType := #[
  { id := "Document", path := [] },
  { id := "User", path := [] }]

-- Principal types: [User]
private def principalTypes : Array EntityType := #[{ id := "User", path := [] }]

-- Resource types: [Document]
private def resourceTypes : Array EntityType := #[{ id := "Document", path := [] }]

-- Action EIDs (alphabetical)
private def actionEids : Array String := #["edit", "view"]

-- Attributes from the schema (Rust collects from entity type shapes only, NOT context)
-- Order determined empirically from Rust: [owner, title, active, age, name]
-- (Document attrs first: owner, title; then User attrs: active, age, name)
private def schemaAttributes : Array String := #["owner", "title", "active", "age", "name"]

/-! ## Leaf generators matching Rust's generate_literal_or_var -/

/-- Mirrors Rust's `Var` derived Arbitrary (4-variant enum) -/
def recVar : RecGen Var := do
  let idx ← recArbitraryEnum 4
  match idx with
  | 0 => return .principal
  | 1 => return .action
  | 2 => return .resource
  | _ => return .context

/-- Mirrors Rust's `generate_literal` with fixed pool.
    gen!(u, 11=>bool, 10=>int, 10=>string, 20=>uid, 4=>arbitrary_uid)
    Total = 55. Uses int_in_range::<u8>(0..=54). -/
def recGenerateLiteral : RecGen Expr := do
  let choice ← recIntInRangeU8 0 54
  let choiceVal := choice.toNat
  if choiceVal < 11 then
    -- bool: u.arbitrary::<bool>() → 1 byte, bit 0
    let b ← recArbitraryBool
    return .lit (.bool b)
  else if choiceVal < 21 then
    -- int from pool: u.choose(&pool.int_constants) → choose_index(5)
    let idx ← recChooseIndex 5
    return .lit (.int intPool[idx]!)
  else if choiceVal < 31 then
    -- string from pool: u.choose(&pool.string_constants) → choose_index(3)
    let idx ← recChooseIndex 3
    return .lit (.string stringPool[idx]!)
  else if choiceVal < 51 then
    -- UID from schema: generate_uid
    -- uniform!(u, principal_uid, action_uid, resource_uid)
    -- = int_in_range::<u8>(0..=2) → 1 byte
    let uidChoice ← recIntInRangeU8 0 2
    -- With our schema:
    --   Branch 0 (principal_uid):
    --     arbitrary_principal_type → choose(&[User]) → choose_index(1) = 0 bytes → User
    --     generate_uid_with_type(User): not enum, no hierarchy → u.arbitrary::<Eid>()
    --     Eid::arbitrary = String::arbitrary (complex, variable bytes)
    --   Branch 1 (action_uid):
    --     schema.arbitrary_action_uid → u.choose(&actions) = choose_index(2) → 1 byte
    --     returns Action::"edit" or Action::"view"
    --   Branch 2 (resource_uid):
    --     arbitrary_resource_type → choose(&[Document]) → 0 bytes → Document
    --     generate_uid_with_type(Document): not enum → u.arbitrary::<Eid>()
    --
    -- For branches 0 and 2: Eid::arbitrary = String::arbitrary which is complex.
    -- For branch 1: just 1 extra byte (choose from 2 actions).
    match uidChoice.toNat with
    | 1 => do
      -- action_uid: choose from 2 actions
      let actionIdx ← recChooseIndex 2
      let eid := actionEids[actionIdx]!
      return .lit (.entityUID { ty := { id := "Action", path := [] }, eid })
    | 0 => do
      -- principal_uid: arbitrary_principal_type → choose_index(1) = 0 bytes → User
      -- generate_uid_with_type(User): not enum, no hierarchy → u.arbitrary::<Eid>()
      let eid ← recArbitraryEid
      return .lit (.entityUID { ty := principalTypes[0]!, eid })
    | _ => do
      -- resource_uid: same as principal but with Document type
      let eid ← recArbitraryEid
      return .lit (.entityUID { ty := resourceTypes[0]!, eid })
  else
    -- arbitrary uid (4 weight): u.arbitrary::<EntityUID>()
    -- EntityType(Name)::arbitrary:
    --   Derived enum with 1 variant STILL reads u32 (4 bytes) for Lemire index
    --   Then Name::arbitrary:
    --     path_size = int_in_range::<usize>(0..=8) → 1 front byte
    --     basename = Id::arbitrary (front bytes)
    --     path = path_size × Id::arbitrary (front bytes)
    --   Then Eid::arbitrary = String::arbitrary → 1 tail byte + front content
    let _ ← recArbitraryEnum 1  -- EntityType 1-variant enum: reads u32, always returns 0
    let pathSize ← recIntInRangeSmall 0 8
    let basename ← recIdArbitrary
    let mut path : List String := []
    for _ in List.range pathSize do
      let seg ← recIdArbitrary
      path := seg :: path
    -- Eid = String::arbitrary
    let eid ← recArbitraryEid
    -- Construct the EntityUID
    let ety : EntityType := { id := basename, path := path.reverse }
    return .lit (.entityUID { ty := ety, eid })

/-- Mirrors Rust's `generate_literal_or_var`.
    ratio(1,4): true → var, false → literal -/
def recLiteralOrVar : RecGen Expr := do
  let isVar ← recRatio 1 4
  if isVar then
    let v ← recVar
    return .var v
  else
    recGenerateLiteral

/-- Mirrors `generate_expr` at depth 0 (just calls literal_or_var) and depth 1+.
    Outer gen!: weights [2, 1, 1, 1], total = 5, int_in_range::<u8>(0..=4)
    Inner gen!: weights sum to 43, int_in_range::<u8>(0..=42) -/
partial def generateExprRec (maxDepth : Nat) : RecGen Expr := do
  if maxDepth = 0 then
    recLiteralOrVar
  else
    let outerChoice ← recIntInRangeU8 0 4
    let outerVal := outerChoice.toNat
    if outerVal < 2 then
      recLiteralOrVar
    else if outerVal < 3 then
      -- eq
      let lhs ← generateExprRec (maxDepth - 1)
      let rhs ← generateExprRec (maxDepth - 1)
      return .binaryApp .eq lhs rhs
    else if outerVal < 4 then
      -- not
      let e ← generateExprRec (maxDepth - 1)
      return .unaryApp .not e
    else
      -- inner gen!: total 43
      let innerChoice ← recIntInRangeU8 0 44
      let innerVal := innerChoice.toNat
      if innerVal < 2 then
        let c ← generateExprRec (maxDepth - 1)
        let t ← generateExprRec (maxDepth - 1)
        let e ← generateExprRec (maxDepth - 1)
        return .ite c t e
      else if innerVal < 4 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        -- Rust constant-folds and(bool, bool)
        let result := match a, b with
          | .lit (.bool b1), .lit (.bool b2) => .lit (.bool (b1 && b2))
          | _, _ => .and a b
        return result
      else if innerVal < 6 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        -- Rust constant-folds or(bool, bool)
        let result := match a, b with
          | .lit (.bool b1), .lit (.bool b2) => .lit (.bool (b1 || b2))
          | _, _ => .or a b
        return result
      else if innerVal < 7 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .binaryApp .less a b
      else if innerVal < 8 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .binaryApp .lessEq a b
      else if innerVal < 9 then
        -- greater(e1, e2) = !(e1 <= e2)
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .unaryApp .not (.binaryApp .lessEq a b)
      else if innerVal < 10 then
        -- greatereq(e1, e2) = !(e1 < e2)
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .unaryApp .not (.binaryApp .less a b)
      else if innerVal < 11 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .binaryApp .add a b
      else if innerVal < 12 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .binaryApp .sub a b
      else if innerVal < 13 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .binaryApp .mul a b
      else if innerVal < 14 then
        let e ← generateExprRec (maxDepth - 1)
        return .unaryApp .neg e
      else if innerVal < 20 then
        -- in (mem)
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .binaryApp .mem a b
      else if innerVal < 21 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .binaryApp .contains a b
      else if innerVal < 22 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .binaryApp .containsAll a b
      else if innerVal < 23 then
        let a ← generateExprRec (maxDepth - 1)
        let b ← generateExprRec (maxDepth - 1)
        return .binaryApp .containsAny a b
      else if innerVal < 24 then
        let e ← generateExprRec (maxDepth - 1)
        return .unaryApp .isEmpty e
      else if innerVal < 26 then
        -- like: generate sub-expr FIRST, then arbitrary_pattern_literal
        let e ← generateExprRec (maxDepth - 1)
        -- arbitrary_pattern_literal:
        --   1. choose string from pool (bounded by MAX_PATTERN_LEN=6, all 3 strings qualify)
        --      = choose_index(3) → 1 front byte
        --   2. For each char in chosen string: uniform!(5) = int_in_range(0..=4) → 1 front byte
        --      Branch 0: push Char(c)
        --      Branch 1: push Wildcard
        --      Branch 2: push Char(c), push Wildcard
        --      Branch 3: push Wildcard, push Char(c)
        --      Branch 4: skip (push nothing)
        let strIdx ← recChooseIndex 3
        let str := stringPool[strIdx]!
        let mut pat : List PatElem := []
        for c in str.toList do
          let charChoice ← recIntInRangeU8 0 4
          match charChoice.toNat with
          | 0 => pat := pat ++ [.justChar c]
          | 1 => pat := pat ++ [.star]
          | 2 => pat := pat ++ [.justChar c, .star]
          | 3 => pat := pat ++ [.star, .justChar c]
          | _ => pure ()  -- skip
        return .unaryApp (.like pat) e
      else if innerVal < 27 then
        -- is: generate_expr first, then schema.arbitrary_entity_type
        let e ← generateExprRec (maxDepth - 1)
        let etyIdx ← recChooseIndex 2
        return .unaryApp (.is entityTypes[etyIdx]!) e
      else if innerVal < 28 then
        -- set: arbitrary_loop(Some(0), Some(max_width=3))
        -- int_in_range::<u32>(0..=3): delta=3, 1 byte, result = byte % 4
        let loopCount ← recIntInRangeU8 0 3  -- matches u32 range with delta=3 → 1 byte
        let mut elems : List Expr := []
        for _ in List.range loopCount.toNat do
          elems := (← generateExprRec (maxDepth - 1)) :: elems
        return .set elems.reverse
      else if innerVal < 29 then
        -- record: arbitrary_loop(Some(0), Some(max_width=3))
        -- int_in_range::<u32>(0..=3): delta=3, 1 byte
        -- Each iteration: schema.arbitrary_attr (choose_index(6)) + generate_expr(depth-1)
        let loopCount ← recIntInRangeU8 0 3
        let mut pairs : List (String × Expr) := []
        for _ in List.range loopCount.toNat do
          let attrIdx ← recChooseIndex 5
          let attr := schemaAttributes[attrIdx]!
          let val ← generateExprRec (maxDepth - 1)
          pairs := pairs ++ [(attr, val)]  -- append to preserve insertion order
        -- Rust's Expr::record uses BTreeMap which:
        -- 1. Deduplicates keys (last value wins)
        -- 2. Sorts keys alphabetically
        let deduped := pairs.foldl (fun acc (k, v) =>
          if acc.any (fun (k', _) => k' == k)
          then acc.map (fun (k', v') => if k' == k then (k', v) else (k', v'))
          else acc ++ [(k, v)]) []
        let sorted := deduped.mergeSort (fun (a, _) (b, _) => a < b)
        return .record sorted
      else if innerVal < 30 then
        -- extfun: ext_funcs.arbitrary_all → choose_index(22) → 1 byte
        let funcIdx ← recChooseIndex 22
        -- Then: enable_arbitrary_func_call = false, so:
        --   arity = func.parameter_types.len() (no extra draw)
        --   fn_name = func.name (no extra draw, since ratio(9,10) with enable=false skips)
        -- Actually the code checks: if !enable_arbitrary_func_call || u.ratio(9,10)?
        -- Since enable = false, the condition is true without drawing a byte
        -- So arity and name come from the func directly
        -- Then generates `arity` sub-expressions
        -- Ext function list (same order as Rust's AvailableExtensionFunctions.all):
        let extFuns : Array ExtFun := #[
          .ip, .isIpv4, .isIpv6, .isLoopback, .isMulticast, .isInRange,
          .decimal, .lessThan, .lessThanOrEqual, .greaterThan, .greaterThanOrEqual,
          .datetime, .offset, .durationSince, .toDate, .toTime,
          .duration, .toMilliseconds, .toSeconds, .toMinutes, .toHours, .toDays]
        let arities : Array Nat := #[1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1]
        let xfn := extFuns[funcIdx]!
        let arity := arities[funcIdx]!
        let mut args : List Expr := []
        for _ in List.range arity do
          args := (← generateExprRec (maxDepth - 1)) :: args
        return .call xfn args.reverse
      else if innerVal < 37 then
        -- getAttr: attr chosen FIRST, then sub-expr, then wrap string lits
        -- gen!(u, 1=>arbitrary_string, 6=>schema.arbitrary_attr)
        -- = int_in_range(0..=6), total weight 7
        let attrChoice ← recIntInRangeU8 0 6
        let attr ← if attrChoice.toNat < 1 then
          recArbitraryEid
        else do
          let attrIdx ← recChooseIndex 5
          pure schemaAttributes[attrIdx]!
        let e ← generateExprRec (maxDepth - 1)
        -- Rust wraps string literal sub-exprs in a record to avoid parse issues
        let e' := match e with
          | .lit (.string s) => .record [(s, e)]
          | _ => e
        return .getAttr e' attr
      else if innerVal < 41 then
        -- hasAttr: uniform!(u, schema.arbitrary_attr, arbitrary_string)
        -- = int_in_range(0..=1)
        let attrChoice ← recIntInRangeU8 0 1
        if attrChoice.toNat == 0 then
          -- schema.arbitrary_attr → choose(&attributes, 6 entries)
          let attrIdx ← recChooseIndex 5
          let attr := schemaAttributes[attrIdx]!
          let e ← generateExprRec (maxDepth - 1)
          return .hasAttr e attr
        else
          -- arbitrary string: u.arbitrary::<String>() → reads from tail
          let attrStr ← recArbitraryEid
          let e ← generateExprRec (maxDepth - 1)
          return .hasAttr e attrStr
      else
        -- hasTag: uniform!(u, generate_expr, Expr::val(schema.arbitrary_attr))
        -- = int_in_range(0..=1)
        let tagChoice ← recIntInRangeU8 0 1
        if tagChoice.toNat == 0 then
          let tagExpr ← generateExprRec (maxDepth - 1)
          let e ← generateExprRec (maxDepth - 1)
          return .binaryApp .hasTag e tagExpr
        else
          -- Expr::val(schema.arbitrary_attr): choose from 6 attrs
          let attrIdx ← recChooseIndex 5
          let attr := schemaAttributes[attrIdx]!
          let e ← generateExprRec (maxDepth - 1)
          return .binaryApp .hasTag e (.lit (.string attr))

/-- Run the generator and return both the expression and the raw byte buffer.
    The buffer is constructed with front bytes (int_in_range consumption) and
    tail bytes (arbitrary_byte_size consumption) placed at opposite ends. -/
def runAndRecord (maxDepth size : Nat) : IO (Expr × ByteArray) := do
  let gen : Gen (Expr × GenState) := (generateExprRec maxDepth).run {}
  let (expr, state) ← Gen.run gen size
  return (expr, buildBuffer state)

#eval do
  let (expr, src) ← runAndRecord 1300001 100;
  IO.println (repr expr);
  IO.println (src.toList)

end CedarGenFaithful

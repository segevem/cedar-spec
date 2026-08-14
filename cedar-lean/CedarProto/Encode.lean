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
import Cedar.Validation
import CedarProto.Expr

/-! # Protobuf encoding for Cedar Expr

Encodes a `Cedar.Spec.Expr` into a protobuf-encoded `ByteArray` matching
the `cedar_policy_core.Expr` message definition from `core.proto`.

Wire format summary:
- Tag = (fieldNum << 3) | wireType, encoded as varint
- VARINT (0): bool, enum, int32/int64/uint64
- LEN (2): string, bytes, nested messages, repeated fields
- Nested message: tag + varint(length) + payload bytes
- Enum: tag + varint(enumValue)
- String: tag + varint(byteLen) + utf8Bytes
- Map: repeated LEN entries, each with field1=key, field2=value
-/

namespace CedarProto.Encode

open Cedar.Spec
open Cedar.Data

/-! ## Varint encoding -/

partial def encodeVarint (n : UInt64) (buf : ByteArray) : ByteArray :=
  if n < 128 then
    buf.push n.toUInt8
  else
    let byte := (n.toUInt8 &&& 0x7F) ||| 0x80
    encodeVarint (n >>> 7) (buf.push byte)

def encodeVarintNat (n : Nat) (buf : ByteArray) : ByteArray :=
  encodeVarint n.toUInt64 buf

/-! ## Tag encoding -/

def encodeTag (fieldNum : Nat) (wireType : UInt8) (buf : ByteArray) : ByteArray :=
  let tag := (fieldNum.toUInt64 <<< 3) ||| wireType.toUInt64
  encodeVarint tag buf

/-! ## Primitive field encoders -/

def encodeBool (fieldNum : Nat) (b : Bool) (buf : ByteArray) : ByteArray :=
  let buf := encodeTag fieldNum 0 buf
  encodeVarint (if b then 1 else 0) buf

def encodeInt64 (fieldNum : Nat) (i : Int) (buf : ByteArray) : ByteArray :=
  let buf := encodeTag fieldNum 0 buf
  let val : UInt64 := if i >= 0 then i.toNat.toUInt64 else (i + (2^64 : Int)).toNat.toUInt64
  encodeVarint val buf

def encodeEnum (fieldNum : Nat) (val : Nat) (buf : ByteArray) : ByteArray :=
  if val == 0 then buf  -- proto3: default enum value is omitted
  else
    let buf := encodeTag fieldNum 0 buf
    encodeVarintNat val buf

def encodeEnumAlways (fieldNum : Nat) (val : Nat) (buf : ByteArray) : ByteArray :=
  let buf := encodeTag fieldNum 0 buf
  encodeVarintNat val buf

def encodeString (fieldNum : Nat) (s : String) (buf : ByteArray) : ByteArray :=
  if s.isEmpty then buf  -- proto3: empty string is default, omitted
  else
    let bytes := s.toUTF8
    let buf := encodeTag fieldNum 2 buf
    let buf := encodeVarintNat bytes.size buf
    buf ++ bytes

def encodeStringAlways (fieldNum : Nat) (s : String) (buf : ByteArray) : ByteArray :=
  let bytes := s.toUTF8
  let buf := encodeTag fieldNum 2 buf
  let buf := encodeVarintNat bytes.size buf
  buf ++ bytes

def encodeBytes (fieldNum : Nat) (payload : ByteArray) (buf : ByteArray) : ByteArray :=
  let buf := encodeTag fieldNum 2 buf
  let buf := encodeVarintNat payload.size buf
  buf ++ payload

/-! ## Name encoding (message Name { string id = 1; repeated string path = 2; }) -/

def encodeName (n : Cedar.Spec.Name) : ByteArray :=
  let buf := ByteArray.empty
  let buf := encodeStringAlways 1 n.id buf
  n.path.foldl (fun buf p => encodeStringAlways 2 p buf) buf

/-! ## EntityUID encoding (message EntityUid { Name ty = 1; string eid = 2; }) -/

def encodeEntityUID (uid : EntityUID) : ByteArray :=
  let buf := ByteArray.empty
  let nameBuf := encodeName uid.ty
  let buf := encodeBytes 1 nameBuf buf
  encodeStringAlways 2 uid.eid buf

/-! ## Var encoding (enum: Principal=0, Action=1, Resource=2, Context=3) -/

def varToInt : Var → Nat
  | .principal => 0
  | .action => 1
  | .resource => 2
  | .context => 3

/-! ## UnaryOp encoding (enum: Not=0, Neg=1, IsEmpty=2) -/

def unaryOpToInt : UnaryOp → Nat
  | .not => 0
  | .neg => 1
  | .isEmpty => 2
  | .like _ => 0  -- like/is handled separately
  | .is _ => 0

/-! ## BinaryOp encoding (enum: Eq=0..HasTag=11) -/

def binaryOpToInt : BinaryOp → Nat
  | .eq => 0
  | .less => 1
  | .lessEq => 2
  | .add => 3
  | .sub => 4
  | .mul => 5
  | .mem => 6
  | .contains => 7
  | .containsAll => 8
  | .containsAny => 9
  | .getTag => 10
  | .hasTag => 11

/-! ## ExtFun → Name encoding -/

def extFunToName : ExtFun → Cedar.Spec.Name
  | .decimal => { id := "decimal", path := [] }
  | .lessThan => { id := "lessThan", path := [] }
  | .lessThanOrEqual => { id := "lessThanOrEqual", path := [] }
  | .greaterThan => { id := "greaterThan", path := [] }
  | .greaterThanOrEqual => { id := "greaterThanOrEqual", path := [] }
  | .ip => { id := "ip", path := [] }
  | .isIpv4 => { id := "isIpv4", path := [] }
  | .isIpv6 => { id := "isIpv6", path := [] }
  | .isLoopback => { id := "isLoopback", path := [] }
  | .isMulticast => { id := "isMulticast", path := [] }
  | .isInRange => { id := "isInRange", path := [] }
  | .datetime => { id := "datetime", path := [] }
  | .duration => { id := "duration", path := [] }
  | .offset => { id := "offset", path := [] }
  | .durationSince => { id := "durationSince", path := [] }
  | .toDate => { id := "toDate", path := [] }
  | .toTime => { id := "toTime", path := [] }
  | .toMilliseconds => { id := "toMilliseconds", path := [] }
  | .toSeconds => { id := "toSeconds", path := [] }
  | .toMinutes => { id := "toMinutes", path := [] }
  | .toHours => { id := "toHours", path := [] }
  | .toDays => { id := "toDays", path := [] }

/-! ## PatElem encoding
    message PatternElem { oneof data { Wildcard wildcard = 1; string c = 2; } }
    enum Wildcard { unit = 0; }
-/

def encodePatElem (pe : PatElem) : ByteArray :=
  let buf := ByteArray.empty
  match pe with
  | .star =>
    -- field 1 (wildcard enum), varint wire type, value 0
    encodeEnumAlways 1 0 buf
  | .justChar c =>
    encodeStringAlways 2 (String.singleton c) buf

/-! ## Expr encoding (recursive)

message Expr {
  oneof expr_kind {
    Literal lit = 1;    -- message { oneof lit { bool b=1; int64 i=2; string s=3; EntityUid euid=4; } }
    Var var = 2;        -- enum
    SlotId slot = 3;
    If if = 4;          -- message { Expr test=1; Expr then=2; Expr else=3; }
    And and = 5;        -- message { Expr left=1; Expr right=2; }
    Or or = 6;          -- message { Expr left=1; Expr right=2; }
    UnaryApp uApp = 7;  -- message { Op op=1; Expr expr=2; }
    BinaryApp bApp = 8; -- message { Op op=1; Expr left=2; Expr right=3; }
    ExtensionFunctionApp extApp = 9; -- message { Name fn_name=1; repeated Expr args=2; }
    GetAttr getAttr = 10; -- message { Expr expr=1; string attr=2; }
    HasAttr hasAttr = 11; -- message { Expr expr=1; string attr=2; }
    Like like = 12;     -- message { Expr expr=1; repeated PatternElem pattern=2; }
    Is is = 13;         -- message { Expr expr=1; Name entity_type=2; }
    Set set = 14;       -- message { repeated Expr elements=1; }
    Record record = 15; -- message { map<string, Expr> items=1; }
  }
}
-/

partial def encodeExpr (e : Expr) : ByteArray :=
  let buf := ByteArray.empty
  match e with
  | .lit p => encodeLit p buf
  | .var v =>
    -- field 2, varint wire type (enum)
    encodeEnumAlways 2 (varToInt v) buf
  | .ite c t el =>
    let inner := encodeIf c t el
    encodeBytes 4 inner buf
  | .and l r =>
    let inner := encodeAnd l r
    encodeBytes 5 inner buf
  | .or l r =>
    let inner := encodeOr l r
    encodeBytes 6 inner buf
  | .unaryApp (.like pat) sub =>
    let inner := encodeLike sub pat
    encodeBytes 12 inner buf
  | .unaryApp (.is ety) sub =>
    let inner := encodeIs sub ety
    encodeBytes 13 inner buf
  | .unaryApp op sub =>
    let inner := encodeUnaryApp op sub
    encodeBytes 7 inner buf
  | .binaryApp op l r =>
    let inner := encodeBinaryApp op l r
    encodeBytes 8 inner buf
  | .hasAttr sub attr =>
    let inner := encodeHasAttr sub attr
    encodeBytes 11 inner buf
  | .getAttr sub attr =>
    let inner := encodeGetAttr sub attr
    encodeBytes 10 inner buf
  | .set es =>
    let inner := encodeSet es
    encodeBytes 14 inner buf
  | .record pairs =>
    let inner := encodeRecord pairs
    encodeBytes 15 inner buf
  | .call fn args =>
    let inner := encodeExtApp fn args
    encodeBytes 9 inner buf

where
  encodeLit (p : Prim) (buf : ByteArray) : ByteArray :=
    let inner := match p with
      | .bool b =>
        let ibuf := ByteArray.empty
        encodeBool 1 b ibuf
      | .int i =>
        let ibuf := ByteArray.empty
        encodeInt64 2 i.toInt ibuf
      | .string s =>
        let ibuf := ByteArray.empty
        encodeStringAlways 3 s ibuf
      | .entityUID uid =>
        let uidBuf := encodeEntityUID uid
        let ibuf := ByteArray.empty
        encodeBytes 4 uidBuf ibuf
    encodeBytes 1 inner buf

  encodeIf (c t el : Expr) : ByteArray :=
    let buf := ByteArray.empty
    let cBuf := encodeExpr c
    let buf := encodeBytes 1 cBuf buf
    let tBuf := encodeExpr t
    let buf := encodeBytes 2 tBuf buf
    let eBuf := encodeExpr el
    encodeBytes 3 eBuf buf

  encodeAnd (l r : Expr) : ByteArray :=
    let buf := ByteArray.empty
    let lBuf := encodeExpr l
    let buf := encodeBytes 1 lBuf buf
    let rBuf := encodeExpr r
    encodeBytes 2 rBuf buf

  encodeOr (l r : Expr) : ByteArray :=
    let buf := ByteArray.empty
    let lBuf := encodeExpr l
    let buf := encodeBytes 1 lBuf buf
    let rBuf := encodeExpr r
    encodeBytes 2 rBuf buf

  encodeUnaryApp (op : UnaryOp) (sub : Expr) : ByteArray :=
    let buf := ByteArray.empty
    let buf := encodeEnumAlways 1 (unaryOpToInt op) buf
    let sBuf := encodeExpr sub
    encodeBytes 2 sBuf buf

  encodeBinaryApp (op : BinaryOp) (l r : Expr) : ByteArray :=
    let buf := ByteArray.empty
    let buf := encodeEnumAlways 1 (binaryOpToInt op) buf
    let lBuf := encodeExpr l
    let buf := encodeBytes 2 lBuf buf
    let rBuf := encodeExpr r
    encodeBytes 3 rBuf buf

  encodeExtApp (fn : ExtFun) (args : List Expr) : ByteArray :=
    let buf := ByteArray.empty
    let nameBuf := encodeName (extFunToName fn)
    let buf := encodeBytes 1 nameBuf buf
    args.foldl (fun buf arg =>
      let argBuf := encodeExpr arg
      encodeBytes 2 argBuf buf) buf

  encodeGetAttr (sub : Expr) (attr : Attr) : ByteArray :=
    let buf := ByteArray.empty
    let sBuf := encodeExpr sub
    let buf := encodeBytes 1 sBuf buf
    encodeStringAlways 2 attr buf

  encodeHasAttr (sub : Expr) (attr : Attr) : ByteArray :=
    let buf := ByteArray.empty
    let sBuf := encodeExpr sub
    let buf := encodeBytes 1 sBuf buf
    encodeStringAlways 2 attr buf

  encodeLike (sub : Expr) (pat : List PatElem) : ByteArray :=
    let buf := ByteArray.empty
    let sBuf := encodeExpr sub
    let buf := encodeBytes 1 sBuf buf
    pat.foldl (fun buf pe =>
      let peBuf := encodePatElem pe
      encodeBytes 2 peBuf buf) buf

  encodeIs (sub : Expr) (ety : Cedar.Spec.Name) : ByteArray :=
    let buf := ByteArray.empty
    let sBuf := encodeExpr sub
    let buf := encodeBytes 1 sBuf buf
    let nBuf := encodeName ety
    encodeBytes 2 nBuf buf

  encodeSet (es : List Expr) : ByteArray :=
    let buf := ByteArray.empty
    es.foldl (fun buf e =>
      let eBuf := encodeExpr e
      encodeBytes 1 eBuf buf) buf

  encodeRecord (pairs : List (Attr × Expr)) : ByteArray :=
    -- map<string, Expr> items = 1;
    -- Each map entry: tag(1, LEN) + varint(size) + [tag(1,LEN)+key + tag(2,LEN)+value]
    let buf := ByteArray.empty
    pairs.foldl (fun buf (k, v) =>
      let entry := ByteArray.empty
      let entry := encodeStringAlways 1 k entry
      let vBuf := encodeExpr v
      let entry := encodeBytes 2 vBuf entry
      encodeBytes 1 entry buf) buf

/-! ## PolicySet encoding

Wraps an expression into a minimal PolicySet proto:
  PolicySet { templates: [TemplateBody { id: "policy0", effect: Permit(1),
    principal_constraint: { ... }, action_constraint: { ... },
    resource_constraint: { ... }, non_scope_constraints: <expr> }],
    links: [Policy { template_id: "policy0" }] }
-/

def encodePrincipalOrResourceConstraint : ByteArray :=
  -- message PrincipalOrResourceConstraint { oneof constraint { All all = 1; ... } }
  -- All is enum with single value `unit = 0`
  -- field 1 (all), varint wire type, value 0
  let buf := ByteArray.empty
  encodeEnumAlways 1 0 buf

def encodeActionConstraint : ByteArray :=
  -- message ActionConstraint { oneof constraint { All all = 1; ... } }
  let buf := ByteArray.empty
  encodeEnumAlways 1 0 buf

def encodeTemplateBody (policyId : String) (expr : Expr) : ByteArray :=
  let buf := ByteArray.empty
  -- field 1: id (string)
  let buf := encodeStringAlways 1 policyId buf
  -- field 4: effect (enum Effect { Forbid=0, Permit=1 })
  let buf := encodeEnumAlways 4 1 buf  -- Permit
  -- field 5: principal_constraint (message)
  let pcBuf := encodePrincipalOrResourceConstraint
  let buf := encodeBytes 5 pcBuf buf
  -- field 6: action_constraint (message)
  let acBuf := encodeActionConstraint
  let buf := encodeBytes 6 acBuf buf
  -- field 7: resource_constraint (message)
  let rcBuf := encodePrincipalOrResourceConstraint
  let buf := encodeBytes 7 rcBuf buf
  -- field 8: non_scope_constraints (Expr)
  let exprBuf := encodeExpr expr
  encodeBytes 8 exprBuf buf

def encodeLink (policyId : String) : ByteArray :=
  let buf := ByteArray.empty
  -- field 1: template_id (string)
  let buf := encodeStringAlways 1 policyId buf
  -- field 3: is_template_link (bool) = false (static policy)
  -- omit since false is default
  buf

def encodePolicySet (exprs : List Expr) : ByteArray :=
  let buf := ByteArray.empty
  let (buf, _) := exprs.foldl (fun (buf, idx) e =>
    let pid := s!"policy{idx}"
    -- field 1: templates (repeated TemplateBody)
    let tBuf := encodeTemplateBody pid e
    let buf := encodeBytes 1 tBuf buf
    -- field 2: links (repeated Policy)
    let lBuf := encodeLink pid
    let buf := encodeBytes 2 lBuf buf
    (buf, idx + 1)) (buf, 0)
  buf

/-! ## Full Policy encoding (with real scope constraints)

`encodePolicySet` above wraps a bare `Expr` with all-`Any` scopes (everything in the
`when` clause). This section encodes a full `Cedar.Spec.Policy`, emitting its actual
principal/action/resource scope constraints. Mirrors the proto oneofs in `core.proto`:

  PrincipalOrResourceConstraint { Any any=1; InMessage in=2; EqMessage eq=3;
                                  IsMessage is=4; IsInMessage isIn=5 }
    where InMessage/EqMessage { EntityReference er=1 }, IsMessage { Name entity_type=1 },
          IsInMessage { EntityReference er=1; Name entity_type=2 }
  ActionConstraint { Any any=1; InMessage in=2 (repeated EntityUid euids=1);
                     EqMessage eq=3 (EntityUid euid=1) }
  EntityReference { Slot slot=1; EntityUid euid=2 }

Slots are NOT modeled in the Lean `Scope`, so only the non-slot `euid` arm of
`EntityReference` is emitted (templates/slots are future work). -/

/-- `EntityReference { EntityUid euid = 2 }` (non-slot). -/
def encodeEntityReference (uid : EntityUID) : ByteArray :=
  encodeBytes 2 (encodeEntityUID uid) ByteArray.empty

/-- Encode a principal/resource `Scope` as a `PrincipalOrResourceConstraint`. -/
def encodePrincipalOrResourceScope : Scope → ByteArray
  | .any           => encodeEnumAlways 1 0 ByteArray.empty
  | .mem uid       => -- InMessage { er=1 } at field 2
    encodeBytes 2 (encodeBytes 1 (encodeEntityReference uid) ByteArray.empty) ByteArray.empty
  | .eq uid        => -- EqMessage { er=1 } at field 3
    encodeBytes 3 (encodeBytes 1 (encodeEntityReference uid) ByteArray.empty) ByteArray.empty
  | .is ety        => -- IsMessage { entity_type=1 } at field 4
    encodeBytes 4 (encodeBytes 1 (encodeName ety) ByteArray.empty) ByteArray.empty
  | .isMem ety uid => -- IsInMessage { er=1, entity_type=2 } at field 5
    let m := encodeBytes 1 (encodeEntityReference uid) ByteArray.empty
    let m := encodeBytes 2 (encodeName ety) m
    encodeBytes 5 m ByteArray.empty

/-- Encode an `ActionScope` as an `ActionConstraint`. The proto has no `is`/`isMem`
    arm for actions (Cedar's concrete grammar forbids `action is …`), and the
    `WellTypedActionScope` generator never produces them, so those map to `Any`. -/
def encodeActionScopeConstraint (a : ActionScope) : ByteArray :=
  let inOf (uids : List EntityUID) : ByteArray :=
    -- InMessage { repeated EntityUid euids=1 } at field 2
    let inner := uids.foldl (fun b uid => encodeBytes 1 (encodeEntityUID uid) b) ByteArray.empty
    encodeBytes 2 inner ByteArray.empty
  match a with
  | .actionScope .any         => encodeEnumAlways 1 0 ByteArray.empty
  | .actionScope (.mem uid)   => inOf [uid]
  | .actionScope (.eq uid)    => -- EqMessage { EntityUid euid=1 } at field 3
    encodeBytes 3 (encodeBytes 1 (encodeEntityUID uid) ByteArray.empty) ByteArray.empty
  | .actionScope (.is _)      => encodeEnumAlways 1 0 ByteArray.empty  -- not representable → Any
  | .actionScope (.isMem _ _) => encodeEnumAlways 1 0 ByteArray.empty  -- not representable → Any
  | .actionInAny uids         => inOf uids

/-- Encode a full `Policy` as a `TemplateBody` (id, effect, real scope constraints,
    and the `when`/`unless` conditions folded into `non_scope_constraints`). -/
def encodePolicyTemplateBody (p : Policy) : ByteArray :=
  let buf := ByteArray.empty
  let buf := encodeStringAlways 1 p.id buf                                       -- id
  let effVal := match p.effect with | .permit => 1 | .forbid => 0
  let buf := encodeEnumAlways 4 effVal buf                                       -- effect
  let buf := encodeBytes 5 (encodePrincipalOrResourceScope p.principalScope.scope) buf
  let buf := encodeBytes 6 (encodeActionScopeConstraint p.actionScope) buf
  let buf := encodeBytes 7 (encodePrincipalOrResourceScope p.resourceScope.scope) buf
  -- non_scope_constraints (field 8): a policy with no `when`/`unless` clauses has an
  -- empty condition list; cedar-policy encodes that as an absent field (its
  -- `non_scope_constraints()` returns `None`), so we omit field 8 here too rather than
  -- emit a spurious `true`. Otherwise emit the AND-folded condition expression.
  match p.condition with
  | [] => buf
  | _  => encodeBytes 8 (encodeExpr p.condition.toExpr) buf

/-- Encode a list of full `Policy`s as a `PolicySet` (each a static template + link).
    Ids are renumbered `policy{idx}` so template ids and links always match. -/
def encodePolicies (policies : List Policy) : ByteArray :=
  let (buf, _) := policies.foldl (fun (buf, idx) p =>
    let pid := s!"policy{idx}"
    let tBuf := encodePolicyTemplateBody { p with id := pid }
    let buf := encodeBytes 1 tBuf buf          -- field 1: templates
    let lBuf := encodeLink pid
    let buf := encodeBytes 2 lBuf buf          -- field 2: links
    (buf, idx + 1)) (ByteArray.empty, 0)
  buf

/-! ## Schema encoding

message Schema { repeated EntityDecl entity_decls = 1; repeated ActionDecl action_decls = 2; }
message EntityDecl { Name name=1; repeated Name descendants=2; map<string,AttributeType> attributes=3; optional Type tags=5; repeated string enum_choices=6; }
message ActionDecl { EntityUid name=1; repeated EntityUid descendants=3; map<string,AttributeType> context=4; repeated Name principal_types=5; repeated Name resource_types=6; }
message Type { oneof data { Prim prim=1; Type set_elem=2; Name entity=3; Record record=4; Name ext=5; } enum Prim { String=0; Bool=1; Long=2; } message Record { map<string,AttributeType> attrs=1; } }
message AttributeType { Type attr_type=1; bool is_required=2; }
-/

open Cedar.Validation in
def encodeType (ty : CedarType) : ByteArray :=
  match ty with
  | .bool _ => encodeEnumAlways 1 1 ByteArray.empty
  | .int => encodeEnumAlways 1 2 ByteArray.empty
  | .string => encodeEnumAlways 1 0 ByteArray.empty
  | .entity ety => encodeBytes 3 (encodeName ety) ByteArray.empty
  | .set elemTy => encodeBytes 2 (encodeType elemTy) ByteArray.empty
  | .record rty => encodeBytes 4 (encodeRecordAttrs rty.toList) ByteArray.empty
  | .ext xty =>
    -- Extension type names are unqualified in cedar-policy (registered via
    -- `Name::parse_unqualified_name`), matching `extFunToName` above. Namespacing
    -- them as `Cedar::duration` made cedar-policy reject `attr <= duration(...)`.
    let extName := match xty with
      | .decimal => Name.mk "decimal" []
      | .ipAddr => Name.mk "ipaddr" []
      | .datetime => Name.mk "datetime" []
      | .duration => Name.mk "duration" []
    encodeBytes 5 (encodeName extName) ByteArray.empty
where
  encodeRecordAttrs : List (Attr × QualifiedType) → ByteArray
    | [] => ByteArray.empty
    | (attr, .required t) :: rest =>
      let tyBuf := encodeBool 2 true (encodeBytes 1 (encodeType t) ByteArray.empty)
      let entry := encodeBytes 2 tyBuf (encodeStringAlways 1 attr ByteArray.empty)
      encodeBytes 1 entry ByteArray.empty ++ encodeRecordAttrs rest
    | (attr, .optional t) :: rest =>
      let tyBuf := encodeBool 2 false (encodeBytes 1 (encodeType t) ByteArray.empty)
      let entry := encodeBytes 2 tyBuf (encodeStringAlways 1 attr ByteArray.empty)
      encodeBytes 1 entry ByteArray.empty ++ encodeRecordAttrs rest

open Cedar.Validation in
def encodeAttributeType (qty : QualifiedType) : ByteArray :=
  match qty with
  | .required t => encodeBool 2 true (encodeBytes 1 (encodeType t) ByteArray.empty)
  | .optional t => encodeBool 2 false (encodeBytes 1 (encodeType t) ByteArray.empty)

/- The proto `EntityDecl.descendants`/`ActionDecl.descendants` fields (2 and 3)
   carry *descendants*, whereas the Lean `TypeEnv` stores *ancestors*. This
   matches Cedar's post-construction serialization. So the encoder must invert
   the relation before writing: `descendants(x) = { y | x ∈ ancestors(y) }`.
   Because the generated ancestor sets are already transitively closed
   (`Schema.lean`/`PickClosedAncestors`), the reversed descendant sets are
   closed too — no `compute_tc` needed here, just the reversal. This is what
   makes the decoded schema faithful to the generated one (both `CedarProto`
   and the Rust decoder invert field 2 back to ancestors). -/
open Cedar.Validation in
def encodeEntityDecl (ety : EntityType) (entry : EntitySchemaEntry)
    (descendants : List EntityType) : ByteArray :=
  let buf := encodeBytes 1 (encodeName ety) ByteArray.empty
  let buf := descendants.foldl (fun b d => encodeBytes 2 (encodeName d) b) buf
  match entry with
  | .standard sentry =>
    let buf := sentry.attrs.toList.foldl (fun b (attr, qty) =>
      let mapEntry := encodeBytes 2 (encodeAttributeType qty) (encodeStringAlways 1 attr ByteArray.empty)
      encodeBytes 3 mapEntry b) buf
    match sentry.tags with
    | .some tagTy => encodeBytes 5 (encodeType tagTy) buf
    | .none => buf
  | .enum eids =>
    eids.toList.foldl (fun b eid => encodeStringAlways 6 eid b) buf

open Cedar.Validation in
def encodeActionDecl (uid : EntityUID) (entry : ActionSchemaEntry)
    (descendants : List EntityUID) : ByteArray :=
  let buf := encodeBytes 1 (encodeEntityUID uid) ByteArray.empty
  let buf := descendants.foldl (fun b d =>
    encodeBytes 3 (encodeEntityUID d) b) buf
  let buf := entry.context.toList.foldl (fun b (attr, qty) =>
    let mapEntry := encodeBytes 2 (encodeAttributeType qty) (encodeStringAlways 1 attr ByteArray.empty)
    encodeBytes 4 mapEntry b) buf
  let buf := entry.appliesToPrincipal.toList.foldl (fun b p =>
    encodeBytes 5 (encodeName p) b) buf
  entry.appliesToResource.toList.foldl (fun b r =>
    encodeBytes 6 (encodeName r) b) buf

open Cedar.Validation in
def encodeSchema (env : TypeEnv) : ByteArray :=
  -- Invert ancestors → descendants for both entity and action hierarchies.
  let entsList := env.ets.toList
  let entDescendants (x : EntityType) : List EntityType :=
    entsList.filterMap (fun (y, e) => if e.ancestors.contains x then some y else none)
  let buf := entsList.foldl (fun b (ety, entry) =>
    encodeBytes 1 (encodeEntityDecl ety entry (entDescendants ety)) b) ByteArray.empty
  let actsList := env.acts.toList
  let actDescendants (x : EntityUID) : List EntityUID :=
    actsList.filterMap (fun (y, e) => if e.ancestors.contains x then some y else none)
  actsList.foldl (fun b (uid, entry) =>
    encodeBytes 2 (encodeActionDecl uid entry (actDescendants uid)) b) buf

end CedarProto.Encode

/-! ## Roundtrip tests: encode with CedarProto.Encode, decode with CedarProto (Message Expr) -/

section RoundtripTest

open Cedar.Spec
open Cedar.Data
open CedarProto.Encode
open Proto

private def roundtrip (e : Expr) : Except String Expr :=
  let bytes := encodeExpr e
  Message.interpret? bytes

private def testRoundtrip (name : String) (e : Expr) : IO Unit := do
  match roundtrip e with
  | .ok decoded =>
    if decoded == e then
      IO.println s!"  PASS: {name}"
    else
      IO.println s!"  FAIL: {name}"
      IO.println s!"    input:   {repr e}"
      IO.println s!"    decoded: {repr decoded}"
  | .error err =>
    IO.println s!"  FAIL: {name} (decode error: {err})"
    IO.println s!"    bytes: {(encodeExpr e).toList}"

#eval do
  IO.println "=== Protobuf Encode Roundtrip Tests ==="
  -- Literals
  testRoundtrip "bool true" (.lit (.bool true))
  testRoundtrip "bool false" (.lit (.bool false))
  testRoundtrip "int 0" (.lit (.int 0))
  testRoundtrip "int 42" (.lit (.int 42))
  testRoundtrip "int -1" (.lit (.int (-1)))
  testRoundtrip "string hello" (.lit (.string "hello"))
  testRoundtrip "string empty" (.lit (.string ""))
  testRoundtrip "entityUID" (.lit (.entityUID ⟨{ id := "User", path := [] }, "alice"⟩))
  testRoundtrip "entityUID with path" (.lit (.entityUID ⟨{ id := "Admin", path := ["App"] }, "bob"⟩))
  -- Variables
  testRoundtrip "var principal" (.var .principal)
  testRoundtrip "var action" (.var .action)
  testRoundtrip "var resource" (.var .resource)
  testRoundtrip "var context" (.var .context)
  -- Compound
  testRoundtrip "and" (.and (.lit (.bool true)) (.lit (.bool false)))
  testRoundtrip "or" (.or (.var .principal) (.lit (.bool true)))
  testRoundtrip "ite" (.ite (.lit (.bool true)) (.lit (.int 1)) (.lit (.int 2)))
  testRoundtrip "not" (.unaryApp .not (.lit (.bool true)))
  testRoundtrip "neg" (.unaryApp .neg (.lit (.int 5)))
  testRoundtrip "isEmpty" (.unaryApp .isEmpty (.set []))
  testRoundtrip "eq" (.binaryApp .eq (.var .principal) (.var .resource))
  testRoundtrip "less" (.binaryApp .less (.lit (.int 1)) (.lit (.int 2)))
  testRoundtrip "add" (.binaryApp .add (.lit (.int 1)) (.lit (.int 2)))
  testRoundtrip "mem" (.binaryApp .mem (.var .principal) (.var .resource))
  testRoundtrip "contains" (.binaryApp .contains (.set [.lit (.int 1)]) (.lit (.int 1)))
  testRoundtrip "hasTag" (.binaryApp .hasTag (.var .principal) (.lit (.string "role")))
  testRoundtrip "getTag" (.binaryApp .getTag (.var .resource) (.lit (.string "priority")))
  -- Attr access
  testRoundtrip "getAttr" (.getAttr (.var .principal) "name")
  testRoundtrip "hasAttr" (.hasAttr (.var .resource) "score")
  -- Like
  testRoundtrip "like" (.unaryApp (.like [.star, .justChar 'a', .star]) (.lit (.string "banana")))
  -- Is
  testRoundtrip "is" (.unaryApp (.is { id := "User", path := [] }) (.var .principal))
  testRoundtrip "is with path" (.unaryApp (.is { id := "Admin", path := ["App"] }) (.var .principal))
  -- Set / Record
  testRoundtrip "empty set" (.set [])
  testRoundtrip "set" (.set [.lit (.int 1), .lit (.int 2), .lit (.int 3)])
  testRoundtrip "empty record" (.record [])
  testRoundtrip "record" (.record [("x", .lit (.int 1)), ("y", .lit (.string "hi"))])
  -- Extension functions
  testRoundtrip "decimal" (.call .decimal [.lit (.string "1.23")])
  testRoundtrip "ip" (.call .ip [.lit (.string "10.0.0.1")])
  testRoundtrip "isInRange" (.call .isInRange [.call .ip [.lit (.string "10.0.0.1")], .call .ip [.lit (.string "10.0.0.0/24")]])
  -- Nested
  testRoundtrip "nested" (.ite
    (.and (.binaryApp .eq (.getAttr (.var .principal) "age") (.lit (.int 21)))
          (.hasAttr (.var .resource) "score"))
    (.binaryApp .add (.getAttr (.var .resource) "score") (.lit (.int 1)))
    (.lit (.int 0)))
  IO.println "=== Done ==="

end RoundtripTest

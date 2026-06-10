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

/-! # Cedar expression pretty printer

Prints Expr in the same format as Rust's `Display for ast::Expr`.
This is needed for cross-language comparison in the PBT test.
-/

namespace CedarGenFaithful

open Cedar.Spec
open Cedar.Data

/-- Print an EntityUID in Cedar syntax: Type::"eid" -/
def printEntityUID (uid : EntityUID) : String :=
  let tyStr := match uid.ty.path with
    | [] => uid.ty.id
    | ps => String.intercalate "::" (ps ++ [uid.ty.id])
  s!"{tyStr}::\"{uid.eid}\""

/-- Print a Prim in Cedar syntax -/
def printPrim : Prim → String
  | .bool true => "true"
  | .bool false => "false"
  | .int i =>
    let n := i.toInt
    if n < 0 then s!"({n})" else toString n
  | .string s => s!"\"{s}\""
  | .entityUID uid => printEntityUID uid

/-- Does this expression need parenthesization when used as a sub-expression?
    Matches Rust's Display which wraps compound exprs in parens. -/
def needsParens : Expr → Bool
  | .lit _ | .var _ | .set _ | .record _ => false
  | _ => true

mutual
/-- Print an expression, wrapping in parens if compound -/
partial def printExprParens (e : Expr) : String :=
  if needsParens e then s!"({printExpr e})" else printExpr e

/-- Print an Expr in Cedar syntax matching Rust's Display -/
partial def printExpr : Expr → String
  | .lit p => printPrim p
  | .var .principal => "principal"
  | .var .action => "action"
  | .var .resource => "resource"
  | .var .context => "context"
  | .ite c t e => s!"if {printExprParens c} then {printExprParens t} else {printExprParens e}"
  | .and a b => s!"{printExprParens a} && {printExprParens b}"
  | .or a b => s!"{printExprParens a} || {printExprParens b}"
  | .unaryApp .not e =>
    let inner := printExpr e
    match e with
    | .lit _ | .var _ | .set _ | .record _ => s!"!{inner}"
    | _ => s!"!({inner})"
  | .unaryApp .neg e => s!"-({printExpr e})"
  | .unaryApp .isEmpty e => s!"{printExprParens e}.isEmpty()"
  | .unaryApp (.like pat) e =>
    let patStr := String.join (pat.map fun
      | .star => "*"
      | .justChar c => String.ofList [c])
    s!"{printExprParens e} like \"{patStr}\""
  | .unaryApp (.is ety) e =>
    let etyStr := match ety.path with
      | [] => ety.id
      | ps => String.intercalate "::" (ps ++ [ety.id])
    s!"{printExprParens e} is {etyStr}"
  | .binaryApp .eq a b => s!"{printExprParens a} == {printExprParens b}"
  | .binaryApp .less a b => s!"{printExprParens a} < {printExprParens b}"
  | .binaryApp .lessEq a b => s!"{printExprParens a} <= {printExprParens b}"
  | .binaryApp .add a b => s!"{printExprParens a} + {printExprParens b}"
  | .binaryApp .sub a b => s!"{printExprParens a} - {printExprParens b}"
  | .binaryApp .mul a b => s!"{printExprParens a} * {printExprParens b}"
  | .binaryApp .mem a b => s!"{printExprParens a} in {printExprParens b}"
  | .binaryApp .contains a b => s!"{printExprParens a}.contains({printExpr b})"
  | .binaryApp .containsAll a b => s!"{printExprParens a}.containsAll({printExpr b})"
  | .binaryApp .containsAny a b => s!"{printExprParens a}.containsAny({printExpr b})"
  | .binaryApp .hasTag e tag => s!"{printExprParens e}.hasTag({printExpr tag})"
  | .binaryApp .getTag e tag => s!"{printExprParens e}.getTag({printExpr tag})"
  | .getAttr e attr =>
    if attr.isEmpty then s!"{printExprParens e}[\"\"]"
    else s!"{printExprParens e}.{attr}"
  | .hasAttr e attr =>
    if attr.isEmpty then s!"{printExprParens e} has \"\""
    else s!"{printExprParens e} has {attr}"
  | .set es => s!"[{String.intercalate ", " (es.map printExpr)}]"
  | .record pairs =>
    let fields := pairs.map fun (k, v) => s!"{k}: {printExpr v}"
    s!"\{{String.intercalate ", " fields}}"
  | .call xfn args =>
    let name := match xfn with
      | .decimal => "decimal" | .lessThan => "lessThan"
      | .lessThanOrEqual => "lessThanOrEqual"
      | .greaterThan => "greaterThan" | .greaterThanOrEqual => "greaterThanOrEqual"
      | .ip => "ip" | .isIpv4 => "isIpv4" | .isIpv6 => "isIpv6"
      | .isLoopback => "isLoopback" | .isMulticast => "isMulticast"
      | .isInRange => "isInRange" | .datetime => "datetime"
      | .duration => "duration" | .offset => "offset"
      | .durationSince => "durationSince" | .toDate => "toDate"
      | .toTime => "toTime" | .toMilliseconds => "toMilliseconds"
      | .toSeconds => "toSeconds" | .toMinutes => "toMinutes"
      | .toHours => "toHours" | .toDays => "toDays"
    -- Rust displays CONSTRUCTOR ext functions with function syntax: name(args)
    -- Non-constructors use method syntax: arg0.name(rest)
    let isConstructor := match xfn with
      | .ip | .decimal | .datetime | .duration => true
      | _ => false
    if isConstructor then
      s!"{name}({String.intercalate ", " (args.map printExpr)})"
    else
      match args with
      | [] => s!"{name}()"
      | [receiver] => s!"{printExprParens receiver}.{name}()"
      | receiver :: rest => s!"{printExprParens receiver}.{name}({String.intercalate ", " (rest.map printExpr)})"

end

end CedarGenFaithful

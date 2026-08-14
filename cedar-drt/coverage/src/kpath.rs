use cedar_policy::PolicySet;
use cedar_policy_core::ast::{BinaryOp, Expr, ExprKind, PolicySet as CorePolicySet, UnaryOp};
use std::collections::HashSet;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct KPath(pub Vec<&'static str>);

fn bin_op_name(op: &BinaryOp) -> &'static str {
    match op {
        BinaryOp::Eq => "Binary::Eq",
        BinaryOp::Less => "Binary::Less",
        BinaryOp::LessEq => "Binary::LessEq",
        BinaryOp::Add => "Binary::Add",
        BinaryOp::Sub => "Binary::Sub",
        BinaryOp::Mul => "Binary::Mul",
        BinaryOp::In => "Binary::In",
        BinaryOp::Contains => "Binary::Contains",
        BinaryOp::ContainsAll => "Binary::ContainsAll",
        BinaryOp::ContainsAny => "Binary::ContainsAny",
        BinaryOp::GetTag => "Binary::GetTag",
        BinaryOp::HasTag => "Binary::HasTag",
    }
}

fn un_op_name(op: &UnaryOp) -> &'static str {
    match op {
        UnaryOp::Not => "Unary::Not",
        UnaryOp::Neg => "Unary::Neg",
        UnaryOp::IsEmpty => "Unary::IsEmpty",
    }
}

/// Extension-function label, matched on the basename (`&str`, no allocation) so the
/// returned label stays `&'static str` — keeps k-path nodes pointer-cheap to clone/hash.
/// The list is the complete set of Cedar extension functions (decimal/ipaddr/datetime/
/// duration) as of the pinned `./cedar` checkout; `ExtFun::<other>` is a safety net that
/// only triggers if Cedar adds a new one (add it here to distinguish it).
fn ext_fn_name(fn_name: &cedar_policy_core::ast::Name) -> &'static str {
    match fn_name.basename().as_ref() {
        "decimal" => "ExtFun::decimal",
        "lessThan" => "ExtFun::lessThan",
        "lessThanOrEqual" => "ExtFun::lessThanOrEqual",
        "greaterThan" => "ExtFun::greaterThan",
        "greaterThanOrEqual" => "ExtFun::greaterThanOrEqual",
        "ip" => "ExtFun::ip",
        "isInRange" => "ExtFun::isInRange",
        "isIpv4" => "ExtFun::isIpv4",
        "isIpv6" => "ExtFun::isIpv6",
        "isLoopback" => "ExtFun::isLoopback",
        "isMulticast" => "ExtFun::isMulticast",
        "datetime" => "ExtFun::datetime",
        "duration" => "ExtFun::duration",
        "offset" => "ExtFun::offset",
        "durationSince" => "ExtFun::durationSince",
        "toDate" => "ExtFun::toDate",
        "toTime" => "ExtFun::toTime",
        "toMilliseconds" => "ExtFun::toMilliseconds",
        "toSeconds" => "ExtFun::toSeconds",
        "toMinutes" => "ExtFun::toMinutes",
        "toHours" => "ExtFun::toHours",
        "toDays" => "ExtFun::toDays",
        _ => "ExtFun::<other>",
    }
}

/// Node label for k-path / top-constructor stats. Distinguishes the SPECIFIC
/// operator (`Binary::HasTag` vs `Binary::Less`) and extension function
/// (`ExtFun::decimal` vs `ExtFun::ip`) rather than collapsing them to `Binary`/
/// `ExtFun`, so k-paths capture operator-level structural diversity. `Is`/`Like`/
/// `GetAttr`/`HasAttr` stay single labels — the entity type / pattern / attr name is
/// a payload, not a constructor variant. Returns `&'static str` (no allocation) so
/// paths stay cheap to hash/clone. Matches the scheme in `bin/op_hist.rs`.
pub fn expr_kind_name(expr: &Expr) -> &'static str {
    match expr.expr_kind() {
        ExprKind::Lit(_) => "Lit",
        ExprKind::Var(_) => "Var",
        ExprKind::Slot(_) => "Slot",
        ExprKind::Unknown(_) => "Unknown",
        ExprKind::If { .. } => "If",
        ExprKind::And { .. } => "And",
        ExprKind::Or { .. } => "Or",
        ExprKind::UnaryApp { op, .. } => un_op_name(op),
        ExprKind::BinaryApp { op, .. } => bin_op_name(op),
        ExprKind::ExtensionFunctionApp { fn_name, .. } => ext_fn_name(fn_name),
        ExprKind::GetAttr { .. } => "GetAttr",
        ExprKind::HasAttr { .. } => "HasAttr",
        ExprKind::Like { .. } => "Like",
        ExprKind::Is { .. } => "Is",
        ExprKind::Set(_) => "Set",
        ExprKind::Record(_) => "Record",
    }
}

fn children(expr: &Expr) -> Vec<&Expr> {
    match expr.expr_kind() {
        ExprKind::Lit(_) | ExprKind::Var(_) | ExprKind::Slot(_) | ExprKind::Unknown(_) => vec![],
        ExprKind::If {
            test_expr,
            then_expr,
            else_expr,
        } => vec![test_expr.as_ref(), then_expr.as_ref(), else_expr.as_ref()],
        ExprKind::And { left, right } | ExprKind::Or { left, right } => {
            vec![left.as_ref(), right.as_ref()]
        }
        ExprKind::UnaryApp { arg, .. } => vec![arg.as_ref()],
        ExprKind::BinaryApp { arg1, arg2, .. } => vec![arg1.as_ref(), arg2.as_ref()],
        ExprKind::ExtensionFunctionApp { args, .. } => args.iter().collect(),
        ExprKind::GetAttr { expr, .. } | ExprKind::HasAttr { expr, .. } => vec![expr.as_ref()],
        ExprKind::Like { expr, .. } => vec![expr.as_ref()],
        ExprKind::Is { expr, .. } => vec![expr.as_ref()],
        ExprKind::Set(elems) => elems.iter().collect(),
        ExprKind::Record(map) => map.values().collect(),
    }
}

fn collect_kpaths(expr: &Expr, k: usize, prefix: &mut Vec<&'static str>, paths: &mut HashSet<KPath>) {
    let name = expr_kind_name(expr);
    prefix.push(name);

    if prefix.len() >= k {
        paths.insert(KPath(prefix[prefix.len() - k..].to_vec()));
    }

    for child in children(expr) {
        collect_kpaths(child, k, prefix, paths);
    }

    prefix.pop();
}

pub fn extract_kpaths_from_expr(expr: &Expr, k: usize) -> HashSet<KPath> {
    let mut paths = HashSet::new();
    let mut prefix = Vec::new();
    collect_kpaths(expr, k, &mut prefix, &mut paths);
    paths
}

pub fn count_nodes(expr: &Expr) -> usize {
    1 + children(expr).iter().map(|c| count_nodes(c)).sum::<usize>()
}

pub struct InputStats {
    pub node_count: usize,
    pub top_constructors: Vec<&'static str>,
    pub kpaths: HashSet<KPath>,
}

pub fn analyze_policy_set(policies: &PolicySet, k: usize) -> InputStats {
    let mut node_count = 0;
    let mut top_constructors = Vec::new();
    let mut kpaths = HashSet::new();

    // Access the underlying core policy set
    let core_pset: &CorePolicySet = policies.as_ref();
    for policy in core_pset.policies() {
        let condition = policy.condition();
        node_count += count_nodes(&condition);
        top_constructors.push(expr_kind_name(&condition));
        kpaths.extend(extract_kpaths_from_expr(&condition, k));
    }

    InputStats {
        node_count,
        top_constructors,
        kpaths,
    }
}

/// Hash an expression tree including literal values (full content hash).
fn hash_expr(expr: &Expr, hasher: &mut impl Hasher) {
    std::mem::discriminant(expr.expr_kind()).hash(hasher);
    match expr.expr_kind() {
        ExprKind::Lit(lit) => { format!("{:?}", lit).hash(hasher); }
        ExprKind::Var(v) => { v.hash(hasher); }
        ExprKind::Slot(s) => { s.hash(hasher); }
        ExprKind::GetAttr { attr, .. } | ExprKind::HasAttr { attr, .. } => {
            attr.hash(hasher);
        }
        ExprKind::Like { pattern, .. } => { format!("{:?}", pattern).hash(hasher); }
        ExprKind::Is { entity_type, .. } => { format!("{:?}", entity_type).hash(hasher); }
        ExprKind::UnaryApp { op, .. } => { format!("{:?}", op).hash(hasher); }
        ExprKind::BinaryApp { op, .. } => { format!("{:?}", op).hash(hasher); }
        ExprKind::ExtensionFunctionApp { fn_name, .. } => { format!("{:?}", fn_name).hash(hasher); }
        _ => {}
    }
    for child in children(expr) {
        hash_expr(child, hasher);
    }
}

/// Hash an expression tree ignoring literal values (skeleton hash).
/// Two expressions with the same structure but different literal values get the same hash.
fn hash_expr_skeleton(expr: &Expr, hasher: &mut impl Hasher) {
    std::mem::discriminant(expr.expr_kind()).hash(hasher);
    match expr.expr_kind() {
        ExprKind::Lit(lit) => {
            // Hash only the literal *kind* (bool/int/string/entity), not the value
            std::mem::discriminant(lit).hash(hasher);
        }
        ExprKind::Var(v) => { v.hash(hasher); }
        ExprKind::Slot(s) => { s.hash(hasher); }
        ExprKind::GetAttr { attr, .. } | ExprKind::HasAttr { attr, .. } => {
            attr.hash(hasher);
        }
        ExprKind::Like { .. } => { 0u8.hash(hasher); } // ignore pattern content
        ExprKind::Is { entity_type, .. } => { format!("{:?}", entity_type).hash(hasher); }
        ExprKind::UnaryApp { op, .. } => { format!("{:?}", op).hash(hasher); }
        ExprKind::BinaryApp { op, .. } => { format!("{:?}", op).hash(hasher); }
        ExprKind::ExtensionFunctionApp { fn_name, .. } => { format!("{:?}", fn_name).hash(hasher); }
        _ => {}
    }
    for child in children(expr) {
        hash_expr_skeleton(child, hasher);
    }
}

/// Compute a content hash for a PolicySet (sensitive to literal values).
pub fn hash_policy_set(policies: &PolicySet) -> u64 {
    let mut hasher = DefaultHasher::new();
    let core_pset: &CorePolicySet = policies.as_ref();
    for policy in core_pset.policies() {
        hash_expr(&policy.condition(), &mut hasher);
    }
    hasher.finish()
}

/// Compute a skeleton hash for a PolicySet (ignoring literal values).
/// Two PolicySets with the same expression structure but different literals get the same hash.
pub fn hash_policy_set_skeleton(policies: &PolicySet) -> u64 {
    let mut hasher = DefaultHasher::new();
    let core_pset: &CorePolicySet = policies.as_ref();
    for policy in core_pset.policies() {
        hash_expr_skeleton(&policy.condition(), &mut hasher);
    }
    hasher.finish()
}

use cedar_policy::PolicySet;
use cedar_policy_core::ast::{Expr, ExprKind, PolicySet as CorePolicySet};
use std::collections::HashSet;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct KPath(pub Vec<&'static str>);

pub fn expr_kind_name(expr: &Expr) -> &'static str {
    match expr.expr_kind() {
        ExprKind::Lit(_) => "Lit",
        ExprKind::Var(_) => "Var",
        ExprKind::Slot(_) => "Slot",
        ExprKind::Unknown(_) => "Unknown",
        ExprKind::If { .. } => "If",
        ExprKind::And { .. } => "And",
        ExprKind::Or { .. } => "Or",
        ExprKind::UnaryApp { .. } => "Unary",
        ExprKind::BinaryApp { .. } => "Binary",
        ExprKind::ExtensionFunctionApp { .. } => "ExtFun",
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

// SCRATCH: operator-frequency histogram over a directory of corpus batch files.
// Each batch = repeated [u32-le len ‖ entry]; each entry = [schema_len:u32-le ‖
// schema-proto ‖ policies-proto]. Walks every policy condition AST and tallies the
// SPECIFIC operator at each node. Used to answer "which operators does generator A
// emit that generator B doesn't" at the source level (no coverage attribution).
//
//   cargo run --bin op_hist -- <dir-of-.bin>   (prints "op<TAB>count" sorted)
use cedar_policy::proto::traits::Protobuf;
use cedar_policy::PolicySet;
use cedar_policy_core::ast::{BinaryOp, Expr, ExprKind, PolicySet as CorePolicySet, UnaryOp};
use std::collections::{BTreeMap, BTreeSet};

fn decode_batch(data: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut pos = 0;
    while pos + 4 <= data.len() {
        let len = u32::from_le_bytes([data[pos], data[pos + 1], data[pos + 2], data[pos + 3]]) as usize;
        pos += 4;
        if pos + len > data.len() { break; }
        out.push(data[pos..pos + len].to_vec());
        pos += len;
    }
    out
}

fn bin_op(op: &BinaryOp) -> &'static str {
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

fn un_op(op: &UnaryOp) -> &'static str {
    match op {
        UnaryOp::Not => "Unary::Not",
        UnaryOp::Neg => "Unary::Neg",
        UnaryOp::IsEmpty => "Unary::IsEmpty",
    }
}

fn walk(e: &Expr, tally: &mut BTreeMap<String, u64>, seen: &mut BTreeSet<String>, nodes: &mut u64) {
    let (label, children): (String, Vec<&Expr>) = match e.expr_kind() {
        ExprKind::Lit(_) => ("Lit".into(), vec![]),
        ExprKind::Var(_) => ("Var".into(), vec![]),
        ExprKind::Slot(_) => ("Slot".into(), vec![]),
        ExprKind::Unknown(_) => ("Unknown".into(), vec![]),
        ExprKind::If { test_expr, then_expr, else_expr } =>
            ("If".into(), vec![test_expr, then_expr, else_expr]),
        ExprKind::And { left, right } => ("And".into(), vec![left, right]),
        ExprKind::Or { left, right } => ("Or".into(), vec![left, right]),
        ExprKind::UnaryApp { op, arg } => (un_op(op).into(), vec![arg.as_ref()]),
        ExprKind::BinaryApp { op, arg1, arg2 } => (bin_op(op).into(), vec![arg1.as_ref(), arg2.as_ref()]),
        ExprKind::ExtensionFunctionApp { fn_name, args } =>
            (format!("ExtFun::{}", fn_name), args.iter().collect()),
        ExprKind::GetAttr { expr, .. } => ("GetAttr".into(), vec![expr.as_ref()]),
        ExprKind::HasAttr { expr, .. } => ("HasAttr".into(), vec![expr.as_ref()]),
        ExprKind::Like { expr, .. } => ("Like".into(), vec![expr.as_ref()]),
        ExprKind::Is { expr, .. } => ("Is".into(), vec![expr.as_ref()]),
        ExprKind::Set(elems) => ("Set".into(), elems.iter().collect()),
        ExprKind::Record(map) => ("Record".into(), map.values().collect()),
        _ => ("Other".into(), vec![]),
    };
    *tally.entry(label.clone()).or_insert(0) += 1;   // total occurrences
    seen.insert(label);                              // this policy contains >=1 of this label
    *nodes += 1;                                     // total AST nodes (for composition share)
    for c in children { walk(c, tally, seen, nodes); }
}

fn collect_bins(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    for f in rd.flatten() {
        let p = f.path();
        if p.is_dir() { collect_bins(&p, out); }
        else if p.extension().map(|e| e == "bin").unwrap_or(false) { out.push(p); }
    }
}

fn main() {
    let dir = std::env::args().nth(1).expect("usage: op_hist <dir> [--json]");
    let json = std::env::args().any(|a| a == "--json");
    let mut tally: BTreeMap<String, u64> = BTreeMap::new();   // total occurrences per label
    let mut present: BTreeMap<String, u64> = BTreeMap::new(); // #policies containing >=1 of label
    let mut policies = 0u64;
    let mut total_nodes = 0u64;
    let mut entries = 0u64;
    let mut files = Vec::new();
    collect_bins(std::path::Path::new(&dir), &mut files);
    eprintln!("# scanning {} .bin files under {dir}", files.len());
    for p in &files {
        let Ok(data) = std::fs::read(p) else { continue };
        for entry in decode_batch(&data) {
            if entry.len() < 4 { continue; }
            let slen = u32::from_le_bytes([entry[0], entry[1], entry[2], entry[3]]) as usize;
            if entry.len() < 4 + slen { continue; }
            let Ok(ps) = PolicySet::decode(&entry[4 + slen..]) else { continue };
            entries += 1;
            let core: &CorePolicySet = ps.as_ref();
            for pol in core.policies() {
                if std::env::var("DUMP").is_ok() && policies < 3 {
                    eprintln!("--- policy {policies} ---\n  principal: {:?}\n  action: {:?}\n  resource: {:?}\n  condition: {}",
                        pol.principal_constraint(), pol.action_constraint(), pol.resource_constraint(), pol.condition());
                }
                policies += 1;
                let mut seen: BTreeSet<String> = BTreeSet::new();
                walk(&pol.condition(), &mut tally, &mut seen, &mut total_nodes);
                for label in seen { *present.entry(label).or_insert(0) += 1; }
            }
        }
    }
    eprintln!("# {entries} inputs, {policies} policies, {total_nodes} nodes from {dir}");
    if json {
        // {"policies":N,"total_nodes":M,"counts":{...},"present":{...}} — feeds plot_node_hist.py,
        // which derives count/policy, count/total_nodes (composition share), or present/policies (%).
        // Labels are constructor / ext-fn names (no quotes/backslashes) -> simple quoting is safe.
        let kv = |m: &BTreeMap<String, u64>| m.iter()
            .map(|(k, v)| format!("\"{}\":{}", k.replace('"', "\\\""), v))
            .collect::<Vec<_>>().join(",");
        println!("{{\"policies\":{policies},\"total_nodes\":{total_nodes},\"counts\":{{{}}},\"present\":{{{}}}}}",
                 kv(&tally), kv(&present));
    } else {
        for (k, v) in &tally {
            println!("{k}\t{v}");
        }
    }
}

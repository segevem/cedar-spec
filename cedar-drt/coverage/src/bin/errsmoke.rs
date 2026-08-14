// Smoke test for the `illtyped-policy` strategy: generate ill-typed policies via FFI,
// run the Rust validator, and confirm they are REJECTED (error paths hit). Tallies the
// error kinds so we can see the distribution before spending on an AWS coverage run.
use cedar_lean_ffi::{CedarLeanFfi, ValidationResponse};
use cedar_policy::proto::traits::Protobuf;
use cedar_policy::{PolicySet, Schema, ValidationMode, Validator};
use std::collections::BTreeMap;
fn ru32(b: &[u8], p: usize) -> Option<(usize, usize)> {
    if p + 4 > b.len() { return None }
    Some((u32::from_le_bytes([b[p], b[p + 1], b[p + 2], b[p + 3]]) as usize, p + 4))
}
fn main() {
    let secs: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(20);
    let strategy = std::env::args().nth(2).unwrap_or_else(|| "illtyped-policy".to_string());
    let ffi = CedarLeanFfi::new();
    let t0 = std::time::Instant::now();
    let mut seed: u64 = 0;
    let (mut nb, mut np, mut empty_batches) = (0u64, 0u64, 0u64);
    // clean = no errors AND no warnings; err = >=1 error; warn_only = 0 errors but >=1 warning
    let (mut clean, mut err_any, mut warn_only) = (0u64, 0u64, 0u64);
    let mut accepted = 0u64; // alias for `clean`, kept for the sample-dump gate below
    let mut kinds: BTreeMap<String, u64> = BTreeMap::new();
    let mut warn_kinds: BTreeMap<String, u64> = BTreeMap::new();
    // Lean-vs-Rust disambiguation: (rust_ok, lean_ok) tallies.
    let (mut both_ok, mut both_err, mut lean_err_rust_ok, mut rust_err_lean_ok) = (0u64, 0u64, 0u64, 0u64);
    let compare_lean = std::env::var("COMPARE_LEAN").is_ok();
    // COMPARE_DRT: run the actual DRT comparison (run_val_test_checked, AgreeOnAll) and count
    // mismatches — the exact check the validation-drt coverage target uses.
    let compare_drt = std::env::var("COMPARE_DRT").is_ok();
    let (mut drt_ok, mut drt_mismatch) = (0u64, 0u64);
    while t0.elapsed().as_secs() < secs {
        let params = serde_json::json!({"seed":seed,"size":20u32,"schema_size":20u32,"strategy":strategy,"count":100u32});
        seed += 100;
        let buf = match ffi.generate_schema_typeof_proto(&params) { Ok(b) if b.len() >= 4 => b, _ => { empty_batches += 1; continue } };
        let (slen, pos) = match ru32(&buf, 0) { Some(x) => x, None => continue };
        if pos + slen > buf.len() { continue }
        let schema = match Schema::decode(&buf[pos..pos + slen]) { Ok(s) => s, Err(_) => continue };
        let mut pos = pos + slen;
        let (cnt, pp) = match ru32(&buf, pos) { Some(x) => x, None => continue }; pos = pp;
        let schema_txt = format!("{schema:?}");
        let schema_for_lean = schema.clone();
        // DUMP_BATCH0: print every decoded policy of the first batch as Cedar text, to compare
        // against the in-memory Lean reprs (round-trip fidelity check).
        if std::env::var("DUMP_BATCH0").is_ok() && nb == 0 {
            eprintln!("=== batch 0 decoded policies (seed {}) ===", seed - 100);
        }
        let dump0 = std::env::var("DUMP_BATCH0").is_ok() && nb == 0;
        let v = Validator::new(schema);
        for _ in 0..cnt {
            let (plen, pp) = match ru32(&buf, pos) { Some(x) => x, None => break }; pos = pp;
            if pos + plen > buf.len() { break }
            if let Ok(ps) = PolicySet::decode(&buf[pos..pos + plen]) {
                if compare_drt {
                    match cedar_drt::tests::run_val_test_checked(&ffi, schema_for_lean.clone(), &ps, ValidationMode::Strict) {
                        Ok(()) => drt_ok += 1,
                        Err(_) => drt_mismatch += 1,
                    }
                    np += 1;
                    pos += plen;
                    continue;
                }
                let res = v.validate(&ps, ValidationMode::Strict);
                np += 1;
                if dump0 && np <= 6 {
                    let vr = if res.validation_errors().next().is_some() { "ERR" }
                        else if res.validation_warnings().next().is_some() { "WARN" } else { "CLEAN" };
                    eprintln!("[p{np} {vr}] {ps}");
                }
                let has_err = res.validation_errors().next().is_some();
                let has_warn = res.validation_warnings().next().is_some();
                // "flagged" = validator produced ANY diagnostic (error or warning).
                let rust_clean = !has_err && !has_warn;
                if compare_lean {
                    // Lean treats impossiblePolicy as an ERROR; Rust as a WARNING. So compare
                    // Lean-Ok against Rust-clean (no err AND no warn) for an apples-to-apples check.
                    let lean_ok = matches!(
                        ffi.validate(&ps, &schema_for_lean, &ValidationMode::Strict),
                        Ok(ValidationResponse::Ok(()))
                    );
                    match (rust_clean, lean_ok) {
                        (true, true) => both_ok += 1,
                        (false, false) => both_err += 1,
                        (true, false) => lean_err_rust_ok += 1,
                        (false, true) => rust_err_lean_ok += 1,
                    }
                }
                if rust_clean {
                    clean += 1;
                    accepted += 1;
                    if accepted <= 4 {
                        eprintln!("\n### CLEAN (no err/warn) but should be ill-typed #{accepted} ###\n-- schema --\n{schema_txt}\n-- policy --\n{ps}");
                    }
                } else if has_err {
                    err_any += 1;
                    for e in res.validation_errors() {
                        // Debug shows the variant name (e.g. `UnexpectedType`, `TypesMustMatch`),
                        // a stable kind label unlike Display which is prefixed "for policy `p0`, ".
                        let s = format!("{e:?}");
                        let key = s.split(|c: char| !c.is_alphanumeric()).find(|t| !t.is_empty()).unwrap_or("").to_string();
                        *kinds.entry(key).or_insert(0) += 1;
                    }
                } else {
                    warn_only += 1;
                }
                for w in res.validation_warnings() {
                    let s = format!("{w}");
                    let key = s.split(|c| c == ',' || c == ':' || c == '(').next().unwrap_or("").trim().to_string();
                    *warn_kinds.entry(key).or_insert(0) += 1;
                }
            }
            pos += plen;
        }
        nb += 1;
    }
    eprintln!("errsmoke[{strategy}]: {nb} batches ({empty_batches} empty), {np} policies validated in {:?}", t0.elapsed());
    eprintln!("  ERROR(>=1 err): {err_any}   WARN-only: {warn_only}   CLEAN(no err/warn, LEAK): {clean}");
    eprintln!("  error-kind tally:");
    for (k, c) in &kinds { eprintln!("    {c:>7}  {k}"); }
    eprintln!("  warning-kind tally:");
    for (k, c) in &warn_kinds { eprintln!("    {c:>7}  {k}"); }
    if compare_lean {
        eprintln!("  Lean-vs-Rust: both_ok={both_ok}  both_err={both_err}  LEAN_err_RUST_ok={lean_err_rust_ok}  RUST_err_LEAN_ok={rust_err_lean_ok}");
    }
    if compare_drt {
        let tot = drt_ok + drt_mismatch;
        let pct = if tot > 0 { 100.0 * drt_mismatch as f64 / tot as f64 } else { 0.0 };
        eprintln!("  DRT (run_val_test_checked, AgreeOnAll): ok={drt_ok}  MISMATCH={drt_mismatch}  ({pct:.1}% mismatch)");
    }
}

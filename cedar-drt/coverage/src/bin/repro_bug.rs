// Reproduce a DRT-mismatch by regenerating its exact batch via the FFI at the
// crash seed, then dump the Rust-decoded schema (action appliesTo + per-entity
// attributes) and Rust's validation errors. Saves the exact schema+policy proto
// to /tmp so the SAME bytes can be fed to the Lean side.
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::proto::traits::Protobuf;
use cedar_policy::{PolicySet, Schema, ValidationMode, Validator};

fn read_u32(b: &[u8], p: usize) -> Option<(usize, usize)> {
    if p + 4 > b.len() { return None; }
    Some((u32::from_le_bytes([b[p], b[p + 1], b[p + 2], b[p + 3]]) as usize, p + 4))
}

/// Try one FFI batch at `seed`; return (schema_bytes, policy_bytes, PolicySet) for
/// the first policy whose text contains `substr`.
fn scan_batch(ffi: &CedarLeanFfi, strategy: &str, size: u32, seed: u64, substr: &str)
    -> Option<(Vec<u8>, Vec<u8>, PolicySet)> {
    let params = serde_json::json!({
        "seed": seed, "size": size, "schema_size": size, "strategy": strategy, "count": 100
    });
    let buf = ffi.generate_schema_typeof_proto(&params).ok()?;
    if buf.len() < 4 { return None; }
    let (slen, pos) = read_u32(&buf, 0)?;
    let schema_bytes = buf.get(pos..pos + slen)?.to_vec();
    let mut pos = pos + slen;
    let (cnt, np) = read_u32(&buf, pos)?; pos = np;
    for _ in 0..cnt {
        let (plen, np) = read_u32(&buf, pos)?; pos = np;
        let pbytes = buf.get(pos..pos + plen)?.to_vec();
        if let Ok(ps) = PolicySet::decode(pbytes.as_slice()) {
            if ps.to_string().contains(substr) {
                return Some((schema_bytes, pbytes, ps));
            }
        }
        pos += plen;
    }
    None
}

fn repro(name: &str, strategy: &str, size: u32, base: u64, span: u64, substr: &str) {
    println!("\n########## {name}  (strategy={strategy} size={size} base~{base}) ##########");
    let ffi = CedarLeanFfi::new();
    let mut found = None;
    let mut seed = base;
    while seed < base + span {
        if let Some(hit) = scan_batch(&ffi, strategy, size, seed, substr) {
            println!("MATCH at seed {seed}");
            found = Some((seed, hit));
            break;
        }
        seed += 100;
    }
    let (seed, (schema_bytes, policy_bytes, ps)) = match found {
        Some(x) => x,
        None => { println!("NOT FOUND scanning [{base}, {}] for {substr:?}", base + span); return; }
    };
    let tag = name.replace(' ', "_");
    std::fs::write(format!("/tmp/{tag}.schema.pb"), &schema_bytes).ok();
    std::fs::write(format!("/tmp/{tag}.policy.pb"), &policy_bytes).ok();
    println!("policy: {}", ps.to_string().trim());
    match Schema::decode(schema_bytes.as_slice()) {
        Ok(schema) => {
            let r = Validator::new(schema).validate(&ps, ValidationMode::Strict);
            println!("RUST validation_passed={}", r.validation_passed());
            for e in r.validation_errors() { println!("  RUST ERR: {e}"); }
        }
        Err(e) => println!("schema decode err: {e}"),
    }
    println!("(saved /tmp/{tag}.schema.pb + .policy.pb ; seed={seed})");
}

fn main() {
    // (name, strategy, size, base≈start_seed(rep*1e9)+valid@crash, span, substr)
    // Per-rep seed offset is rep_id*1_000_000 (hardcoded in experiment.rs), so
    // base = rep*1_000_000 + valid@crash.
    let jobs: &[(&str, &str, u32, u64, u64, &str)] = &[
        ("bug1", "steep-tags",   12,  0 + 16_730_000,        15_000, "(principal in e::d::\"owner\")"),
        ("bug2", "steep-tags",   12, 17_000_000 +  1_660_000, 15_000, "foo::\"owner\") then (resource.id)"),
        ("bug3", "steep-tags",   12, 19_000_000 + 77_120_000, 15_000, "(true && (resource in baz::owner::\"c\")"),
        ("bug4", "steep-tags",   20,  5_000_000 +  7_570_000, 15_000, "d::foo::id::\"c\") && (principal.bar)"),
        ("bug5", "steep-tags",   20, 15_000_000 +  9_170_000, 15_000, "if true then ((principal in b::\"b\")"),
        ("bug6", "typeof-check", 12,  0 +  4_920_000,        15_000, "foo::\"c\") then ((resource.getTag"),
        ("bug7", "typeof-check", 12,  5_000_000 + 11_100_000, 15_000, "(principal in a::foo::\"a\") && ((principal.owner) < 14)"),
        ("bug8", "typeof-check", 20,  5_000_000 +  3_280_000, 15_000, "(principal.e).isIpv6()"),
    ];
    for (name, strat, size, base, span, substr) in jobs {
        repro(name, strat, *size, *base, *span, substr);
    }
}

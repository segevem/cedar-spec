// Reproduce the symcc-term-never-errors crashes by replaying the welltyped generator from the
// crashing seed and running the SAME never-errors check (Rust compile + Lean asserts + structural
// compare). Dumps the offending policy (Cedar text), req_env, and the diff / Lean compile error.
//
//   symcc_repro <seed_base> <size> [max_batches] [stop_kind: mismatch|compilefail|any]
// e.g. crash1:  symcc_repro 8000000000 20 2000 compilefail
//      crash2:  symcc_repro 17000000000 12 2000 mismatch
use cedar_drt_inner::symcc::asserts_match_result;
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::proto::traits::Protobuf;
use cedar_policy::{PolicySet, Schema};
use cedar_policy_symcc::{never_errors_asserts, CompiledPolicy};

fn ru32(b: &[u8], p: usize) -> Option<(usize, usize)> {
    if p + 4 > b.len() { return None }
    Some((u32::from_le_bytes([b[p], b[p + 1], b[p + 2], b[p + 3]]) as usize, p + 4))
}

/// Decode an `encode_batch` blob into its individual `[len|payload]` entries.
fn decode_batch(data: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut pos = 0;
    while pos + 4 <= data.len() {
        let len = u32::from_le_bytes([data[pos], data[pos+1], data[pos+2], data[pos+3]]) as usize;
        pos += 4;
        if pos + len > data.len() { break }
        out.push(data[pos..pos+len].to_vec());
        pos += len;
    }
    out
}

fn main() {
    // CORPUS-REPLAY mode: `symcc_repro corpus <dir>` — decode every `batch_*.bin`
    // (each an encode_batch of `[schema_len|schema|policies]` entries) and run the
    // real Rust-vs-Lean never-errors compare on the EXACT collected policies. Dumps
    // any mismatch / Lean compile-fail with the offending policy+schema.
    if std::env::args().nth(1).as_deref() == Some("corpus") {
        let dir = std::env::args().nth(2).expect("usage: symcc_repro corpus <dir>");
        let ffi = CedarLeanFfi::new();
        let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(&dir).expect("read dir")
            .filter_map(|e| e.ok()).map(|e| e.path())
            .filter(|p| p.extension().map(|x| x == "bin").unwrap_or(false)).collect();
        files.sort();
        eprintln!("corpus replay: {} batch files in {dir}", files.len());
        let (mut checked, mut mism, mut cf) = (0u64, 0u64, 0u64);
        for (fi, f) in files.iter().enumerate() {
            let data = match std::fs::read(f) { Ok(d) => d, Err(_) => continue };
            for entry in decode_batch(&data) {
                let (slen, pos) = match ru32(&entry, 0) { Some(x) => x, None => continue };
                if pos + slen > entry.len() { continue }
                let schema = match Schema::decode(&entry[pos..pos + slen]) { Ok(s) => s, Err(_) => continue };
                let ps = match PolicySet::decode(&entry[pos + slen..]) { Ok(p) => p, Err(_) => continue };
                let lean_schema = match ffi.load_lean_schema_object(&schema) { Ok(s) => s, Err(_) => continue };
                for req_env in schema.request_envs() {
                    for policy in ps.policies() {
                        let Ok(compiled) = CompiledPolicy::compile(policy, &req_env, &schema) else { continue };
                        checked += 1;
                        let rust_asserts = never_errors_asserts(&compiled);
                        match ffi.asserts_of_check_never_errors(policy, lean_schema.clone(), &req_env) {
                            Ok(Ok(lean_asserts)) => {
                                if let Err(diff) = asserts_match_result(rust_asserts, lean_asserts) {
                                    mism += 1;
                                    eprintln!("\n########## MISMATCH (file={} req_env={req_env:?}) ##########", f.display());
                                    eprintln!("-- policy --\n{policy}");
                                    eprintln!("-- schema --\n{schema:?}");
                                    eprintln!("-- diff (8k) --\n{}", &diff.chars().take(8000).collect::<String>());
                                }
                            }
                            Ok(Err(e)) => eprintln!("[{}] lean encode err: {e}", f.display()),
                            Err(e) => {
                                cf += 1;
                                eprintln!("\n########## LEAN COMPILE-FAIL (file={} req_env={req_env:?}) ##########", f.display());
                                eprintln!("-- error --\n{e}");
                                eprintln!("-- policy --\n{policy}");
                            }
                        }
                    }
                }
            }
            if fi % 20 == 0 { eprintln!("  ..file {fi}/{} (checked {checked}, mism {mism}, compilefail {cf})", files.len()); }
        }
        eprintln!("\nCORPUS DONE: checked={checked} mismatches={mism} compilefails={cf}");
        return;
    }

    // ENCODE-DETERMINISM check: `symcc_repro encmd5 <dir>` — decode each corpus policy, RE-ENCODE it
    // via Protobuf (the same path cedar-lean-ffi uses to hand policies to Lean) and print the byte
    // length + a cheap checksum. Run across many fresh processes: if the checksum varies, the proto
    // encoding is non-deterministic (prost HashMap map-field iteration), which is the root cause.
    if std::env::args().nth(1).as_deref() == Some("encmd5") {
        let dir = std::env::args().nth(2).expect("usage: symcc_repro encmd5 <dir>");
        let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(&dir).expect("read dir")
            .filter_map(|e| e.ok()).map(|e| e.path())
            .filter(|p| p.extension().map(|x| x == "bin").unwrap_or(false)).collect();
        files.sort();
        let mut sum: u64 = 0;
        let mut total = 0usize;
        for f in &files {
            let data = match std::fs::read(f) { Ok(d) => d, Err(_) => continue };
            for entry in decode_batch(&data) {
                let (slen, pos) = match ru32(&entry, 0) { Some(x) => x, None => continue };
                if pos + slen > entry.len() { continue }
                let ps = match PolicySet::decode(&entry[pos + slen..]) { Ok(p) => p, Err(_) => continue };
                let bytes = ps.encode();
                // order-sensitive rolling checksum of the re-encoded bytes
                let mut h: u64 = 1469598103934665603;
                for b in &bytes { h = (h ^ *b as u64).wrapping_mul(1099511628211); }
                sum ^= h.rotate_left((total % 61) as u32);
                total += bytes.len();
            }
        }
        println!("ENCSUM={sum:016x} totalbytes={total}");
        return;
    }

    // CORPUS SIG-SCAN (fast, Rust-only): `symcc_repro corpus-sig <dir> <needle>` — over EVERY
    // batch_*.bin, compile only the deterministic Rust `never_errors` term (NO Lean call) and report
    // any policy whose term contains <needle>. Lets us scan the whole 12GB corpus in minutes to prove
    // presence/absence of the exact crash-signature policy.
    if std::env::args().nth(1).as_deref() == Some("corpus-sig") {
        let dir = std::env::args().nth(2).expect("usage: symcc_repro corpus-sig <dir> <needle>");
        let needle = std::env::args().nth(3).expect("need <needle>");
        let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(&dir).expect("read dir")
            .filter_map(|e| e.ok()).map(|e| e.path())
            .filter(|p| p.extension().map(|x| x == "bin").unwrap_or(false)).collect();
        files.sort();
        eprintln!("corpus-sig: {} batch files in {dir}, needle={needle:?}", files.len());
        let (mut checked, mut hits) = (0u64, 0u64);
        for (fi, f) in files.iter().enumerate() {
            let data = match std::fs::read(f) { Ok(d) => d, Err(_) => continue };
            for entry in decode_batch(&data) {
                let (slen, pos) = match ru32(&entry, 0) { Some(x) => x, None => continue };
                if pos + slen > entry.len() { continue }
                let schema = match Schema::decode(&entry[pos..pos + slen]) { Ok(s) => s, Err(_) => continue };
                let ps = match PolicySet::decode(&entry[pos + slen..]) { Ok(p) => p, Err(_) => continue };
                for req_env in schema.request_envs() {
                    for policy in ps.policies() {
                        let Ok(compiled) = CompiledPolicy::compile(policy, &req_env, &schema) else { continue };
                        checked += 1;
                        let term = never_errors_asserts(&compiled).asserts().as_ref().iter()
                            .map(|t| t.to_string()).collect::<Vec<_>>().join("\n");
                        if term.contains(needle.as_str()) {
                            hits += 1;
                            eprintln!("\n########## SIG HIT (file={} req_env={req_env:?}) ##########", f.display());
                            eprintln!("-- policy --\n{policy}");
                            eprintln!("-- schema --\n{schema:?}");
                            eprintln!("-- term (8k) --\n{}", &term.chars().take(8000).collect::<String>());
                        }
                    }
                }
            }
            if fi % 500 == 0 { eprintln!("  ..file {fi}/{} (checked {checked}, hits {hits})", files.len()); }
        }
        eprintln!("\nCORPUS-SIG DONE: files={} checked={checked} hits={hits}", files.len());
        return;
    }

    // WORKER-THREAD generation dump: `symcc_repro types-worker <seed> <size> <batches>` — generate
    // through the REAL `TimeoutFfi` (the throughput probe's worker-thread path) and dump per-batch
    // request-env types, so we can diff against main-thread `types` for the same seed. If they differ,
    // the throughput probe's stream != collect/symcc_repro's stream for the same seed.
    if std::env::args().nth(1).as_deref() == Some("types-worker") {
        let seed_base: u64 = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(17000000000);
        let size: u32 = std::env::args().nth(3).and_then(|s| s.parse().ok()).unwrap_or(12);
        let batches: u64 = std::env::args().nth(4).and_then(|s| s.parse().ok()).unwrap_or(30);
        let tf = cedar_drt_coverage::timeout_ffi::TimeoutFfi::new();
        for b in 0..batches {
            let seed = seed_base + b * 100;
            let params = serde_json::json!({"seed":seed,"size":size,"schema_size":size,"strategy":"welltyped-policy","count":100u32});
            let buf = match tf.generate_schema_typeof_proto(&params) { Some(x) if x.len() >= 4 => x, _ => { eprintln!("batch={b} seed={seed} <gen failed>"); continue } };
            let (slen, pos) = match ru32(&buf, 0) { Some(x) => x, None => continue };
            if pos + slen > buf.len() { continue }
            let schema = match Schema::decode(&buf[pos..pos + slen]) { Ok(s) => s, Err(_) => continue };
            let tys: std::collections::BTreeSet<String> = schema.request_envs().map(|re| format!("{re:?}")).collect();
            eprintln!("batch={b} seed={seed} envs={tys:?}");
        }
        return;
    }

    let seed_base: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(8000000000);
    let size: u32 = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(20);
    let max_batches: u64 = std::env::args().nth(3).and_then(|s| s.parse().ok()).unwrap_or(2000);
    let stop = std::env::args().nth(4).unwrap_or_else(|| "any".into());
    // SIGNATURE-SEARCH mode: `stop == "sig:<needle>"`. Instead of the (flaky, nondeterministic)
    // Rust-vs-Lean compare, compute ONLY the deterministic Rust `never_errors` term and print the
    // policy+schema+req_env whenever the term string CONTAINS <needle>. Lets us pin the offending
    // policy from a seed without needing the mismatch to fire.
    let sig: Option<String> = stop.strip_prefix("sig:").map(|s| s.to_string());
    let ffi = CedarLeanFfi::new();
    let (mut compilefails, mut mismatches, mut checked) = (0u64, 0u64, 0u64);
    eprintln!("repro: seed_base={seed_base} size={size} stop={stop}");
    'outer: for b in 0..max_batches {
        let seed = seed_base + b * 100;
        let params = serde_json::json!({"seed":seed,"size":size,"schema_size":size,"strategy":"welltyped-policy","count":100u32});
        let buf = match ffi.generate_schema_typeof_proto(&params) { Ok(x) if x.len() >= 4 => x, _ => continue };
        let (slen, pos) = match ru32(&buf, 0) { Some(x) => x, None => continue };
        if pos + slen > buf.len() { continue }
        let schema = match Schema::decode(&buf[pos..pos + slen]) { Ok(s) => s, Err(_) => continue };
        let mut pos = pos + slen;
        let (cnt, np) = match ru32(&buf, pos) { Some(x) => x, None => continue }; pos = np;
        // TYPES-dump mode: print the entity-type names of each batch's schema and continue.
        // Lets us verify whether a given entity type (e.g. `b::id`) is generated at these seeds.
        if stop == "types" {
            let tys: std::collections::BTreeSet<String> = schema.request_envs()
                .map(|re| format!("{re:?}"))
                .collect();
            eprintln!("batch={b} seed={seed} envs={tys:?}");
            continue;
        }
        let lean_schema = match ffi.load_lean_schema_object(&schema) { Ok(s) => s, Err(_) => continue };
        for pi in 0..cnt {
            let (plen, np) = match ru32(&buf, pos) { Some(x) => x, None => break }; pos = np;
            if pos + plen > buf.len() { break }
            let ps = match PolicySet::decode(&buf[pos..pos + plen]) { Ok(p) => p, Err(_) => { pos += plen; continue } };
            pos += plen;
            for req_env in schema.request_envs() {
                for policy in ps.policies() {
                    let Ok(compiled) = CompiledPolicy::compile(policy, &req_env, &schema) else { continue };
                    checked += 1;
                    let rust_asserts = never_errors_asserts(&compiled);
                    if let Some(ref needle) = sig {
                        let term_str = rust_asserts.asserts().as_ref().iter()
                            .map(|t| t.to_string()).collect::<Vec<_>>().join("\n");
                        if term_str.contains(needle.as_str()) {
                            mismatches += 1;
                            eprintln!("\n################ SIG MATCH (seed={seed} batch={b} policy_idx={pi}) ################");
                            eprintln!("-- req_env --\n{req_env:?}");
                            eprintln!("-- policy --\n{policy}");
                            eprintln!("-- schema --\n{schema:?}");
                            eprintln!("-- rust term (truncated 8k) --\n{}", &term_str.chars().take(8000).collect::<String>());
                            break 'outer;
                        }
                        continue;
                    }
                    match ffi.asserts_of_check_never_errors(policy, lean_schema.clone(), &req_env) {
                        Ok(Ok(lean_asserts)) => {
                            if let Err(diff) = asserts_match_result(rust_asserts, lean_asserts) {
                                mismatches += 1;
                                eprintln!("\n################ MISMATCH (seed={seed} batch={b} policy_idx={pi}) ################");
                                eprintln!("-- req_env --\n{req_env:?}");
                                eprintln!("-- policy --\n{policy}");
                                eprintln!("-- schema --\n{schema:?}");
                                eprintln!("-- diff (truncated 4k) --\n{}", &diff.chars().take(4000).collect::<String>());
                                if stop != "compilefail" { break 'outer }
                            }
                        }
                        Ok(Err(e)) => eprintln!("[seed={seed}] lean encode err: {e}"),
                        Err(e) => {
                            compilefails += 1;
                            eprintln!("\n################ LEAN COMPILE-FAIL (seed={seed} batch={b} policy_idx={pi}) ################");
                            eprintln!("-- error --\n{e}");
                            eprintln!("-- req_env --\n{req_env:?}");
                            eprintln!("-- policy --\n{policy}");
                            eprintln!("-- schema --\n{schema:?}");
                            if stop != "mismatch" { break 'outer }
                        }
                    }
                }
            }
        }
        if b % 50 == 0 { eprintln!("  ..batch {b} (checked {checked}, compilefails {compilefails}, mismatches {mismatches})"); }
    }
    eprintln!("\nDONE: checked={checked} compilefails={compilefails} mismatches={mismatches}");
}

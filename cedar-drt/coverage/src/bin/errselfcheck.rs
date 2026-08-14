// COMPILED self-check of the ill-typed generator: generate + validate in-Lean (no proto
// round-trip). Isolates generator soundness. Prints per-seed counts and reprs of accepted
// (i.e. unsound = well-typed) policies so we can see which constructors are involved.
use cedar_lean_ffi::CedarLeanFfi;

fn main() {
    let n_seeds: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(10);
    let count: u64 = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let size: u64 = std::env::args().nth(3).and_then(|s| s.parse().ok()).unwrap_or(20);
    let dump = std::env::var("DUMP").is_ok();
    let ffi = CedarLeanFfi::new();
    let (mut tot_gen, mut tot_rej, mut tot_acc) = (0i64, 0i64, 0i64);
    let mut shown = 0;
    for s in 0..n_seeds {
        let seed = s * 100;
        let params = serde_json::json!({"seed":seed,"size":size,"schema_size":size,"count":count});
        let buf = match ffi.illtyped_self_check(&params) { Ok(b) => b, Err(e) => { eprintln!("seed {seed}: ffi err {e:?}"); continue } };
        let txt = String::from_utf8_lossy(&buf);
        let j: serde_json::Value = match serde_json::from_str(&txt) { Ok(v) => v, Err(_) => { eprintln!("seed {seed}: bad json: {txt}"); continue } };
        let envs = j["envs"].as_i64().unwrap_or(-1);
        let gen = j["generated"].as_i64().unwrap_or(0);
        let rej = j["rejected"].as_i64().unwrap_or(0);
        let acc = j["accepted"].as_i64().unwrap_or(0);
        tot_gen += gen; tot_rej += rej; tot_acc += acc;
        eprintln!("seed {seed:>6}: envs={envs} generated={gen} rejected={rej} ACCEPTED(unsound)={acc}");
        if dump {
            if let Some(samples) = j["samples"].as_array() {
                for smp in samples {
                    if shown >= 20 { break }
                    shown += 1;
                    eprintln!("  UNSOUND #{shown}: {}", smp.as_str().unwrap_or(""));
                }
            }
        }
    }
    let pct = if tot_gen > 0 { 100.0 * tot_acc as f64 / tot_gen as f64 } else { 0.0 };
    eprintln!("\nTOTAL: generated={tot_gen} rejected={tot_rej} ACCEPTED(unsound)={tot_acc}  ({pct:.1}% unsound)");
}

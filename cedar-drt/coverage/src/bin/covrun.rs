// Instrumented 30s run: generate welltyped policies via FFI + validate (Rust) to
// measure cedar_policy_core::validator::typecheck coverage from OUR generator.
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::proto::traits::Protobuf;
use cedar_policy::{PolicySet, Schema, ValidationMode, Validator};
fn ru32(b:&[u8],p:usize)->Option<(usize,usize)>{ if p+4>b.len(){return None} Some((u32::from_le_bytes([b[p],b[p+1],b[p+2],b[p+3]]) as usize,p+4)) }
fn main(){
    let secs: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(30);
    let ffi = CedarLeanFfi::new();
    let t0 = std::time::Instant::now();
    let mut seed: u64 = 0; let (mut nb, mut np) = (0u64, 0u64);
    while t0.elapsed().as_secs() < secs {
        let params = serde_json::json!({"seed":seed,"size":20u32,"schema_size":20u32,"strategy":"welltyped-policy","count":100u32});
        seed += 100;
        let buf = match ffi.generate_schema_typeof_proto(&params){ Ok(b) if b.len()>=4 => b, _ => continue };
        let (slen,pos)=match ru32(&buf,0){Some(x)=>x,None=>continue};
        if pos+slen>buf.len(){continue}
        let schema = match Schema::decode(&buf[pos..pos+slen]){Ok(s)=>s,Err(_)=>continue};
        let mut pos=pos+slen;
        let (cnt,pp)=match ru32(&buf,pos){Some(x)=>x,None=>continue}; pos=pp;
        let v = Validator::new(schema);
        for _ in 0..cnt {
            let (plen,pp)=match ru32(&buf,pos){Some(x)=>x,None=>break}; pos=pp;
            if pos+plen>buf.len(){break}
            if let Ok(ps)=PolicySet::decode(&buf[pos..pos+plen]){ let _=v.validate(&ps, ValidationMode::Strict); np+=1; }
            pos+=plen;
        }
        nb+=1;
    }
    eprintln!("covrun: {} batches, {} policies validated in {:?}", nb, np, t0.elapsed());
}

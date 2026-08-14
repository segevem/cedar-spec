//! Decode a violation's schema.bin + policies.bin, dump Rust's entity hierarchy,
//! and run BOTH validators (Rust cedar-policy + Lean FFI) to confirm the mismatch
//! on the isolated input. Usage: probe_bug <schema.bin> <policies.bin>
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::proto::traits::Protobuf;
use cedar_policy::{PolicySet, Schema, ValidationMode, Validator};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let sb = std::fs::read(&args[1]).expect("read schema");
    let pb = std::fs::read(&args[2]).expect("read policies");
    let schema = Schema::decode(sb.as_slice()).expect("decode schema");
    let ps = PolicySet::decode(pb.as_slice()).expect("decode policies");

    println!("=== POLICY ===\n{ps}\n");
    // Rust ValidatorSchema Debug shows each entity's `descendants`.
    println!("=== RUST SCHEMA (Debug: descendants view) ===\n{schema:?}\n");

    let rust = Validator::new(schema.clone()).validate(&ps, ValidationMode::Strict);
    println!("=== RUST validate passed = {} ===", rust.validation_passed());
    for e in rust.validation_errors() {
        println!("  RUST ERR: {e}");
    }

    let ffi = CedarLeanFfi::new();
    match ffi.validate(&ps, &schema, &ValidationMode::Strict) {
        Ok(r) => println!("=== LEAN validate (original policy) = {r:?} ==="),
        Err(e) => println!("=== LEAN validate FFI error: {e} ==="),
    }

    // Discriminator: strip the `in`-guard. If Lean now REJECTS bare `principal.b`,
    // it DOES enumerate the principal=owner env → the bug is the `in` short-circuit
    // (descendentOf). If it still ACCEPTS, it never checks that env (enumeration).
    if args.len() > 3 {
        let bare: PolicySet = args[3].parse().expect("parse bare policy");
        println!("\n=== DISCRIMINATOR policy ===\n{bare}");
        let rr = Validator::new(schema.clone()).validate(&bare, ValidationMode::Strict);
        println!("RUST bare passed = {}", rr.validation_passed());
        match ffi.validate(&bare, &schema, &ValidationMode::Strict) {
            Ok(r) => println!("LEAN bare = {r:?}"),
            Err(e) => println!("LEAN bare FFI error: {e}"),
        }
    }
}

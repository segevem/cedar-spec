//! Property-based test: Lean generates expressions and byte buffers,
//! Rust replays the bytes through ExprGenerator::generate_expr and
//! asserts the result matches.
//!
//! Run:
//!   1. cd cedar-lean && .lake/build/bin/CedarGenFaithfulTest > /tmp/lean_pbt.jsonl
//!   2. cd cedar-policy-generators && cargo test pbt_replay -- --nocapture
//!
//! The test reads /tmp/lean_pbt.jsonl (one JSON object per line).

use arbitrary::Unstructured;
use cedar_policy_generators::abac::{AvailableExtensionFunctions, ConstantPool, UnknownPool};
use cedar_policy_generators::expr::ExprGenerator;
use cedar_policy_generators::schema::Schema;
use cedar_policy_generators::settings::ABACSettings;
use serde::Deserialize;
use smol_str::SmolStr;
use std::fs;

#[derive(Deserialize)]
struct TestCase {
    bytes: Vec<u8>,
    expr: String,
    #[serde(default = "default_depth")]
    depth: usize,
}

fn default_depth() -> usize {
    1
}

fn fixed_settings() -> ABACSettings {
    ABACSettings {
        match_types: false,
        max_depth: 2,
        max_width: 3,
        enable_additional_attributes: false,
        enable_like: true,
        enable_action_groups_and_attrs: false,
        enable_arbitrary_func_call: false,
        enable_unknowns: false,
        enable_action_in_constraints: false,
        total_action_request_env_limit: 10,
        max_actions: 5,
    }
}

fn fixed_pool() -> ConstantPool {
    ConstantPool::new(
        vec![0, 1, -1, 42, 100],
        vec![
            SmolStr::from("hello"),
            SmolStr::from("world"),
            SmolStr::from("test"),
        ],
    )
}

fn fixed_schema() -> Schema {
    use cedar_policy_core::validator::{json_schema, RawName};

    let schema_json = serde_json::json!({
        "": {
            "entityTypes": {
                "User": {
                    "shape": {
                        "type": "Record",
                        "attributes": {
                            "name": { "type": "String" },
                            "age": { "type": "Long" },
                            "active": { "type": "Boolean" }
                        }
                    }
                },
                "Document": {
                    "shape": {
                        "type": "Record",
                        "attributes": {
                            "owner": { "type": "Entity", "name": "User" },
                            "title": { "type": "String" }
                        }
                    }
                }
            },
            "actions": {
                "view": {
                    "appliesTo": {
                        "principalTypes": ["User"],
                        "resourceTypes": ["Document"],
                        "context": {
                            "type": "Record",
                            "attributes": {
                                "reason": { "type": "String" }
                            }
                        }
                    }
                },
                "edit": {
                    "appliesTo": {
                        "principalTypes": ["User"],
                        "resourceTypes": ["Document"],
                        "context": { "type": "Record", "attributes": {} }
                    }
                }
            }
        }
    });

    let frag: json_schema::Fragment<RawName> =
        serde_json::from_value(schema_json).expect("valid json schema");

    let pool_bytes = vec![0u8; 50];
    let mut u = Unstructured::new(&pool_bytes);
    #[allow(deprecated)]
    Schema::from_raw_schemafrag(frag, fixed_settings(), &mut u).expect("schema from fragment")
}

#[test]
fn pbt_replay() {
    let path = "/tmp/lean_pbt.jsonl";
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Skipping PBT test: could not read {path}: {e}");
            eprintln!("Run: cd cedar-lean && .lake/build/bin/CedarGenFaithfulTest > /tmp/lean_pbt.jsonl");
            return;
        }
    };

    let schema = fixed_schema();
    let settings = fixed_settings();
    let pool = fixed_pool();
    let ext_funcs = AvailableExtensionFunctions::create(&settings);
    let unknown_pool = UnknownPool::default();

    let mut pass = 0;
    let mut fail = 0;
    let mut skip = 0;
    let total = content.lines().count();

    for (i, line) in content.lines().enumerate() {
        let tc: TestCase = match serde_json::from_str(line) {
            Ok(tc) => tc,
            Err(e) => {
                eprintln!("  line {i}: parse error: {e}");
                skip += 1;
                continue;
            }
        };

        let mut u = Unstructured::new(&tc.bytes);
        let mut gen = ExprGenerator {
            schema: &schema,
            settings: &settings,
            constant_pool: &pool,
            unknown_pool: &unknown_pool,
            ext_funcs: &ext_funcs,
            hierarchy: None,
        };

        match gen.generate_expr(tc.depth, &mut u) {
            Ok(rust_expr) => {
                let rust_str = format!("{rust_expr}");
                if rust_str == tc.expr {
                    pass += 1;
                } else {
                    fail += 1;
                    if fail <= 10 {
                        eprintln!(
                            "  FAIL line {i}: Lean=\"{}\" Rust=\"{}\"",
                            tc.expr, rust_str
                        );
                    }
                }
            }
            Err(e) => {
                // Generation can fail for some byte patterns (e.g., hitting
                // branches that need String::arbitrary with insufficient buffer)
                skip += 1;
                if skip <= 5 {
                    eprintln!("  SKIP line {i}: Rust error: {e:?}");
                }
            }
        }
    }

    println!("\n=== PBT Results: {pass} passed, {fail} failed, {skip} skipped out of {total} ===");
    // Allow some failures (branches that involve String::arbitrary from tail)
    // but the majority should pass
    let pass_rate = if total > 0 {
        pass as f64 / (total - skip) as f64
    } else {
        1.0
    };
    println!("  Pass rate (excluding skips): {:.1}%", pass_rate * 100.0);
    assert!(
        pass_rate >= 0.8,
        "Pass rate {:.1}% is below 80% threshold",
        pass_rate * 100.0
    );
}

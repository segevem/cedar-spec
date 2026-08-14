use std::collections::HashMap;
use rand::{SeedableRng, RngCore, rngs::SmallRng};
use arbitrary::Unstructured;
use cedar_policy_generators::{schema, settings::ABACSettings};
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy::Schema;
use arbitrary::Arbitrary;

fn main() {
    let sizes: Vec<usize> = vec![32, 64, 128, 256, 512, 1024, 65536];
    let attempts = 10000u64;

    for sz in sizes {
        let mut hierarchy_errors: HashMap<String, u64> = HashMap::new();
        let mut policy_errors: HashMap<String, u64> = HashMap::new();
        let mut convert_errors: HashMap<String, u64> = HashMap::new();
        let mut success = 0u64;
        let mut schema_fail = 0u64;

        for seed in 0..attempts {
            let mut rng = SmallRng::seed_from_u64(seed);
            let mut buf = vec![0u8; sz];
            rng.fill_bytes(&mut buf);
            let mut u = Unstructured::new(&buf);

            let settings = ABACSettings {
                enable_additional_attributes: true,
                ..ABACSettings::type_directed()
            };
            let gen_schema = match schema::Schema::arbitrary(settings, &mut u) {
                Ok(s) => s,
                Err(e) => {
                    schema_fail += 1;
                    let _ = e;
                    continue;
                }
            };
            let hierarchy = match gen_schema.arbitrary_hierarchy(&mut u) {
                Ok(h) => h,
                Err(e) => {
                    let key = format!("{}", e);
                    *hierarchy_errors.entry(key).or_insert(0) += 1;
                    continue;
                }
            };
            match gen_schema.arbitrary_policy(&hierarchy, &mut u) {
                Ok(_) => {},
                Err(e) => {
                    let key = format!("{}", e);
                    *policy_errors.entry(key).or_insert(0) += 1;
                    continue;
                }
            };
            match Schema::try_from(gen_schema) {
                Ok(_) => {},
                Err(e) => {
                    let key = format!("{}", e);
                    *convert_errors.entry(key).or_insert(0) += 1;
                    continue;
                }
            };
            success += 1;
        }

        println!("\n=== Buffer size: {} bytes ({} success / {} attempts = {:.1}%) ===",
            sz, success, attempts, success as f64 / attempts as f64 * 100.0);

        if schema_fail > 0 {
            println!("  Schema failures: {}", schema_fail);
        }

        if !hierarchy_errors.is_empty() {
            println!("  Hierarchy failures ({} total):", hierarchy_errors.values().sum::<u64>());
            let mut sorted: Vec<_> = hierarchy_errors.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            for (err, count) in sorted.iter().take(5) {
                let truncated: String = err.chars().take(100).collect();
                println!("    {:>5} - {}", count, truncated);
            }
        }

        if !policy_errors.is_empty() {
            println!("  Policy failures ({} total):", policy_errors.values().sum::<u64>());
            let mut sorted: Vec<_> = policy_errors.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            for (err, count) in sorted.iter().take(5) {
                let truncated: String = err.chars().take(100).collect();
                println!("    {:>5} - {}", count, truncated);
            }
        }

        if !convert_errors.is_empty() {
            println!("  Convert failures ({} total):", convert_errors.values().sum::<u64>());
            let mut sorted: Vec<_> = convert_errors.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            for (err, count) in sorted.iter().take(5) {
                let truncated: String = err.chars().take(100).collect();
                println!("    {:>5} - {}", count, truncated);
            }
        }
    }
}

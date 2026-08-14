use std::collections::HashMap;
use std::path::PathBuf;
use arbitrary::Unstructured;
use cedar_policy_generators::{schema, settings::ABACSettings};
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy::Schema;
use arbitrary::Arbitrary;

fn main() {
    let corpus_dir = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("Usage: diagnose_corpus <corpus_dir>");
        std::process::exit(1);
    });

    let mut files: Vec<PathBuf> = std::fs::read_dir(&corpus_dir)
        .expect("failed to read corpus dir")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_file())
        .collect();
    files.sort();

    let settings = ABACSettings {
        enable_additional_attributes: true,
        ..ABACSettings::type_directed()
    };

    let mut schema_fail: HashMap<String, u64> = HashMap::new();
    let mut hierarchy_fail: HashMap<String, u64> = HashMap::new();
    let mut policy_fail: HashMap<String, u64> = HashMap::new();
    let mut convert_fail: HashMap<String, u64> = HashMap::new();
    let mut success = 0u64;
    let mut total = 0u64;

    for path in &files {
        let buf = match std::fs::read(path) {
            Ok(b) => b,
            Err(_) => continue,
        };
        total += 1;

        let mut u = Unstructured::new(&buf);

        let gen_schema = match schema::Schema::arbitrary(settings.clone(), &mut u) {
            Ok(s) => s,
            Err(e) => {
                let key = format!("{}", e);
                *schema_fail.entry(key).or_insert(0) += 1;
                continue;
            }
        };
        let hierarchy = match gen_schema.arbitrary_hierarchy(&mut u) {
            Ok(h) => h,
            Err(e) => {
                let key = format!("{}", e);
                *hierarchy_fail.entry(key).or_insert(0) += 1;
                continue;
            }
        };
        match gen_schema.arbitrary_policy(&hierarchy, &mut u) {
            Ok(_) => {},
            Err(e) => {
                let key = format!("{}", e);
                *policy_fail.entry(key).or_insert(0) += 1;
                continue;
            }
        };
        match Schema::try_from(gen_schema) {
            Ok(_) => {},
            Err(e) => {
                let key = format!("{:?}", e);
                *convert_fail.entry(key).or_insert(0) += 1;
                continue;
            }
        };
        success += 1;
    }

    let sf_total: u64 = schema_fail.values().sum();
    let hf_total: u64 = hierarchy_fail.values().sum();
    let pf_total: u64 = policy_fail.values().sum();
    let cf_total: u64 = convert_fail.values().sum();

    println!("=== Corpus replay: {} files ===", total);
    println!("  Success:   {:>6} ({:.1}%)", success, success as f64 / total as f64 * 100.0);
    println!("  Schema:    {:>6} ({:.1}%)", sf_total, sf_total as f64 / total as f64 * 100.0);
    println!("  Hierarchy: {:>6} ({:.1}%)", hf_total, hf_total as f64 / total as f64 * 100.0);
    println!("  Policy:    {:>6} ({:.1}%)", pf_total, pf_total as f64 / total as f64 * 100.0);
    println!("  Convert:   {:>6} ({:.1}%)", cf_total, cf_total as f64 / total as f64 * 100.0);

    if !schema_fail.is_empty() {
        println!("\n  Schema errors:");
        let mut sorted: Vec<_> = schema_fail.iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(a.1));
        for (err, count) in sorted.iter().take(5) {
            let truncated: String = err.chars().take(100).collect();
            println!("    {:>5} - {}", count, truncated);
        }
    }

    if !hierarchy_fail.is_empty() {
        println!("\n  Hierarchy errors:");
        let mut sorted: Vec<_> = hierarchy_fail.iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(a.1));
        for (err, count) in sorted.iter().take(5) {
            let truncated: String = err.chars().take(100).collect();
            println!("    {:>5} - {}", count, truncated);
        }
    }

    if !policy_fail.is_empty() {
        println!("\n  Policy errors:");
        let mut sorted: Vec<_> = policy_fail.iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(a.1));
        for (err, count) in sorted.iter().take(5) {
            let truncated: String = err.chars().take(100).collect();
            println!("    {:>5} - {}", count, truncated);
        }
    }

    if !convert_fail.is_empty() {
        println!("\n  Convert errors:");
        let mut sorted: Vec<_> = convert_fail.iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(a.1));
        for (err, count) in sorted.iter().take(10) {
            println!("    {:>5} - {}", count, err);
        }
    }
}

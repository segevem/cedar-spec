#![no_main]

use cedar_policy::{Schema, ValidationMode, Validator};
use cedar_policy_generators::{schema, schema_gen::SchemaGen, settings::ABACSettings};
use libfuzzer_sys::arbitrary::Unstructured;
use libfuzzer_sys::fuzz_target;
use rand::{RngCore, SeedableRng, rngs::SmallRng};

use std::sync::atomic::{AtomicU64, Ordering};

static VALID_COUNT: AtomicU64 = AtomicU64::new(0);
static ATTEMPT_COUNT: AtomicU64 = AtomicU64::new(0);
// Track how often each (buf_size_idx, depth_idx) pair is selected by the fuzzer
// 8 buf sizes × 5 depths = 40 slots
static CONFIG_COUNTS: [AtomicU64; 40] = {
    const ZERO: AtomicU64 = AtomicU64::new(0);
    [ZERO; 40]
};

/// The fuzzer evolves 5 bytes: (buf_size, depth, width, seed_hi, seed_lo).
/// The 2-byte seed gives 65536 deterministic random fills per config,
/// letting the fuzzer learn specific (config, seed) pairs that hit new code.
fuzz_target!(|data: &[u8]| {
    ATTEMPT_COUNT.fetch_add(1, Ordering::Relaxed);
    if data.len() < 5 {
        return;
    }

    // Decode config from fuzzer-controlled bytes
    let buf_size_selector = data[0];
    let depth = data[1];
    let width = data[2];
    let prng_seed = u16::from_le_bytes([data[3], data[4]]) as u64;

    // Map selectors to actual values — keep it small
    let buf_idx = (buf_size_selector % 8) as usize;
    let depth_idx = (depth % 5) as usize;
    CONFIG_COUNTS[buf_idx * 5 + depth_idx].fetch_add(1, Ordering::Relaxed);

    let buf_size = match buf_size_selector % 8 {
        0 => 16,
        1 => 32,
        2 => 48,
        3 => 64,
        4 => 96,
        5 => 128,
        6 => 192,
        7 => 256,
        _ => unreachable!(),
    };
    let max_depth = ((depth % 5) + 1) as usize; // 1..=5
    let max_width = ((width % 5) + 1) as usize; // 1..=5

    let settings = ABACSettings {
        match_types: true,
        max_depth,
        max_width,
        enable_additional_attributes: true,
        enable_like: true,
        enable_action_groups_and_attrs: true,
        enable_arbitrary_func_call: true,
        enable_unknowns: false,
        enable_action_in_constraints: true,
        total_action_request_env_limit: 1024,
        max_actions: 16,
    };

    // Fill generation buffer from seed — deterministic per (config, seed) pair
    let mut rng = SmallRng::seed_from_u64(prng_seed);
    let mut buf = vec![0u8; buf_size];
    rng.fill_bytes(&mut buf);

    let mut u = Unstructured::new(&buf);

    let gen_schema = match schema::Schema::arbitrary(settings, &mut u) {
        Ok(s) => s,
        Err(_) => return,
    };
    let hierarchy = match gen_schema.arbitrary_hierarchy(&mut u) {
        Ok(h) => h,
        Err(_) => return,
    };
    let policy = match gen_schema.arbitrary_policy(&hierarchy, &mut u) {
        Ok(p) => p,
        Err(_) => return,
    };

    let schema = match Schema::try_from(gen_schema) {
        Ok(s) => s,
        Err(_) => return,
    };
    let policies = policy.into_policy_set();

    // Run the validator — this is what we're measuring coverage of
    let validator = Validator::new(schema);
    let _result = validator.validate(&policies, ValidationMode::Strict);

    let valid = VALID_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
    let attempts = ATTEMPT_COUNT.load(Ordering::Relaxed);
    if valid % 5000 == 0 {
        let buf_sizes = [16, 32, 48, 64, 96, 128, 192, 256];
        let mut counts: Vec<(usize, usize, u64)> = Vec::new();
        for bi in 0..8 {
            for di in 0..5 {
                let c = CONFIG_COUNTS[bi * 5 + di].load(Ordering::Relaxed);
                if c > 0 {
                    counts.push((buf_sizes[bi], di + 1, c));
                }
            }
        }
        counts.sort_by(|a, b| b.2.cmp(&a.2));
        eprintln!("[meta] {} valid / {} attempts. Top configs:", valid, attempts);
        for (buf, depth, count) in counts.iter().take(5) {
            eprintln!("  buf={:>4} depth={} count={}", buf, depth, count);
        }
    }
});


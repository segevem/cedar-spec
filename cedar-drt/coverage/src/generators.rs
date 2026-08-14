use std::path::PathBuf;
use std::str::FromStr;

use arbitrary::Unstructured;
use cedar_policy::{PolicySet, Schema};
use cedar_policy_generators::{schema, schema_gen::SchemaGen, settings::ABACSettings};
use rand::{Rng, RngCore, SeedableRng, rngs::SmallRng};

use crate::{ValidationGenerator, ValidationInput};

/// Generator using the existing cedar-policy-generators with type-directed
/// or undirected settings, driven by a PRNG seeded from the input seed.
pub struct ABACGenerator {
    pub name: String,
    pub settings: ABACSettings,
    pub buffer_size: usize,
}

impl ABACGenerator {
    pub fn type_directed() -> Self {
        Self {
            name: "abac-type-directed".to_string(),
            settings: ABACSettings {
                enable_additional_attributes: true,
                ..ABACSettings::type_directed()
            },
            buffer_size: 65536,
        }
    }

    pub fn undirected() -> Self {
        Self {
            name: "abac-undirected".to_string(),
            settings: ABACSettings {
                enable_additional_attributes: true,
                ..ABACSettings::undirected()
            },
            buffer_size: 65536,
        }
    }
}

impl ValidationGenerator for ABACGenerator {
    fn name(&self) -> &str {
        &self.name
    }

    fn generate(&self, seed: u64) -> Option<ValidationInput> {
        self.generate_inner(seed, false)
    }
}

impl ABACGenerator {
    pub fn generate_inner(&self, seed: u64, verbose: bool) -> Option<ValidationInput> {
        let mut rng = SmallRng::seed_from_u64(seed);
        let mut buf = vec![0u8; self.buffer_size];
        rng.fill_bytes(&mut buf);

        let mut u = Unstructured::new(&buf);

        let gen_schema: schema::Schema = match schema::Schema::arbitrary(self.settings.clone(), &mut u) {
            Ok(s) => s,
            Err(e) => {
                if verbose {
                    eprintln!("  [seed={seed}] Schema::arbitrary failed: {e}");
                }
                return None;
            }
        };
        let hierarchy = match gen_schema.arbitrary_hierarchy(&mut u) {
            Ok(h) => h,
            Err(e) => {
                if verbose {
                    eprintln!("  [seed={seed}] arbitrary_hierarchy failed: {e}");
                }
                return None;
            }
        };
        let policy = match gen_schema.arbitrary_policy(&hierarchy, &mut u) {
            Ok(p) => p,
            Err(e) => {
                if verbose {
                    eprintln!("  [seed={seed}] arbitrary_policy failed: {e}");
                }
                return None;
            }
        };

        let schema = match Schema::try_from(gen_schema) {
            Ok(s) => s,
            Err(e) => {
                if verbose {
                    eprintln!("  [seed={seed}] Schema::try_from failed: {e}");
                }
                return None;
            }
        };
        let policies = policy.into_policy_set();

        Some(ValidationInput { schema, policies, raw_bytes: Some(buf), provenance: None })
    }

    /// Run N attempts and return error breakdown counts.
    pub fn diagnose(&self, attempts: u64) -> ErrorBreakdown {
        let mut result = ErrorBreakdown::default();
        for seed in 0..attempts {
            let mut rng = SmallRng::seed_from_u64(seed);
            let mut buf = vec![0u8; self.buffer_size];
            rng.fill_bytes(&mut buf);
            let mut u = Unstructured::new(&buf);

            let gen_schema = match schema::Schema::arbitrary(self.settings.clone(), &mut u) {
                Ok(s) => s,
                Err(_) => { result.schema_fail += 1; continue; }
            };
            let hierarchy = match gen_schema.arbitrary_hierarchy(&mut u) {
                Ok(h) => h,
                Err(_) => { result.hierarchy_fail += 1; continue; }
            };
            match gen_schema.arbitrary_policy(&hierarchy, &mut u) {
                Ok(_) => {},
                Err(_) => { result.policy_fail += 1; continue; }
            };
            match Schema::try_from(gen_schema) {
                Ok(_) => {},
                Err(_) => { result.convert_fail += 1; continue; }
            };
            result.success += 1;
        }
        result
    }
}

#[derive(Default, Debug)]
pub struct ErrorBreakdown {
    pub schema_fail: u64,
    pub hierarchy_fail: u64,
    pub policy_fail: u64,
    pub convert_fail: u64,
    pub success: u64,
}

/// Same as ABACGenerator but retries with different sub-seeds until it
/// produces a valid input (up to `max_retries` attempts per seed).
pub struct RetryABACGenerator {
    pub inner: ABACGenerator,
    pub max_retries: u64,
}

impl RetryABACGenerator {
    pub fn type_directed() -> Self {
        Self {
            inner: ABACGenerator::type_directed(),
            max_retries: 100,
        }
    }

    pub fn undirected() -> Self {
        Self {
            inner: ABACGenerator::undirected(),
            max_retries: 100,
        }
    }
}

impl ValidationGenerator for RetryABACGenerator {
    fn name(&self) -> &str {
        match self.inner.name.as_str() {
            "abac-type-directed" => "retry-abac-type-directed",
            "abac-undirected" => "retry-abac-undirected",
            _ => "retry-abac",
        }
    }

    fn generate(&self, seed: u64) -> Option<ValidationInput> {
        for attempt in 0..self.max_retries {
            let sub_seed = seed.wrapping_mul(1000).wrapping_add(attempt);
            if let Some(input) = self.inner.generate_inner(sub_seed, false) {
                return Some(input);
            }
        }
        None
    }
}

/// Generator that scales buffer size AND max_depth/max_width over time.
/// Growth rate is configurable: slow vs fast.
pub struct ScalingGenerator {
    pub name: String,
    pub type_directed: bool,
    /// Buffer growth in bytes per step
    pub buf_growth: usize,
    /// How many attempts per growth step
    pub step_interval: u64,
    /// Starting buffer size
    pub min_buffer: usize,
    /// Starting max_depth
    pub min_depth: usize,
    /// How many steps before depth increases by 1
    pub depth_step_interval: u64,
}

impl ScalingGenerator {
    pub fn slow() -> Self {
        Self {
            name: "scaling-slow".to_string(),
            type_directed: true,
            buf_growth: 6,
            step_interval: 500,
            min_buffer: 32,
            min_depth: 2,
            depth_step_interval: 5000,
        }
    }

    pub fn fast() -> Self {
        Self {
            name: "scaling-fast".to_string(),
            type_directed: true,
            buf_growth: 60,
            step_interval: 50,
            min_buffer: 32,
            min_depth: 2,
            depth_step_interval: 1000,
        }
    }

    /// Stays small for 90% of attempts, then ramps up in the final 10%.
    /// Needs total_attempts hint to know where the boundary is.
    pub fn late_ramp(total_attempts: u64) -> Self {
        Self {
            name: "scaling-late-ramp".to_string(),
            type_directed: true,
            // These get overridden in generate() below
            buf_growth: 0,
            step_interval: 1,
            min_buffer: total_attempts as usize, // stash total_attempts here
            min_depth: 2,
            depth_step_interval: 1,
        }
    }
}

/// Generator that stays in the small-term space for most of its budget,
/// then ramps up for the final portion.
pub struct LateRampGenerator {
    pub name: String,
    pub type_directed: bool,
    pub small_buffer: usize,
    pub small_depth: usize,
    pub large_buffer: usize,
    pub large_depth: usize,
    /// Fraction of attempts spent in small mode (0.0 to 1.0)
    pub small_fraction: f64,
    /// Total expected attempts (used to compute the transition point)
    pub total_hint: u64,
}

impl LateRampGenerator {
    pub fn new(total_hint: u64) -> Self {
        Self {
            name: "late-ramp".to_string(),
            type_directed: true,
            small_buffer: 256,
            small_depth: 3,
            large_buffer: 65536,
            large_depth: 7,
            small_fraction: 0.9,
            total_hint,
        }
    }
}

impl ValidationGenerator for LateRampGenerator {
    fn name(&self) -> &str {
        &self.name
    }

    fn generate(&self, seed: u64) -> Option<ValidationInput> {
        let transition = (self.total_hint as f64 * self.small_fraction) as u64;
        let (buf_size, max_depth) = if seed < transition {
            (self.small_buffer, self.small_depth)
        } else {
            // Linear ramp from small to large over the remaining 10%
            let ramp_progress = (seed - transition) as f64
                / (self.total_hint - transition).max(1) as f64;
            let ramp_progress = ramp_progress.min(1.0);
            let buf = self.small_buffer
                + ((self.large_buffer - self.small_buffer) as f64 * ramp_progress) as usize;
            let depth = self.small_depth
                + ((self.large_depth - self.small_depth) as f64 * ramp_progress) as usize;
            (buf, depth)
        };

        let settings = ABACSettings {
            match_types: self.type_directed,
            max_depth,
            max_width: max_depth,
            enable_additional_attributes: true,
            enable_like: true,
            enable_action_groups_and_attrs: true,
            enable_arbitrary_func_call: true,
            enable_unknowns: false,
            enable_action_in_constraints: true,
            total_action_request_env_limit: 1024,
            max_actions: 16,
        };

        let mut rng = SmallRng::seed_from_u64(seed);
        let mut buf = vec![0u8; buf_size];
        rng.fill_bytes(&mut buf);

        let mut u = Unstructured::new(&buf);

        let gen_schema = schema::Schema::arbitrary(settings, &mut u).ok()?;
        let hierarchy = gen_schema.arbitrary_hierarchy(&mut u).ok()?;
        let policy = gen_schema.arbitrary_policy(&hierarchy, &mut u).ok()?;

        let schema = Schema::try_from(gen_schema).ok()?;
        let policies = policy.into_policy_set();

        Some(ValidationInput { schema, policies, raw_bytes: Some(buf), provenance: None })
    }
}

impl ValidationGenerator for ScalingGenerator {
    fn name(&self) -> &str {
        &self.name
    }

    fn generate(&self, seed: u64) -> Option<ValidationInput> {
        let buf_steps = (seed / self.step_interval) as usize;
        let buf_size = self.min_buffer.saturating_add(self.buf_growth.saturating_mul(buf_steps));

        let depth_steps = (seed / self.depth_step_interval) as usize;
        let max_depth = self.min_depth.saturating_add(depth_steps);
        let max_width = self.min_depth.saturating_add(depth_steps);

        let settings = ABACSettings {
            match_types: self.type_directed,
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

        let mut rng = SmallRng::seed_from_u64(seed);
        let mut buf = vec![0u8; buf_size];
        rng.fill_bytes(&mut buf);

        let mut u = Unstructured::new(&buf);

        let gen_schema = schema::Schema::arbitrary(settings, &mut u).ok()?;
        let hierarchy = gen_schema.arbitrary_hierarchy(&mut u).ok()?;
        let policy = gen_schema.arbitrary_policy(&hierarchy, &mut u).ok()?;

        let schema = Schema::try_from(gen_schema).ok()?;
        let policies = policy.into_policy_set();

        Some(ValidationInput { schema, policies, raw_bytes: Some(buf), provenance: None })
    }
}

// Keep the old name as an alias
pub type GrowingBufferGenerator = ScalingGenerator;

/// Generator where the seed encodes configuration parameters (buf_size, depth, width)
/// and a separate PRNG fills the actual generation buffer. This simulates what a
/// fuzzer targeting the config space would do.
pub struct MetaGenerator {
    pub type_directed: bool,
    /// Available buffer sizes to choose from
    pub buf_sizes: Vec<usize>,
    /// Available depths to choose from
    pub depths: Vec<usize>,
}

impl MetaGenerator {
    pub fn small() -> Self {
        Self {
            type_directed: true,
            buf_sizes: vec![16, 32, 48, 64, 96, 128, 192, 256],
            depths: vec![1, 2, 3, 4],
        }
    }
}

impl ValidationGenerator for MetaGenerator {
    fn name(&self) -> &str {
        "meta-small"
    }

    fn generate(&self, seed: u64) -> Option<ValidationInput> {
        // Decode config from seed bits
        let buf_idx = (seed as usize) % self.buf_sizes.len();
        let depth_idx = ((seed / self.buf_sizes.len() as u64) as usize) % self.depths.len();
        let prng_seed = seed / (self.buf_sizes.len() * self.depths.len()) as u64;

        let buf_size = self.buf_sizes[buf_idx];
        let max_depth = self.depths[depth_idx];

        let settings = ABACSettings {
            match_types: self.type_directed,
            max_depth,
            max_width: max_depth,
            enable_additional_attributes: true,
            enable_like: true,
            enable_action_groups_and_attrs: true,
            enable_arbitrary_func_call: true,
            enable_unknowns: false,
            enable_action_in_constraints: true,
            total_action_request_env_limit: 1024,
            max_actions: 16,
        };

        let mut rng = SmallRng::seed_from_u64(prng_seed);
        let mut buf = vec![0u8; buf_size];
        rng.fill_bytes(&mut buf);

        let mut u = Unstructured::new(&buf);

        let gen_schema = schema::Schema::arbitrary(settings, &mut u).ok()?;
        let hierarchy = gen_schema.arbitrary_hierarchy(&mut u).ok()?;
        let policy = gen_schema.arbitrary_policy(&hierarchy, &mut u).ok()?;

        let schema = Schema::try_from(gen_schema).ok()?;
        let policies = policy.into_policy_set();

        Some(ValidationInput { schema, policies, raw_bytes: Some(buf), provenance: None })
    }
}

/// A configuration bucket for the adaptive generator.
#[derive(Clone, Debug)]
pub struct GenConfig {
    pub buf_size: usize,
    pub max_depth: usize,
    pub max_width: usize,
    pub weight: f64,
    pub hits: u64,
}

/// Coverage-guided generator that tracks which configurations produce new
/// coverage and biases toward them.
pub struct AdaptiveGenerator {
    pub configs: Vec<GenConfig>,
    pub check_interval: u64,
    pub last_coverage: u64,
    pub type_directed: bool,
}

impl AdaptiveGenerator {
    pub fn new() -> Self {
        // Start with a diverse set of configurations
        let mut configs = Vec::new();
        for &buf in &[32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536] {
            for &depth in &[1, 2, 3, 4, 5, 7, 10] {
                configs.push(GenConfig {
                    buf_size: buf,
                    max_depth: depth,
                    max_width: depth,
                    weight: 1.0,
                    hits: 0,
                });
            }
        }
        Self {
            configs,
            check_interval: 200,
            last_coverage: 0,
            type_directed: true,
        }
    }

    pub fn pick_config(&self, seed: u64) -> &GenConfig {
        let total_weight: f64 = self.configs.iter().map(|c| c.weight).sum();
        let mut rng = SmallRng::seed_from_u64(seed.wrapping_mul(7919));
        let mut pick = (rng.next_u64() as f64 / u64::MAX as f64) * total_weight;
        for config in &self.configs {
            pick -= config.weight;
            if pick <= 0.0 {
                return config;
            }
        }
        self.configs.last().unwrap()
    }

    /// Called periodically to check if coverage increased and update weights.
    #[cfg(feature = "profraw")]
    pub fn update_weights(&mut self) {
        if let Some(current) = crate::get_current_coverage() {
            if current > self.last_coverage {
                let gain = current - self.last_coverage;
                // Boost weights of configs that were recently used (had hits)
                for config in &mut self.configs {
                    if config.hits > 0 {
                        config.weight += gain as f64 * config.hits as f64;
                        config.hits = 0;
                    }
                }
                self.last_coverage = current;
            } else {
                // No gain — reset hit counters
                for config in &mut self.configs {
                    config.hits = 0;
                }
            }
        }
    }

    #[cfg(not(feature = "profraw"))]
    pub fn update_weights(&mut self) {}
}

impl ValidationGenerator for AdaptiveGenerator {
    fn name(&self) -> &str {
        "adaptive"
    }

    fn generate(&self, seed: u64) -> Option<ValidationInput> {
        let config = self.pick_config(seed);

        let settings = ABACSettings {
            match_types: self.type_directed,
            max_depth: config.max_depth,
            max_width: config.max_width,
            enable_additional_attributes: true,
            enable_like: true,
            enable_action_groups_and_attrs: true,
            enable_arbitrary_func_call: true,
            enable_unknowns: false,
            enable_action_in_constraints: true,
            total_action_request_env_limit: 1024,
            max_actions: 16,
        };

        let mut rng = SmallRng::seed_from_u64(seed);
        let mut buf = vec![0u8; config.buf_size];
        rng.fill_bytes(&mut buf);

        let mut u = Unstructured::new(&buf);

        let gen_schema = schema::Schema::arbitrary(settings, &mut u).ok()?;
        let hierarchy = gen_schema.arbitrary_hierarchy(&mut u).ok()?;
        let policy = gen_schema.arbitrary_policy(&hierarchy, &mut u).ok()?;

        let schema = Schema::try_from(gen_schema).ok()?;
        let policies = policy.into_policy_set();

        Some(ValidationInput { schema, policies, raw_bytes: Some(buf), provenance: None })
    }
}

/// Replays a fuzzer corpus directory. Each "seed" indexes into the sorted
/// list of corpus files, and the file bytes are used as the Unstructured buffer.
pub struct CorpusReplayGenerator {
    pub files: Vec<PathBuf>,
    pub settings: ABACSettings,
}

impl CorpusReplayGenerator {
    pub fn new(corpus_dir: &str, settings: ABACSettings) -> Self {
        let mut files: Vec<PathBuf> = std::fs::read_dir(corpus_dir)
            .expect("failed to read corpus directory")
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.is_file())
            .collect();
        files.sort();
        eprintln!("Loaded {} corpus files from {}", files.len(), corpus_dir);
        Self { files, settings }
    }
}

impl ValidationGenerator for CorpusReplayGenerator {
    fn name(&self) -> &str {
        "corpus-replay"
    }

    fn generate(&self, seed: u64) -> Option<ValidationInput> {
        let idx = seed as usize;
        if idx >= self.files.len() {
            return None;
        }
        let buf = std::fs::read(&self.files[idx]).ok()?;
        let mut u = Unstructured::new(&buf);

        let gen_schema = schema::Schema::arbitrary(self.settings.clone(), &mut u).ok()?;
        let hierarchy = gen_schema.arbitrary_hierarchy(&mut u).ok()?;
        let policy = gen_schema.arbitrary_policy(&hierarchy, &mut u).ok()?;

        let schema = Schema::try_from(gen_schema).ok()?;
        let policies = policy.into_policy_set();

        Some(ValidationInput { schema, policies, raw_bytes: Some(buf), provenance: None })
    }
}

/// Wraps the undirected generator and sometimes mutates the policy to trigger
/// edge cases like undeclared actions or invalid enum entities.
pub struct MutatingGenerator {
    pub inner: ABACGenerator,
    pub mutation_probability: f64,
}

impl MutatingGenerator {
    pub fn new() -> Self {
        Self {
            inner: ABACGenerator::undirected(),
            mutation_probability: 0.05,
        }
    }
}

impl ValidationGenerator for MutatingGenerator {
    fn name(&self) -> &str {
        "mutating-undirected"
    }

    fn generate(&self, seed: u64) -> Option<ValidationInput> {
        let input = self.inner.generate_inner(seed, false)?;

        let mut rng = SmallRng::seed_from_u64(seed.wrapping_mul(31337));
        if rng.random::<f64>() >= self.mutation_probability {
            return Some(input);
        }

        // Apply a mutation
        let policy_text = input.policies.to_string();
        let mutated_text = match rng.random::<u8>() % 3 {
            0 => mutate_action(&policy_text, &mut rng),
            1 => mutate_entity_type(&policy_text, &mut rng),
            2 => mutate_attribute_name(&policy_text, &mut rng),
            _ => unreachable!(),
        };

        let mutated_policies = match PolicySet::from_str(&mutated_text) {
            Ok(ps) => ps,
            Err(_) => return Some(input),
        };

        Some(ValidationInput {
            schema: input.schema,
            policies: mutated_policies,
            raw_bytes: None,
            provenance: None,
        })
    }
}

fn mutate_action(policy_text: &str, _rng: &mut SmallRng) -> String {
    let needle = "Action::\"";
    if let Some(start) = policy_text.find(needle) {
        let after_action = start + needle.len();
        if let Some(close_quote) = policy_text[after_action..].find('"') {
            let end = after_action + close_quote + 1;
            return format!(
                "{}Action::\"__nonexistent__\"{}",
                &policy_text[..start],
                &policy_text[end..]
            );
        }
    }
    policy_text.to_string()
}

fn mutate_entity_type(policy_text: &str, _rng: &mut SmallRng) -> String {
    // Find a pattern like Type::"eid" and replace eid with invalid variant
    let needle = "::\"";
    if let Some(start) = policy_text.find(needle) {
        let quote_start = start + needle.len();
        if let Some(close_quote) = policy_text[quote_start..].find('"') {
            let end = quote_start + close_quote + 1;
            return format!(
                "{}::\"__bad_variant__\"{}",
                &policy_text[..start],
                &policy_text[end..]
            );
        }
    }
    policy_text.to_string()
}

fn mutate_attribute_name(policy_text: &str, _rng: &mut SmallRng) -> String {
    // Find .attr_name and replace with nonexistent attribute
    if let Some(pos) = policy_text.find(|c: char| c == '.') {
        let after_dot = &policy_text[pos + 1..];
        let attr_len = after_dot
            .find(|c: char| !c.is_alphanumeric() && c != '_')
            .unwrap_or(after_dot.len());
        if attr_len > 0 && after_dot.chars().next().map_or(false, |c| c.is_alphabetic()) {
            let end = pos + 1 + attr_len;
            return format!(
                "{}.__zzz_nonexistent{}",
                &policy_text[..pos],
                &policy_text[end..]
            );
        }
    }
    policy_text.to_string()
}

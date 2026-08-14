use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExperimentConfig {
    pub experiment_id: String,
    pub generators: Vec<GeneratorConfig>,
    pub target: TargetKind,
    pub phases: PhaseConfigs,
    #[serde(default)]
    pub cpu_pin: bool,
    #[serde(default)]
    pub seed_base: u64,
    pub output_dir: String,
    #[serde(default)]
    pub s3_bucket: Option<String>,
    #[serde(default)]
    pub s3_prefix: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GeneratorConfig {
    pub kind: GeneratorKind,
    #[serde(default)]
    pub params: GeneratorParams,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum GeneratorKind {
    TypeDirected,
    Undirected,
    RetryTypeDirected,
    RetryUndirected,
    ScalingSlow,
    ScalingFast,
    MetaSmall,
    MutatingUndirected,
    LateRamp,
    Adaptive,
    #[cfg(feature = "lean-gen")]
    LeanTypeof,
    #[cfg(feature = "lean-gen")]
    LeanSchemaTypeof,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct GeneratorParams {
    #[serde(default = "default_buffer_size")]
    pub buffer_size: usize,
    #[serde(default = "default_lean_size")]
    pub lean_size: u32,
    #[serde(default)]
    pub scoring: Option<String>,
    #[serde(default)]
    pub weighting: Option<String>,
    #[serde(default)]
    pub unconstrained_depth: Option<u32>,
    #[serde(default)]
    pub relation_budget: Option<u32>,
    /// Starting seed for the Lean schema+term generator. Each repetition sets
    /// this to a distinct value so reps draw disjoint, independent samples
    /// (required for meaningful bootstrap CIs across runs). Ignored by
    /// generators that take the seed per-call.
    #[serde(default)]
    pub start_seed: u64,
}

fn default_buffer_size() -> usize {
    65536
}

fn default_lean_size() -> u32 {
    20
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TargetKind {
    RustOnly,
    #[cfg(feature = "lean-gen")]
    ValidationDrt,
    #[cfg(feature = "lean-gen")]
    LevelValidationDrt,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PhaseConfigs {
    pub throughput: ThroughputConfig,
    #[serde(default)]
    pub collect: CollectConfig,
    #[serde(default)]
    pub analyze: AnalyzeConfig,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ThroughputConfig {
    pub duration_secs: u64,
    #[serde(default = "default_reps")]
    pub reps: u32,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CollectConfig {
    #[serde(default)]
    pub valid_count: Option<u64>,
    #[serde(default = "default_reps")]
    pub reps: u32,
    #[serde(default = "default_snapshot_interval")]
    pub snapshot_interval_secs: u64,
}

impl Default for CollectConfig {
    fn default() -> Self {
        Self {
            valid_count: None,
            reps: default_reps(),
            snapshot_interval_secs: default_snapshot_interval(),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AnalyzeConfig {
    #[serde(default)]
    pub corpus_dir: Option<String>,
    #[serde(default = "default_batch_size")]
    pub batch_size: usize,
    #[serde(default = "default_reps")]
    pub reps: u32,
}

impl Default for AnalyzeConfig {
    fn default() -> Self {
        Self {
            corpus_dir: None,
            batch_size: default_batch_size(),
            reps: default_reps(),
        }
    }
}

fn default_reps() -> u32 {
    5
}

fn default_snapshot_interval() -> u64 {
    10
}

fn default_batch_size() -> usize {
    100
}

/// A point-in-time snapshot during throughput measurement.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ThroughputSnapshot {
    pub elapsed_secs: f64,
    pub valid_count: u64,
    pub attempt_count: u64,
}

/// Result of a single throughput repetition.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ThroughputResult {
    pub rep_id: u32,
    pub generator: String,
    pub target: String,
    pub duration_secs: f64,
    pub seed: u64,
    pub valid_count: u64,
    pub attempt_count: u64,
    pub throughput_valid_per_sec: f64,
    pub throughput_attempts_per_sec: f64,
    pub elapsed_secs: f64,
    pub params: GeneratorParams,
    pub snapshots: Vec<ThroughputSnapshot>,
}

/// Summary across multiple throughput repetitions.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ThroughputSummary {
    pub generator: String,
    pub target: String,
    pub reps: u32,
    pub duration_secs: u64,
    pub mean_valid_count: f64,
    pub stddev_valid_count: f64,
    pub mean_throughput_valid_per_sec: f64,
    pub stddev_throughput_valid_per_sec: f64,
    pub median_time_series: Vec<ThroughputSnapshot>,
    pub results: Vec<ThroughputResult>,
}

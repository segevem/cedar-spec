use std::collections::HashSet;
use std::fs;
use std::io::BufRead;
use std::path::Path;

use crate::kpath;

use serde::{Deserialize, Serialize};

/// Per-input metadata stored during the collection phase.
#[derive(Debug, Deserialize)]
pub struct InputMetadata {
    pub idx: u64,
    pub seed: u64,
    pub node_count: usize,
    pub kpath2_count: usize,
    pub kpath3_count: usize,
}

/// Result of the analysis phase for a single repetition.
#[derive(Debug, Serialize)]
pub struct AnalyzeResult {
    pub corpus_size: usize,
    pub unique_inputs: usize,
    pub unique_skeletons: usize,
    pub total_nodes: u64,
    pub mean_node_count: f64,
    pub median_node_count: usize,
    pub cumulative_2paths: usize,
    pub cumulative_3paths: usize,
    pub kpath2_frequency: Vec<(String, u64)>,
    pub kpath3_frequency: Vec<(String, u64)>,
    pub diversity_over_time: Vec<DiversitySnapshot>,
    pub source_coverage_pct: Option<f64>,
    pub coverage_snapshots: Vec<CoverageBatch>,
}

/// Coverage at a batch boundary.
#[derive(Debug, Clone, Serialize)]
pub struct CoverageBatch {
    pub corpus_idx: usize,
    pub counters_hit: usize,
    pub counters_total: usize,
    pub coverage_pct: f64,
}

/// A point in the diversity-over-time series.
#[derive(Debug, Clone, Serialize)]
pub struct DiversitySnapshot {
    pub input_idx: usize,
    pub unique_inputs: usize,
    pub unique_skeletons: usize,
    pub cumulative_2paths: usize,
    pub cumulative_3paths: usize,
}

// TODO: replay_corpus_with_coverage requires a `decode_raw` method on
// ValidationGenerator and a profraw-instrumented build. Implement when
// the decode path is available on the trait.

/// Compute metrics from the per_input.jsonl file without source coverage.
/// Used when not built with profraw support, or as a supplement.
pub fn compute_metrics_from_jsonl(corpus_dir: &Path) -> MetricsFromJsonl {
    let metadata_path = corpus_dir
        .parent()
        .unwrap_or(corpus_dir)
        .join("per_input.jsonl");

    let mut node_counts: Vec<usize> = Vec::new();
    let mut total_nodes: u64 = 0;
    let mut unique_fingerprints: HashSet<(usize, usize, usize)> = HashSet::new();
    let mut cumulative_2paths: usize = 0;
    let mut cumulative_3paths: usize = 0;
    let mut count: usize = 0;

    if let Ok(file) = fs::File::open(&metadata_path) {
        let reader = std::io::BufReader::new(file);
        for line in reader.lines().flatten() {
            if let Ok(meta) = serde_json::from_str::<InputMetadata>(&line) {
                node_counts.push(meta.node_count);
                total_nodes += meta.node_count as u64;
                unique_fingerprints.insert((meta.node_count, meta.kpath2_count, meta.kpath3_count));
                cumulative_2paths = cumulative_2paths.max(meta.kpath2_count);
                cumulative_3paths = cumulative_3paths.max(meta.kpath3_count);
                count += 1;
            }
        }
    }

    node_counts.sort();
    let n = node_counts.len();
    let mean = if n > 0 {
        total_nodes as f64 / n as f64
    } else {
        0.0
    };
    let median = if n > 0 { node_counts[n / 2] } else { 0 };

    MetricsFromJsonl {
        unique_inputs: unique_fingerprints.len(),
        total_nodes,
        mean_node_count: mean,
        median_node_count: median,
        cumulative_2paths,
        cumulative_3paths,
    }
}

pub struct MetricsFromJsonl {
    pub unique_inputs: usize,
    pub total_nodes: u64,
    pub mean_node_count: f64,
    pub median_node_count: usize,
    pub cumulative_2paths: usize,
    pub cumulative_3paths: usize,
}

/// Analyze a completed collection rep's output directory.
/// Reads per_input.jsonl for metrics. Does NOT require profraw build.
pub fn analyze_collection_dir(rep_dir: &Path) -> AnalyzeResult {
    let corpus_dir = rep_dir.join("corpus");
    let corpus_size = fs::read_dir(&corpus_dir)
        .map(|rd| rd.filter_map(|e| e.ok()).count())
        .unwrap_or(0);

    let metrics = compute_metrics_from_jsonl(&corpus_dir);

    AnalyzeResult {
        corpus_size,
        unique_inputs: metrics.unique_inputs,
        unique_skeletons: metrics.unique_inputs, // jsonl path doesn't have skeleton info
        total_nodes: metrics.total_nodes,
        mean_node_count: metrics.mean_node_count,
        median_node_count: metrics.median_node_count,
        cumulative_2paths: metrics.cumulative_2paths,
        cumulative_3paths: metrics.cumulative_3paths,
        kpath2_frequency: Vec::new(),
        kpath3_frequency: Vec::new(),
        diversity_over_time: Vec::new(),
        source_coverage_pct: None,
        coverage_snapshots: Vec::new(),
    }
}

/// Corpus entries are stored as `[schema_len:u32-le ‖ schema-proto ‖ policies-proto]`
/// (see `collect.rs`). Extract the `PolicySet` for structural (re)analysis.
fn decode_corpus_policies(buf: &[u8]) -> Option<cedar_policy::PolicySet> {
    use cedar_policy::PolicySet;
    use cedar_policy::proto::traits::Protobuf;
    if buf.len() < 4 { return None; }
    let schema_len = u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]) as usize;
    if buf.len() < 4 + schema_len { return None; }
    PolicySet::decode(&buf[4 + schema_len..]).ok()
}

/// Decode one corpus buffer into a `PolicySet` per `format`: "proto" = the framed
/// `[schema_len‖schema‖policies]` entry; anything else = raw `Unstructured` bytes replayed
/// through the ABAC generator.
fn decode_input(buf: &[u8], format: &str) -> Option<cedar_policy::PolicySet> {
    match format {
        "proto" => decode_corpus_policies(buf),
        _ => {
            use arbitrary::{Arbitrary, Unstructured};
            use cedar_policy::Schema;
            use cedar_policy_generators::{schema, schema_gen::SchemaGen};
            let settings = cedar_policy_generators::settings::ABACSettings::type_directed();
            let mut u = Unstructured::new(buf);
            let gen_schema = schema::Schema::arbitrary(settings, &mut u).ok()?;
            let hierarchy = gen_schema.arbitrary_hierarchy(&mut u).ok()?;
            let policy = gen_schema.arbitrary_policy(&hierarchy, &mut u).ok()?;
            let _schema = Schema::try_from(gen_schema).ok()?;
            Some(policy.into_policy_set())
        }
    }
}

/// Split an S3 batch object (`[u32-le len ‖ payload]` repeated) into its per-input entries.
fn split_batch(data: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut pos = 0;
    while pos + 4 <= data.len() {
        let len = u32::from_le_bytes([data[pos], data[pos + 1], data[pos + 2], data[pos + 3]]) as usize;
        pos += 4;
        if pos + len > data.len() { break; }
        out.push(data[pos..pos + len].to_vec());
        pos += len;
    }
    out
}

/// Per-thread analysis accumulator for the parallel (rayon) fold/reduce.
///
/// CONSTANT-MEMORY distinct-counters (`Hll`) and node distribution (`NodeHistogram`) — NOT
/// `HashSet<u64>`/`Vec<usize>`, which grow O(N) and blow memory at millions of inputs (the
/// whole reason `hll` exists). The k-path sets/freqs ARE bounded (distinct k-paths saturate
/// per the grammar), so exact sets are fine there.
struct Partial {
    hist: crate::hll::NodeHistogram,
    total_nodes: u64,
    uniq: crate::hll::Hll,
    uniq_skel: crate::hll::Hll,
    all_2paths: HashSet<kpath::KPath>,
    all_3paths: HashSet<kpath::KPath>,
    kpath2_freq: std::collections::HashMap<kpath::KPath, u64>,
    kpath3_freq: std::collections::HashMap<kpath::KPath, u64>,
    replayed: u64,
}
impl Partial {
    fn new() -> Self {
        Partial {
            hist: crate::hll::NodeHistogram::default(),
            total_nodes: 0,
            uniq: crate::hll::Hll::new(21),       // ~0.07% error, 2MB regs
            uniq_skel: crate::hll::Hll::new(21),
            all_2paths: HashSet::new(),
            all_3paths: HashSet::new(),
            kpath2_freq: std::collections::HashMap::new(),
            kpath3_freq: std::collections::HashMap::new(),
            replayed: 0,
        }
    }
    fn add(&mut self, policies: &cedar_policy::PolicySet) {
        let stats3 = kpath::analyze_policy_set(policies, 3);
        let stats2 = kpath::analyze_policy_set(policies, 2);
        self.hist.add(stats3.node_count);
        self.total_nodes += stats3.node_count as u64;
        self.uniq.add(kpath::hash_policy_set(policies));
        self.uniq_skel.add(kpath::hash_policy_set_skeleton(policies));
        for p in &stats2.kpaths { *self.kpath2_freq.entry(p.clone()).or_insert(0) += 1; }
        for p in &stats3.kpaths { *self.kpath3_freq.entry(p.clone()).or_insert(0) += 1; }
        self.all_2paths.extend(stats2.kpaths.iter().cloned());
        self.all_3paths.extend(stats3.kpaths.iter().cloned());
        self.replayed += 1;
    }
    fn merge(mut self, o: Partial) -> Partial {
        self.hist.merge(&o.hist);
        self.total_nodes += o.total_nodes;
        self.uniq.merge(&o.uniq);
        self.uniq_skel.merge(&o.uniq_skel);
        self.all_2paths.extend(o.all_2paths);
        self.all_3paths.extend(o.all_3paths);
        for (k, v) in o.kpath2_freq { *self.kpath2_freq.entry(k).or_insert(0) += v; }
        for (k, v) in o.kpath3_freq { *self.kpath3_freq.entry(k).or_insert(0) += v; }
        self.replayed += o.replayed;
        self
    }
}

fn empty_analyze_result(corpus_size: usize) -> AnalyzeResult {
    AnalyzeResult {
        corpus_size, unique_inputs: 0, unique_skeletons: 0, total_nodes: 0,
        mean_node_count: 0.0, median_node_count: 0, cumulative_2paths: 0, cumulative_3paths: 0,
        kpath2_frequency: Vec::new(), kpath3_frequency: Vec::new(),
        diversity_over_time: Vec::new(), source_coverage_pct: None, coverage_snapshots: Vec::new(),
    }
}

/// Number of contiguous corpus chunks the parallel analyze splits into. Each chunk is
/// analyzed independently on its own core (so this bounds parallelism), and each chunk
/// boundary becomes one `diversity_over_time` snapshot (so this is also the curve
/// resolution). Overridable via `ANALYZE_CHUNKS`. 128 → 128-way parallelism + a 128-point
/// smooth curve; peak memory is `CHUNKS * (2 HLLs @ p=21 = 4 MB)` ≈ 512 MB (bounded by
/// CHUNKS, NOT by N — the k-path sets saturate per the grammar).
fn analyze_chunk_count() -> usize {
    std::env::var("ANALYZE_CHUNKS")
        .ok()
        .and_then(|s| s.parse().ok())
        .filter(|&c: &usize| c > 0)
        .unwrap_or(128)
}

/// PARALLEL analysis of a whole corpus: rayon over contiguous, index-numbered chunks on all
/// cores. This is the heavy k-path/diversity work moved OFF the collect critical path —
/// collect just streams the corpus (COLLECT_STREAM_ONLY), and this recomputes every metric
/// with maniac parallelism (each input is independent).
///
/// DIVERSITY OVER TIME via NUMBERED OUTPUTS: `buffers` is already in collection order, so its
/// index IS the stream position. We split into contiguous chunks, analyze each in parallel
/// into a `Partial` (mergeable HLLs + bounded k-path sets), then cumulative-merge the chunks
/// IN ORDER. Because merge is associative and each chunk covers a known prefix range, the
/// cumulative state after chunk `c` is EXACTLY the prefix `[0 .. end_of_chunk_c]` — so we emit
/// a `DiversitySnapshot` (unique / skeletons / 2-paths / 3-paths) at each chunk boundary,
/// keyed by that stream position (which plot_over_time maps to wall-clock via valid_count).
/// The final fully-merged `Partial` gives the final metrics — same numbers as a plain fold.
fn analyze_buffers_parallel(buffers: Vec<Vec<u8>>, format: &str) -> AnalyzeResult {
    use rayon::prelude::*;
    let corpus_size = buffers.len();
    if corpus_size == 0 {
        return empty_analyze_result(0);
    }

    let n_chunks = analyze_chunk_count().min(corpus_size).max(1);
    let chunk_size = corpus_size.div_ceil(n_chunks);

    // Parallel: one Partial per contiguous chunk, tagged with its chunk index (for ordering)
    // and the global stream position at its end (for the snapshot x-axis).
    let mut chunk_partials: Vec<(usize, usize, Partial)> = buffers
        .par_chunks(chunk_size)
        .enumerate()
        .map(|(ci, chunk)| {
            let mut p = Partial::new();
            for buf in chunk {
                if let Some(ps) = decode_input(buf, format) {
                    if !ps.is_empty() {
                        p.add(&ps);
                    }
                }
            }
            let end = ((ci + 1) * chunk_size).min(corpus_size);
            (ci, end, p)
        })
        .collect();
    chunk_partials.sort_by_key(|&(ci, _, _)| ci);

    // Cumulative-merge in stream order, snapshotting the prefix diversity at each boundary.
    let mut diversity_over_time: Vec<DiversitySnapshot> = Vec::with_capacity(chunk_partials.len());
    let mut m = Partial::new();
    for (_, end, part) in chunk_partials {
        m = m.merge(part);
        diversity_over_time.push(DiversitySnapshot {
            input_idx: end,
            unique_inputs: m.uniq.estimate() as usize,
            unique_skeletons: m.uniq_skel.estimate() as usize,
            cumulative_2paths: m.all_2paths.len(),
            cumulative_3paths: m.all_3paths.len(),
        });
    }

    let mut k2: Vec<(String, u64)> = m.kpath2_freq.into_iter().map(|(k, v)| (k.0.join("\u{2192}"), v)).collect();
    k2.sort_by(|a, b| b.1.cmp(&a.1));
    let mut k3: Vec<(String, u64)> = m.kpath3_freq.into_iter().map(|(k, v)| (k.0.join("\u{2192}"), v)).collect();
    k3.sort_by(|a, b| b.1.cmp(&a.1));

    AnalyzeResult {
        corpus_size,
        unique_inputs: m.uniq.estimate() as usize,
        unique_skeletons: m.uniq_skel.estimate() as usize,
        total_nodes: m.total_nodes,
        mean_node_count: m.hist.mean(),
        median_node_count: m.hist.median(),
        cumulative_2paths: m.all_2paths.len(),
        cumulative_3paths: m.all_3paths.len(),
        kpath2_frequency: k2,
        kpath3_frequency: k3,
        diversity_over_time,
        source_coverage_pct: None,
        coverage_snapshots: Vec::new(),
    }
}

/// Replay a corpus of raw fuzz buffers (format=fuzz) or protobuf PolicySets (format=proto),
/// compute per-input metrics, write per_input.jsonl, and return AnalyzeResult.
pub fn replay_and_analyze(rep_dir: &Path, format: &str) -> AnalyzeResult {
    let corpus_dir = rep_dir.join("corpus");
    let mut corpus_files: Vec<std::path::PathBuf> = fs::read_dir(&corpus_dir)
        .map(|rd| rd.filter_map(|e| e.ok()).map(|e| e.path()).filter(|p| p.is_file()).collect())
        .unwrap_or_default();
    corpus_files.sort();
    // Read every input into memory (small framed buffers), splitting S3-style batch files
    // into their entries, then analyze in parallel (rayon).
    let mut buffers: Vec<Vec<u8>> = Vec::new();
    for path in &corpus_files {
        let data = match fs::read(path) { Ok(d) => d, Err(_) => continue };
        let is_batch = path.file_name().and_then(|n| n.to_str())
            .map(|n| n.starts_with("batch_")).unwrap_or(false);
        if is_batch {
            buffers.extend(split_batch(&data));
        } else {
            buffers.push(data);
        }
    }
    analyze_buffers_parallel(buffers, format)
}

#[cfg(feature = "s3")]
pub async fn replay_and_analyze_from_s3(
    client: &aws_sdk_s3::Client,
    bucket: &str,
    prefix: &str,
    format: &str,
) -> AnalyzeResult {
    use crate::experiment::s3;
    // Collect all per-input buffers from S3 (stream_batches yields one owned Vec per input),
    // then analyze in parallel (rayon) — same core as the local path.
    let mut buffers: Vec<Vec<u8>> = Vec::new();
    s3::stream_batches(client, bucket, prefix, |buf| {
        buffers.push(buf);
    })
    .await
    .ok();
    analyze_buffers_parallel(buffers, format)
}

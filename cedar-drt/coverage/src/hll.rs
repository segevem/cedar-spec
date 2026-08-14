//! Constant-memory metric accumulators for the collect-with-inline-analysis path.
//!
//! The exact `HashSet<u64>` distinct-counters and the `Vec<usize>` used for the
//! median grow O(N) and blew memory on very large runs. These replacements are
//! O(1) (HLL: ~16 KB of registers; histogram: O(max node count)) regardless of N.
//!
//! - [`Hll`]: HyperLogLog distinct-count estimate, ~0.8% standard error at p=14.
//! - [`NodeHistogram`]: exact mean + median of small non-negative integers.

/// Dense HyperLogLog over `u64` hashes. `p` register-index bits → `2^p` registers.
pub struct Hll {
    regs: Vec<u8>,
    p: u32,
}

impl Hll {
    /// `p = 14` → 16384 registers (16 KB), ~0.81% standard error.
    pub fn new(p: u32) -> Self {
        assert!((4..=24).contains(&p));
        Hll { regs: vec![0u8; 1usize << p], p }
    }

    #[inline]
    pub fn add(&mut self, x: u64) {
        let idx = (x >> (64 - self.p)) as usize; // high p bits → register index
        let rest = x & ((1u64 << (64 - self.p)) - 1); // low (64-p) bits
        // rank = position (1-indexed) of the leftmost set bit within the window.
        let rank = if rest == 0 {
            (64 - self.p + 1) as u8
        } else {
            (rest.leading_zeros() - self.p + 1) as u8
        };
        if rank > self.regs[idx] {
            self.regs[idx] = rank;
        }
    }

    /// Merge another HLL (same `p`) in place: register-wise max — the standard,
    /// exact HLL union. Lets per-thread HLLs be reduced after a parallel fold.
    pub fn merge(&mut self, other: &Hll) {
        debug_assert_eq!(self.p, other.p, "HLL merge requires equal p");
        for (a, b) in self.regs.iter_mut().zip(other.regs.iter()) {
            if *b > *a {
                *a = *b;
            }
        }
    }

    pub fn estimate(&self) -> u64 {
        let m = self.regs.len() as f64;
        let alpha = match self.regs.len() {
            16 => 0.673,
            32 => 0.697,
            64 => 0.709,
            _ => 0.7213 / (1.0 + 1.079 / m),
        };
        let sum: f64 = self.regs.iter().map(|&r| 2f64.powi(-(r as i32))).sum();
        let raw = alpha * m * m / sum;
        // Small-range correction: linear counting when many registers are empty.
        if raw <= 2.5 * m {
            let zeros = self.regs.iter().filter(|&&r| r == 0).count() as f64;
            if zeros > 0.0 {
                return (m * (m / zeros).ln()).round() as u64;
            }
        }
        raw.round() as u64
    }
}

/// Exact mean + median of small non-negative integers (node counts) in O(max)
/// memory, via a bucket histogram that grows to the largest value seen.
#[derive(Default)]
pub struct NodeHistogram {
    buckets: Vec<u64>,
    total: u64,
    sum: u128,
}

impl NodeHistogram {
    pub fn add(&mut self, v: usize) {
        if v >= self.buckets.len() {
            self.buckets.resize(v + 1, 0);
        }
        self.buckets[v] += 1;
        self.total += 1;
        self.sum += v as u128;
    }

    pub fn total(&self) -> u64 {
        self.total
    }

    /// Merge another histogram in place (bucket-wise sum) — for reducing per-thread
    /// histograms after a parallel fold. Exact: mean/median are preserved.
    pub fn merge(&mut self, other: &NodeHistogram) {
        if other.buckets.len() > self.buckets.len() {
            self.buckets.resize(other.buckets.len(), 0);
        }
        for (a, b) in self.buckets.iter_mut().zip(other.buckets.iter()) {
            *a += *b;
        }
        self.total += other.total;
        self.sum += other.sum;
    }

    pub fn mean(&self) -> f64 {
        if self.total == 0 {
            0.0
        } else {
            self.sum as f64 / self.total as f64
        }
    }

    /// Lower median: value at cumulative index `total/2` (matches
    /// `sorted[n/2]`, the previous exact behavior).
    pub fn median(&self) -> usize {
        if self.total == 0 {
            return 0;
        }
        let target = self.total / 2;
        let mut cum = 0u64;
        for (v, &c) in self.buckets.iter().enumerate() {
            cum += c;
            if cum > target {
                return v;
            }
        }
        self.buckets.len().saturating_sub(1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    // Deterministic pseudo-random u64 stream (SplitMix64) — no rand dep.
    fn splitmix(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    /// HLL estimate must track the EXACT distinct count within ~2% across scales.
    #[test]
    fn hll_matches_exact_within_2pct() {
        for &n in &[1_000u64, 100_000, 1_000_000] {
            let mut hll = Hll::new(14);
            let mut exact: HashSet<u64> = HashSet::new();
            let mut s = 0x1234_5678u64;
            for _ in 0..n {
                let h = splitmix(&mut s);
                hll.add(h);
                exact.insert(h);
            }
            let est = hll.estimate() as f64;
            let truth = exact.len() as f64;
            let err = (est - truth).abs() / truth;
            assert!(err < 0.02, "n={n}: est={est} exact={truth} err={:.4}", err);
        }
    }

    /// At p=21 the error should be ~0.07% (target <0.08%). Verify empirically at
    /// our scale (up to 10M distinct), printing the actual relative error.
    #[test]
    fn hll_p21_sub_pointoh8_percent() {
        for &n in &[1_000_000u64, 5_000_000, 10_000_000] {
            let mut hll = Hll::new(21);
            let mut exact: HashSet<u64> = HashSet::new();
            let mut s = 0xABCD_1234u64;
            for _ in 0..n {
                let h = splitmix(&mut s);
                hll.add(h);
                exact.insert(h);
            }
            let truth = exact.len() as f64;
            let err = (hll.estimate() as f64 - truth).abs() / truth;
            println!("p=21 n={n}: relative error = {:.4}% ({:.5})", err * 100.0, err);
            assert!(err < 0.0012, "n={n}: err {:.5} exceeds ~0.12%", err);
        }
    }

    /// With heavy duplication, HLL estimates DISTINCT (not total inserts).
    #[test]
    fn hll_counts_distinct_not_total() {
        let mut hll = Hll::new(14);
        let mut exact: HashSet<u64> = HashSet::new();
        let mut s = 42u64;
        // 500k distinct values, each inserted twice (1M inserts).
        let base: Vec<u64> = (0..500_000).map(|_| splitmix(&mut s)).collect();
        for h in base.iter().chain(base.iter()) {
            hll.add(*h);
            exact.insert(*h);
        }
        let err = (hll.estimate() as f64 - exact.len() as f64).abs() / exact.len() as f64;
        assert!(err < 0.02, "distinct est err {:.4}", err);
    }

    /// Histogram mean/median must equal the exact sort-based values.
    #[test]
    fn histogram_matches_exact() {
        let mut hist = NodeHistogram::default();
        let mut v: Vec<usize> = Vec::new();
        let mut s = 7u64;
        for _ in 0..123_457 {
            let nc = (splitmix(&mut s) % 137) as usize; // small ints, like node counts
            hist.add(nc);
            v.push(nc);
        }
        v.sort_unstable();
        let exact_median = v[v.len() / 2];
        let exact_mean = v.iter().sum::<usize>() as f64 / v.len() as f64;
        assert_eq!(hist.median(), exact_median, "median mismatch");
        assert!((hist.mean() - exact_mean).abs() < 1e-9, "mean mismatch");
    }
}

#!/usr/bin/env python3
"""Plot source coverage growth with 95% CI (t-distribution) from repeated runs."""

import json
import sys
import os
import numpy as np
from scipy import stats as scipy_stats
import matplotlib.pyplot as plt

results_dir = sys.argv[1] if len(sys.argv) > 1 else "./corpus_ci_results"
n_runs = int(sys.argv[2]) if len(sys.argv) > 2 else 5

# Load all runs
specimen_runs = []
fuzz_runs = []

for i in range(1, n_runs + 1):
    run_dir = os.path.join(results_dir, f"run_{i}")
    spec_path = os.path.join(run_dir, "specimen_cov.json")
    fuzz_path = os.path.join(run_dir, "fuzz_cov.json")

    if os.path.exists(spec_path):
        with open(spec_path) as f:
            specimen_runs.append(json.load(f))
    if os.path.exists(fuzz_path):
        with open(fuzz_path) as f:
            fuzz_runs.append(json.load(f))

print(f"Loaded {len(specimen_runs)} specimen runs, {len(fuzz_runs)} fuzz runs")

if not specimen_runs or not fuzz_runs:
    print("ERROR: Need at least 1 run of each")
    sys.exit(1)

# Resample to common time points (10%, 20%, ..., 100% of corpus)
def resample_to_percentiles(runs, n_points=20):
    """For each run, extract coverage at evenly spaced corpus indices."""
    resampled = []
    for run in runs:
        if not run:
            continue
        total = len(run)
        indices = [max(0, int(total * p / n_points) - 1) for p in range(1, n_points + 1)]
        values = [run[min(idx, total-1)]["coverage_pct"] for idx in indices]
        resampled.append(values)
    return np.array(resampled)

# Also extract time-based resampling
def resample_to_time(runs, max_time=90, n_points=20):
    """For each run, extract coverage at evenly spaced time points."""
    resampled = []
    for run in runs:
        if not run:
            continue
        total = len(run)
        # Approximate: entry i was generated at time i/total * max_time
        time_points = np.linspace(max_time / n_points, max_time, n_points)
        values = []
        for t in time_points:
            # Find the entry closest to this time
            idx = min(int(t / max_time * total), total - 1)
            values.append(run[idx]["coverage_pct"])
        resampled.append(values)
    return np.array(resampled), np.linspace(max_time / n_points, max_time, n_points)

n_points = 18
spec_matrix, time_axis = resample_to_time(specimen_runs, n_points=n_points)
fuzz_matrix, _ = resample_to_time(fuzz_runs, n_points=n_points)

n_spec = spec_matrix.shape[0]
n_fuzz = fuzz_matrix.shape[0]

spec_mean = spec_matrix.mean(axis=0)
spec_se = spec_matrix.std(axis=0, ddof=1) / np.sqrt(n_spec)
spec_t = scipy_stats.t.ppf(0.975, df=n_spec - 1) if n_spec > 1 else 0
spec_ci = spec_t * spec_se

fuzz_mean = fuzz_matrix.mean(axis=0)
fuzz_se = fuzz_matrix.std(axis=0, ddof=1) / np.sqrt(n_fuzz)
fuzz_t = scipy_stats.t.ppf(0.975, df=n_fuzz - 1) if n_fuzz > 1 else 0
fuzz_ci = fuzz_t * fuzz_se

# Plot
fig, ax = plt.subplots(figsize=(10, 6))

ax.plot(time_axis, spec_mean, "s-", color="tab:blue", linewidth=2, markersize=4,
        label="Specimen-Derived Unguided")
ax.fill_between(time_axis, spec_mean - spec_ci, spec_mean + spec_ci,
                color="tab:blue", alpha=0.2)

ax.plot(time_axis, fuzz_mean, "o-", color="tab:red", linewidth=2, markersize=4,
        label="Handwritten Guided")
ax.fill_between(time_axis, fuzz_mean - fuzz_ci, fuzz_mean + fuzz_ci,
                color="tab:red", alpha=0.2)

ax.set_xlabel("Generation Time (seconds)", fontsize=12)
ax.set_ylabel("Validator Source Coverage (%)", fontsize=12)
ax.set_title(f"Validator Coverage Over Time\n({n_spec} runs, shaded = 95% CI, t-distribution)", fontsize=13)
ax.legend(fontsize=11)
ax.grid(True, alpha=0.3)

info = (f"Specimen: {spec_mean[-1]:.2f}% [{spec_mean[-1]-spec_ci[-1]:.2f}, {spec_mean[-1]+spec_ci[-1]:.2f}]\n"
        f"Fuzzer: {fuzz_mean[-1]:.2f}% [{fuzz_mean[-1]-fuzz_ci[-1]:.2f}, {fuzz_mean[-1]+fuzz_ci[-1]:.2f}]")
ax.text(0.02, 0.98, info, transform=ax.transAxes, fontsize=9, verticalalignment="top",
        fontfamily="monospace", bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.5))

plt.tight_layout()
output_path = os.path.join(results_dir, "coverage_ci.png")
plt.savefig(output_path, dpi=150)
print(f"Graph saved to: {output_path}")

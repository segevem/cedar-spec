#!/usr/bin/env python3
"""Plot typechecker coverage with confidence intervals from repeated runs."""

import json
import sys
import os
import numpy as np
import matplotlib.pyplot as plt

results_dir = sys.argv[1] if len(sys.argv) > 1 else "./repeated_results"
output_path = sys.argv[2] if len(sys.argv) > 2 else os.path.join(results_dir, "ci_comparison.png")

# Collect data from all runs
fuzzer_runs = []
gen_runs = []
gen_name = None

for run_dir in sorted(os.listdir(results_dir)):
    run_path = os.path.join(results_dir, run_dir)
    if not os.path.isdir(run_path):
        continue

    fuzzer_path = os.path.join(run_path, "fuzzer", "coverage_over_time.json")
    if os.path.exists(fuzzer_path):
        with open(fuzzer_path) as f:
            fuzzer_runs.append(json.load(f))

    for name in os.listdir(run_path):
        if name != "fuzzer":
            gen_path = os.path.join(run_path, name, "coverage_over_time.json")
            if os.path.exists(gen_path):
                with open(gen_path) as f:
                    gen_runs.append(json.load(f))
                gen_name = name

if not fuzzer_runs or not gen_runs:
    print(f"ERROR: Need at least 1 run. Found {len(fuzzer_runs)} fuzzer, {len(gen_runs)} generator runs.")
    sys.exit(1)

print(f"Found {len(fuzzer_runs)} fuzzer runs, {len(gen_runs)} generator runs")

# Extract time series (assume all runs have same time points)
n_points = min(len(r) for r in fuzzer_runs)
fuzz_times = [fuzzer_runs[0][i]["elapsed_secs"] for i in range(n_points)]

fuzz_tc_matrix = np.array([[r[i]["typechecker_pct"] for i in range(n_points)] for r in fuzzer_runs])
gen_tc_matrix = np.array([[r[i]["typechecker_pct"] for i in range(min(len(r) for r in gen_runs))] for r in gen_runs])
gen_n_points = gen_tc_matrix.shape[1]
gen_times = [gen_runs[0][i]["elapsed_secs"] for i in range(gen_n_points)]

# Compute mean and 95% CI using t-distribution (proper for small n)
from scipy import stats as scipy_stats

n_fuzz = fuzz_tc_matrix.shape[0]
n_gen = gen_tc_matrix.shape[0]

fuzz_mean = fuzz_tc_matrix.mean(axis=0)
fuzz_se = fuzz_tc_matrix.std(axis=0, ddof=1) / np.sqrt(n_fuzz)
fuzz_t = scipy_stats.t.ppf(0.975, df=n_fuzz - 1)
fuzz_ci = fuzz_t * fuzz_se

gen_mean = gen_tc_matrix.mean(axis=0)
gen_se = gen_tc_matrix.std(axis=0, ddof=1) / np.sqrt(n_gen)
gen_t = scipy_stats.t.ppf(0.975, df=n_gen - 1)
gen_ci = gen_t * gen_se

# Plot
fig, ax = plt.subplots(figsize=(10, 6))

ax.plot(fuzz_times, fuzz_mean, "o-", color="tab:red", linewidth=2, markersize=4, label="Handwritten Guided")
ax.fill_between(fuzz_times, fuzz_mean - fuzz_ci, fuzz_mean + fuzz_ci, color="tab:red", alpha=0.2)

ax.plot(gen_times, gen_mean, "s-", color="tab:blue", linewidth=2, markersize=4, label="Specimen-Derived Unguided")
ax.fill_between(gen_times, gen_mean - gen_ci, gen_mean + gen_ci, color="tab:blue", alpha=0.2)

ax.set_xlabel("Elapsed Time (seconds)", fontsize=12)
ax.set_ylabel("Typechecker Coverage (%)", fontsize=12)
ax.set_title(f"Typechecker Source Coverage Over Time\n({n_fuzz} runs, shaded = 95% CI, t-distribution)", fontsize=14)
ax.legend(fontsize=11)
ax.grid(True, alpha=0.3)
ax.set_ylim(0, 100)

# Add final stats
info_text = (
    f"Handwritten Guided: {fuzz_mean[-1]:.1f}% [{fuzz_mean[-1]-fuzz_ci[-1]:.1f}, {fuzz_mean[-1]+fuzz_ci[-1]:.1f}]\n"
    f"Specimen-Derived Unguided: {gen_mean[-1]:.1f}% [{gen_mean[-1]-gen_ci[-1]:.1f}, {gen_mean[-1]+gen_ci[-1]:.1f}]"
)
ax.text(0.02, 0.98, info_text, transform=ax.transAxes, fontsize=9,
        verticalalignment="top", fontfamily="monospace",
        bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.5))

plt.tight_layout()
plt.savefig(output_path, dpi=150)
print(f"Graph saved to: {output_path}")

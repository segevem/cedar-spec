#!/usr/bin/env python3
"""Plot typechecker coverage over time for fuzzer vs generator."""

import json
import sys
import os

import matplotlib.pyplot as plt

output_dir = sys.argv[1] if len(sys.argv) > 1 else "./coverage_results"

fuzzer_path = os.path.join(output_dir, "fuzzer", "coverage_over_time.json")
gen_path = None
for name in os.listdir(output_dir):
    if name != "fuzzer" and os.path.isfile(os.path.join(output_dir, name, "coverage_over_time.json")):
        gen_path = os.path.join(output_dir, name, "coverage_over_time.json")
        gen_name = name
        break

if not gen_path:
    print("ERROR: Could not find generator results")
    sys.exit(1)

with open(fuzzer_path) as f:
    fuzzer_data = json.load(f)
with open(gen_path) as f:
    gen_data = json.load(f)

fig, ax = plt.subplots(figsize=(10, 6))

# Fuzzer
fuzz_times = [d["elapsed_secs"] for d in fuzzer_data]
fuzz_tc = [d["typechecker_pct"] for d in fuzzer_data]
fuzz_attempts = [d["attempts"] for d in fuzzer_data]

# Generator
gen_times = [d["elapsed_secs"] for d in gen_data]
gen_tc = [d["typechecker_pct"] for d in gen_data]
gen_attempts = [d["attempts"] for d in gen_data]

ax.plot(fuzz_times, fuzz_tc, "o-", color="tab:red", linewidth=2, markersize=4, label="Handwritten Guided")
ax.plot(gen_times, gen_tc, "s-", color="tab:blue", linewidth=2, markersize=4, label="Specimen-Derived Unguided")

ax.set_xlabel("Elapsed Time (seconds)", fontsize=12)
ax.set_ylabel("Typechecker Coverage (%)", fontsize=12)
ax.set_title("Typechecker Source Coverage Over Time", fontsize=14)
ax.legend(fontsize=11)
ax.grid(True, alpha=0.3)
ax.set_ylim(0, 100)

# Add secondary info as text
final_fuzz = fuzzer_data[-1]
final_gen = gen_data[-1]
info_text = (
    f"Handwritten Guided: {final_fuzz['attempts']:,} attempts, {final_fuzz['valid_inputs']:,} valid → {final_fuzz['typechecker_pct']}%\n"
    f"Specimen-Derived Unguided: {final_gen['attempts']:,} attempts, {final_gen['valid_inputs']:,} valid → {final_gen['typechecker_pct']}%"
)
ax.text(0.02, 0.98, info_text, transform=ax.transAxes, fontsize=9,
        verticalalignment="top", fontfamily="monospace",
        bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.5))

plt.tight_layout()
out_path = os.path.join(output_dir, "comparison_graph.png")
plt.savefig(out_path, dpi=150)
print(f"Graph saved to: {out_path}")

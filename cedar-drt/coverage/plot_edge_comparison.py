#!/usr/bin/env python3
"""Plot edge tracking comparison: novel inputs + features over time."""

import json
import sys
import os

import matplotlib.pyplot as plt

if len(sys.argv) < 3:
    print("Usage: plot_edge_comparison.py <file1.json> <file2.json> [output.png]")
    print("  Each JSON file is an array of {elapsed_secs, novel_inputs, total_features, ...}")
    sys.exit(1)

files = sys.argv[1:-1] if len(sys.argv) > 3 else sys.argv[1:]
output_path = sys.argv[-1] if len(sys.argv) > 3 else "edge_comparison.png"

datasets = []
for f in files:
    with open(f) as fh:
        data = json.load(fh)
    name = os.path.splitext(os.path.basename(f))[0]
    datasets.append((name, data))

fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8), sharex=True)

colors = ["tab:blue", "tab:red", "tab:green", "tab:orange"]

for i, (name, data) in enumerate(datasets):
    times = [d["elapsed_secs"] for d in data]
    novel = [d["novel_inputs"] for d in data]
    features = [d["total_features"] for d in data]
    color = colors[i % len(colors)]

    ax1.plot(times, novel, "o-", color=color, linewidth=2, markersize=4, label=name)
    ax2.plot(times, features, "s-", color=color, linewidth=2, markersize=4, label=name)

ax1.set_ylabel("Novel Inputs (corpus equivalent)", fontsize=11)
ax1.set_title("Edge Coverage Tracking Over Time", fontsize=13)
ax1.legend(fontsize=10)
ax1.grid(True, alpha=0.3)

ax2.set_xlabel("Elapsed Time (seconds)", fontsize=11)
ax2.set_ylabel("Total Edge Features Discovered", fontsize=11)
ax2.legend(fontsize=10)
ax2.grid(True, alpha=0.3)

# Add final stats as annotation
for i, (name, data) in enumerate(datasets):
    final = data[-1]
    ax1.annotate(f"{final['novel_inputs']}",
                 xy=(final['elapsed_secs'], final['novel_inputs']),
                 fontsize=9, color=colors[i % len(colors)])
    ax2.annotate(f"{final['total_features']}",
                 xy=(final['elapsed_secs'], final['total_features']),
                 fontsize=9, color=colors[i % len(colors)])

plt.tight_layout()
plt.savefig(output_path, dpi=150)
print(f"Graph saved to: {output_path}")

#!/usr/bin/env python3
"""Plot median + bootstrap 95% CI per approach, for the key metrics.

Reads <root>/bootstrap_ci.json (written by bootstrap_ci.py) and draws one
subplot per metric: a point at the median with asymmetric error bars to the
bootstrap CI, plus the individual per-run values as faint dots so the sample
is visible. Saves <root>/bootstrap_ci.png.
"""
import argparse
import json
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

PANEL_METRICS = [
    ("cumulative_3paths", "distinct 3-paths (structural coverage)"),
    ("cumulative_2paths", "distinct 2-paths"),
    ("source_lines_covered", "validator lines covered (input-driven)"),
    ("unique_pct", "unique inputs (%)"),
    ("unique_skeletons", "unique skeletons"),
    ("mean_node_count", "mean nodes / policy"),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    with open(os.path.join(args.root, "bootstrap_ci.json")) as f:
        data = json.load(f)

    approaches = list(data["approaches"].keys())
    x = np.arange(len(approaches))
    colors = plt.cm.tab10(np.linspace(0, 1, max(len(approaches), 1)))

    fig, axs = plt.subplots(2, 3, figsize=(18, 9))
    for ax, (mk, title) in zip(axs.flat, PANEL_METRICS):
        meds, los, his = [], [], []
        for name in approaches:
            m = data["approaches"][name]["metrics"].get(mk, {})
            meds.append(m.get("median", np.nan))
            los.append(m.get("median", np.nan) - m.get("ci_lo", np.nan))
            his.append(m.get("ci_hi", np.nan) - m.get("median", np.nan))
            # faint per-run dots
            vals = m.get("values", [])
            ax.scatter([x[len(meds) - 1]] * len(vals), vals, s=14,
                       color=colors[len(meds) - 1], alpha=0.35, zorder=1)
        ax.errorbar(x, meds, yerr=[los, his], fmt="o", capsize=5, lw=1.6,
                    ms=7, color="black", ecolor="dimgray", zorder=3)
        for i in range(len(approaches)):
            ax.scatter([x[i]], [meds[i]], s=60, color=colors[i], zorder=4)
        ax.set_title(title)
        ax.set_xticks(x)
        ax.set_xticklabels(approaches, rotation=25, ha="right", fontsize=8)
        ax.grid(alpha=0.3, axis="y")

    reps = data.get("reps_requested", "?")
    fig.suptitle(f"Median + 95% bootstrap CI ({data.get('resamples','?')} resamples, "
                 f"up to {reps} runs/approach)", fontweight="bold")
    fig.tight_layout(rect=[0, 0, 1, 0.97])
    out = args.out or os.path.join(args.root, "bootstrap_ci.png")
    fig.savefig(out, dpi=130)
    print("wrote", os.path.abspath(out))


if __name__ == "__main__":
    main()

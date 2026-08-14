#!/usr/bin/env python3
"""Coverage TREEMAP: a map of the program where area = executable region-lines and color
= covered fraction (red = uncovered -> green = covered). Answers "which regions of the
program are uncovered" far better than a top-N bar chart: big red blocks are large,
poorly-exercised regions; module grouping separates in-scope validator code from
out-of-scope crate code (authorization / evaluator / parser) the validation experiment
is never expected to hit.

Reads the `coverage_map` section of <root>/coverage_compare.json (written by
coverage_analyze.py) — {which: {file: {covered, total, module}}}. Nested treemap:
modules partition the canvas by total lines, files tile within their module.

Usage: plot_coverage_treemap.py --root <dir> [--which specimen_union] [--min-file 5]
"""
import argparse
import json
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.cm as cm
import matplotlib.colors as mcolors
import matplotlib.pyplot as plt

import squarify


def layout(sizes, x, y, dx, dy):
    """Squarified rectangles for `sizes` (any order) within the box (x,y,dx,dy)."""
    norm = squarify.normalize_sizes(sizes, dx, dy)
    return squarify.squarify(norm, x, y, dx, dy)


# diff-mode category colors: who UNIQUELY reaches each region.
DIFF_CATS = [("only_spec", "#2b7bba", "specimen only"),
             ("shared", "#8c9bab", "shared"),
             ("only_hw", "#d1743c", "handwritten only"),
             ("uncovered", "#e05a4f", "uncovered")]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--mode", default="coverage", choices=["coverage", "diff"],
                    help="coverage: color=covered%% of one side; diff: color=who covers each region")
    ap.add_argument("--which", default="specimen_union",
                    help="coverage-mode key: specimen_union (default) | handwritten_union")
    ap.add_argument("--min-file", type=int, default=4,
                    help="skip files with fewer than this many total region-lines (declutter)")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    cc = os.path.join(args.root, "coverage_compare.json")
    if not os.path.isfile(cc):
        print("no coverage_compare.json"); return
    doc = json.load(open(cc))
    src = doc.get("diff_map") if args.mode == "diff" else (doc.get("coverage_map", {}).get(
        args.which) or next(iter(doc.get("coverage_map", {}).values()), None))
    if not src:
        print(f"coverage_compare.json has no {'diff_map' if args.mode=='diff' else 'coverage_map'} "
              "(re-run coverage_analyze.py)"); return
    fm = src

    # group files by module
    mods = {}
    for f, d in fm.items():
        if d["total"] < args.min_file:
            continue
        if args.mode == "diff":
            mods.setdefault(d["module"], []).append((f, d, d["total"]))
        else:
            mods.setdefault(d["module"], []).append((f, d["covered"], d["total"]))
    if not mods:
        print("nothing to plot"); return
    mod_items = sorted(mods.items(), key=lambda kv: -sum(t for _, _, t in kv[1]))
    mod_sizes = [sum(t for _, _, t in files) for _, files in mod_items]

    W, H = 100.0, 62.0
    fig, ax = plt.subplots(figsize=(17, 10.5))
    cmap = plt.cm.RdYlGn
    norm = mcolors.Normalize(0, 100)
    cat_color = {k: c for k, c, _ in DIFF_CATS}

    def rect_color(mid):
        """mid = covered count (coverage mode) or the per-file diff dict (diff mode)."""
        if args.mode == "diff":
            dom = max(DIFF_CATS, key=lambda kc: mid.get(kc[0], 0))[0]
            return cat_color[dom]
        pct = 100.0 * mid / tot if tot else 0.0
        return cmap(norm(pct))

    for (mod, files), mr in zip(mod_items, layout(mod_sizes, 0, 0, W, H)):
        files_sorted = sorted(files, key=lambda x: -x[2])
        for (fname, mid, tot), fr in zip(files_sorted,
                                         layout([t for _, _, t in files_sorted],
                                                mr["x"], mr["y"], mr["dx"], mr["dy"])):
            ax.add_patch(plt.Rectangle((fr["x"], fr["y"]), fr["dx"], fr["dy"],
                                       facecolor=rect_color(mid), edgecolor="white", linewidth=0.4))
            if fr["dx"] * fr["dy"] > W * H * 0.010:  # only label rectangles big enough to read
                ax.text(fr["x"] + fr["dx"] / 2, fr["y"] + fr["dy"] / 2,
                        os.path.basename(fname).replace(".rs", ""),
                        ha="center", va="center", fontsize=6.5)
        # module boundary + label
        ax.add_patch(plt.Rectangle((mr["x"], mr["y"]), mr["dx"], mr["dy"],
                                   fill=False, edgecolor="black", linewidth=1.6))
        ax.text(mr["x"] + mr["dx"] / 2, mr["y"] + mr["dy"] - 0.6, mod,
                ha="center", va="top", fontsize=9, fontweight="bold",
                bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="none", alpha=0.75))

    ax.set_xlim(0, W); ax.set_ylim(0, H); ax.axis("off")

    if args.mode == "diff":
        # totals per category across all shown files
        agg = {k: 0 for k, _, _ in DIFF_CATS}
        for _, files in mod_items:
            for _, d, _ in files:
                for k in agg:
                    agg[k] += d.get(k, 0)
        handles = [plt.Rectangle((0, 0), 1, 1, fc=c) for _, c, _ in DIFF_CATS]
        labels = [f"{lab} ({agg[k]})" for k, _, lab in DIFF_CATS]
        ax.legend(handles, labels, loc="lower right", fontsize=9, title="region colored by who reaches it")
        ax.set_title("Differential coverage treemap — specimen vs handwritten  "
                     "(area = region-lines; color = who UNIQUELY reaches each region)\n"
                     f"specimen-only {agg['only_spec']}  |  shared {agg['shared']}  |  "
                     f"handwritten-only {agg['only_hw']}  |  uncovered {agg['uncovered']}", fontsize=12)
        out = args.out or os.path.join(args.root, "coverage_treemap_diff.png")
    else:
        tot_all = sum(t for _, files in mod_items for _, _, t in files)
        cov_all = sum(c for _, files in mod_items for _, c, _ in files)
        sm = cm.ScalarMappable(cmap=cmap, norm=norm); sm.set_array([])
        fig.colorbar(sm, ax=ax, label="covered %", shrink=0.55, pad=0.01)
        ax.set_title(f"Coverage treemap — {args.which}  (area = executable region-lines, color = covered%)\n"
                     f"overall {cov_all}/{tot_all} region-lines covered = "
                     f"{100.0 * cov_all / tot_all:.0f}%  |  {tot_all - cov_all} uncovered", fontsize=12)
        out = args.out or os.path.join(args.root, f"coverage_treemap_{args.which}.png")
    plt.savefig(out, dpi=130, bbox_inches="tight")
    print("wrote", out)


if __name__ == "__main__":
    main()

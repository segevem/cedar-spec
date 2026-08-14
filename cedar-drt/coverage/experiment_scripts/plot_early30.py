#!/usr/bin/env python3
"""First-N-seconds coverage zoom: dense source-line coverage over the opening window,
where the main over-time graph's first sample (~1/16 of the corpus) has no points.

Reads <root>/<arm>/rep_NN_early.json ([{elapsed_secs, corpus_idx, covered_lines,
covered_lines_excl}]) produced by cov_early.py. Per arm: prepend each rep's true origin
(0,0), grid-resample onto a common time grid (NaN past each rep's last real sample), then
per-column MEDIAN + 95% bootstrap CI of the median, tail-masking columns supported by fewer
than ceil(n/2) reps. Overlays all arms; colors/order follow the run manifest so they match
the main over-time graphs. Also emits a symlog-x companion to expose the sub-second rise.
"""
import argparse, json, math, os, warnings
import numpy as np
warnings.filterwarnings("ignore", category=RuntimeWarning)  # nanmedian on fully-masked tail columns
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt

COLORS = ["#1f77b4", "#d62728", "#2ca02c", "#9467bd", "#ff7f0e"]
MARKERS = ["o", "s", "^", "D", "v"]


def load_rep(path, metric):
    s = json.load(open(path))
    if not s:
        return None
    key = "covered_lines_excl" if metric == "excl" else "covered_lines"
    x = [0.0]; y = [0.0]                       # true origin: nothing generated -> 0 covered
    for d in s:
        x.append(float(d["elapsed_secs"])); y.append(float(d.get(key, d["covered_lines"])))
    return np.array(x), np.array(y)


def boot_median_ci(M, rng, resamples=5000):
    n = M.shape[0]
    med = np.nanmedian(M, axis=0)
    if n <= 1:
        return med, med.copy(), med.copy()
    idx = rng.integers(0, n, size=(resamples, n))
    boot = np.nanmedian(M[idx], axis=1)
    return med, np.nanpercentile(boot, 2.5, axis=0), np.nanpercentile(boot, 97.5, axis=0)


def agg(root, arm, reps, metric, grid, rng):
    curves = []
    for r in range(reps):
        p = os.path.join(root, arm, f"rep_{r:02d}_early.json")
        if not os.path.exists(p):
            continue
        g = load_rep(p, metric)
        if g is None or len(g[0]) < 2:
            continue
        curves.append(g)
    if not curves:
        return None
    M = np.full((len(curves), len(grid)), np.nan)
    for i, (x, y) in enumerate(curves):
        yi = np.interp(grid, x, y)            # step/linear between real samples
        yi[grid > x[-1]] = np.nan             # no extrapolation past this rep's last sample
        M[i] = yi
    n = M.shape[0]
    support = np.sum(~np.isnan(M), axis=0)
    med, lo, hi = boot_median_ci(M, rng)
    weak = support < max(2, math.ceil(n / 2))
    med[weak] = lo[weak] = hi[weak] = np.nan
    return med, lo, hi, n


def two_dots(root, arm, metric, window, reps):
    """Medians (over reps) of the FIRST measured sample and the value at t=window — the same 2
    points the overlaid inset marked, drawn here on the standalone zoom for continuity."""
    key = "covered_lines_excl" if metric == "excl" else "covered_lines"
    t1s, y1s, y2s = [], [], []
    for r in range(reps):
        p = os.path.join(root, arm, f"rep_{r:02d}_early.json")
        if not os.path.exists(p):
            continue
        s = json.load(open(p))
        if not s:
            continue
        x = np.array([d["elapsed_secs"] for d in s]); y = np.array([d.get(key, d["covered_lines"]) for d in s])
        t1s.append(x[0]); y1s.append(y[0]); y2s.append(float(np.interp(window, x, y)))
    if not t1s:
        return None
    return (float(np.median(t1s)), float(np.median(y1s))), (window, float(np.median(y2s)))


def arm_order(root, manifest):
    if manifest and os.path.exists(manifest):
        return [a["name"] for a in json.load(open(manifest))["approaches"]]
    return sorted(d for d in os.listdir(root) if os.path.isdir(os.path.join(root, d)))


def pretty(name):
    return (name.replace("symcc-", "").replace("wt-policy-", "specimen ")
            .replace("hw-slots-off", "handwritten").replace("hw-plain", "handwritten")
            .replace("hw", "handwritten"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--manifest", default=None)
    ap.add_argument("--out", required=True)
    ap.add_argument("--metric", default="excl", choices=["raw", "excl"])
    ap.add_argument("--reps", type=int, default=20)
    ap.add_argument("--window", type=float, default=30.0)
    ap.add_argument("--grid", type=int, default=400)
    ap.add_argument("--title", default="Line coverage — first 30 seconds")
    a = ap.parse_args()
    names = arm_order(a.root, a.manifest)
    rng = np.random.default_rng(2024)
    grid = np.linspace(0.0, a.window, a.grid)
    rows = []
    for i, name in enumerate(names):
        g = agg(a.root, name, a.reps, a.metric, grid, rng)
        if g:
            rows.append((name, COLORS[i % len(COLORS)], MARKERS[i % len(MARKERS)], g))

    for logx in (False, True):
        fig, ax = plt.subplots(figsize=(10.5, 6.2))
        for name, c, mk, (med, lo, hi, n) in rows:
            ax.plot(grid, med, "-", color=c, lw=2.2, label=f"{pretty(name)} (n={n})")
            ax.fill_between(grid, lo, hi, color=c, alpha=0.13)
            dots = two_dots(a.root, name, a.metric, a.window, a.reps)
            if dots:
                (t1, y1), (t2, y2) = dots
                ax.plot([t1, t2], [y1, y2], "o", color=c, ms=7, mec="white", mew=1.0, zorder=6)
        if logx:
            ax.set_xscale("symlog", linthresh=0.5)
            ax.set_xlim(0, a.window)
            ax.set_xlabel("generation time (s) — symlog, linear below 0.5s")
        else:
            ax.set_xlim(0, a.window)
            ax.set_xlabel("generation time (s)")
        ax.set_ylabel("covered validator source-lines" if a.metric != "raw" else "covered source-lines")
        ax.set_ylim(bottom=0)
        sub = "error+annotation excluded" if a.metric == "excl" else "all lines"
        ax.set_title(f"{a.title}\nper-run median + 95% bootstrap CI · {sub} · starts at (0,0)", fontsize=11)
        ax.grid(alpha=0.3)
        ax.legend(loc="lower right", fontsize=9, framealpha=0.95)
        fig.tight_layout()
        out = a.out if not logx else os.path.splitext(a.out)[0] + "_logx.png"
        fig.savefig(out, dpi=140); print("wrote", out)
        plt.close(fig)


if __name__ == "__main__":
    main()

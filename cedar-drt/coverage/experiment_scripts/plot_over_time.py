#!/usr/bin/env python3
"""Coverage-over-time with median + bootstrap 95% CI band, across repeated runs.

For each approach, loads every rep's `diversity_over_time` series, maps input
index -> wall-clock time via that approach's throughput snapshots (falling back
to input index when throughput is absent), resamples all reps onto a common time
grid, then plots the per-run MEDIAN with a shaded bootstrap 95% CI band.

Usage: plot_over_time.py --root <dir> [--metric cumulative_3paths] [--reps N]
Reads <root>/manifest.json for the approach list when present.
"""
import argparse
import json
import os
import glob
import warnings

# Tail columns can have few reps after masking; a bootstrap resample may hit an all-NaN
# slice (harmless — that grid point just gets a NaN band point, which fill_between skips).
warnings.filterwarnings("ignore", message="All-NaN slice encountered")

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np


def _med_ci(vals, rng, resamples=5000):
    """(median, lo95, hi95) — 95% bootstrap CI OF THE MEDIAN over reps (matches the band method)."""
    v = np.asarray(vals, dtype=float)
    m = float(np.median(v))
    if len(v) <= 1:
        return m, m, m
    boot = np.median(v[rng.integers(0, len(v), size=(resamples, len(v)))], axis=1)
    return m, float(np.percentile(boot, 2.5)), float(np.percentile(boot, 97.5))


def early_band(early_dir, name, window, key, rng, gpts=80):
    """Aggregate the fine first-`window`-seconds coverage (cov_early.py's <arm>/rep_NN_early.json)
    over ALL reps into (grid, median, lo95, hi95) — same median + 95% bootstrap-CI-of-the-median
    method as the main curve, so the early region carries a proper CI BAND (not per-dot bars).
    Each rep is anchored at (0,0) and NaN past its last sample. Returns None if no reps."""
    eg = np.linspace(0.0, window, gpts)
    M = []
    for rep in range(40):
        p = os.path.join(early_dir, name, f"rep_{rep:02d}_early.json")
        if not os.path.exists(p):
            continue
        s = json.load(open(p))
        if not s:
            continue
        x = np.array([0.0] + [d["elapsed_secs"] for d in s], dtype=float)
        y = np.array([0.0] + [d.get(key, d["covered_lines"]) for d in s], dtype=float)
        yi = np.interp(eg, x, y); yi[eg > x[-1]] = np.nan
        M.append(yi)
    if not M:
        return None
    em, el, eh = boot_median_ci(np.vstack(M), rng)
    return eg, em, el, eh


def early_two_points(early_dir, name, window, key, rng):
    """Two measured points for an arm from cov_early.py's <arm>/rep_NN_early.json — the FIRST
    measured sample and the value at t=`window` — each with a 95% bootstrap CI of the median over
    ALL reps. Returns ((t1,y1,y1lo,y1hi),(t2,y2,y2lo,y2hi), nreps) or None."""
    t1s, y1s, y2s = [], [], []
    for rep in range(40):
        p = os.path.join(early_dir, name, f"rep_{rep:02d}_early.json")
        if not os.path.exists(p):
            continue
        s = json.load(open(p))
        if not s:
            continue
        x = np.array([d["elapsed_secs"] for d in s], dtype=float)
        y = np.array([d.get(key, d["covered_lines"]) for d in s], dtype=float)
        t1s.append(x[0]); y1s.append(y[0]); y2s.append(float(np.interp(window, x, y)))
    if not t1s:
        return None
    y1, y1lo, y1hi = _med_ci(y1s, rng)
    y2, y2lo, y2hi = _med_ci(y2s, rng)
    return (float(np.median(t1s)), y1, y1lo, y1hi), (window, y2, y2lo, y2hi), len(t1s)


def boot_median_ci(M, rng, resamples=5000):
    """Per-column MEDIAN across reps + 95% bootstrap CI OF THE MEDIAN (resample reps)."""
    n = M.shape[0]
    med = np.nanmedian(M, axis=0)
    if n <= 1:
        return med, med.copy(), med.copy()
    idx = rng.integers(0, n, size=(resamples, n))
    boot = np.nanmedian(M[idx], axis=1)             # [resamples, cols]
    lo = np.nanpercentile(boot, 2.5, axis=0)
    hi = np.nanpercentile(boot, 97.5, axis=0)
    return med, lo, hi


def approach_names(root, reps_hint):
    mf = os.path.join(root, "manifest.json")
    if os.path.exists(mf):
        with open(mf) as f:
            m = json.load(f)
        return [a["name"] for a in m.get("approaches", [])]
    return sorted(d for d in os.listdir(root)
                  if os.path.isdir(os.path.join(root, d, "analyze")))


def time_map(root, name, rep):
    """valid_count -> elapsed_secs from THIS rep's own throughput snapshots (with origin).
    Each rep gets its OWN map: a rep is mapped onto wall-clock via the throughput probe
    that ran alongside it, so all reps land on a comparable time axis (every rep ran the
    same collection window, so each rep's final valid_count maps to ~the window end).
    Falls back to rep_00's map only if this rep's throughput file is missing (rare), then
    None (caller then uses raw corpus_idx)."""
    # Prefer the COLLECT's OWN timeline (collect/_fuzz_stats_rep_NN.json): for guided arms the
    # corpus is produced by `collect` (generate+log+drain), NOT the separate no-drain throughput
    # PROBE. The probe generates faster than the collect can drain, so mapping corpus_idx through
    # it understates the time and compresses the curve (and, pre-backpressure, the probe count also
    # exceeds the dropped-lossy corpus). With the lossless drain the collect's valid==corpus, so its
    # stats map corpus_idx to true wall-clock. Fall back to the probe for fused/specimen arms (which
    # count-match the probe and have no collect stats).
    for r in (rep, 0):
        cp = os.path.join(root, name, "collect", f"_fuzz_stats_rep_{r:02d}.json")
        if os.path.exists(cp):
            sn = json.load(open(cp)).get("snapshots", [])
            if sn:   # snapshots are (elapsed_ms, valid_count, total_count)
                vc = np.array([0] + [x[1] for x in sn], dtype=float)
                ts = np.array([0.0] + [x[0] / 1000.0 for x in sn], dtype=float)
                return vc, ts
    for r in (rep, 0):
        p = os.path.join(root, name, "throughput", f"rep_{r:02d}.json")
        if not os.path.exists(p):
            continue
        t = json.load(open(p))
        snaps = t.get("snapshots", [])
        if not snaps:
            continue
        vc = np.array([0] + [s["valid_count"] for s in snaps], dtype=float)
        ts = np.array([0.0] + [s["elapsed_secs"] for s in snaps], dtype=float)
        return vc, ts
    return None


def rep_series(root, name, rep, metric):
    # Source line coverage lives in its own over-time file (from coverage_analyze.py),
    # which already carries elapsed_secs + corpus_idx per snapshot — no time_map needed.
    if metric == "source_lines_covered":
        p = os.path.join(root, name, "coverage", f"rep_{rep:02d}_over_time.json")
        if not os.path.exists(p):
            return None
        s = json.load(open(p))
        if not s:
            return None
        # Sharded coverage over-time is keyed by cumulative corpus_idx (per shard boundary),
        # not replay wall-clock (shards run in parallel). Map corpus_idx -> collect wall-clock
        # via the throughput valid_count time-map (same as the diversity curves). Fall back to
        # legacy elapsed_secs when corpus_idx is absent.
        if all("corpus_idx" in d for d in s):
            # Map cumulative corpus_idx -> wall-clock via THIS rep's throughput probe. Valid
            # ONLY for reps whose collect count-matched the probe (corpus_idx_max ~= probe
            # V_t). Reps that undershot (fast generator, I/O-bound drain) are dropped as
            # incomplete in main() via `rep_complete`, so we never plot a fake-early endpoint.
            idx = np.array([d["corpus_idx"] for d in s], dtype=float)
            y = np.array([d["covered_lines"] for d in s], dtype=float)
            tm = time_map(root, name, rep)
            x = np.interp(idx, tm[0], tm[1]) if tm else idx
            return x, y
        x = np.array([d["elapsed_secs"] for d in s], dtype=float)
        y = np.array([d["covered_lines"] for d in s], dtype=float)
        return x, y
    # Throughput: cumulative valid inputs vs wall-clock. Prefer the throughput PROBE
    # snapshots (`throughput/rep_NN.json`), which exist for EVERY arm — guided AND fused.
    # (The old source, `collect/rep_NN/edge_snapshots.json`, is written only by the fused
    # specimen collect, so guided/handwritten arms were silently dropped and the graph showed
    # only wt-policy.) Fall back to collect edge_snapshots if a probe file is somehow absent.
    if metric == "throughput":
        p = os.path.join(root, name, "throughput", f"rep_{rep:02d}.json")
        if os.path.exists(p):
            snaps = json.load(open(p)).get("snapshots", [])
            if len(snaps) >= 2:
                x = np.array([0.0] + [d["elapsed_secs"] for d in snaps], dtype=float)
                y = np.array([0.0] + [d["valid_count"] for d in snaps], dtype=float)
                return x, y
        p2 = os.path.join(root, name, "collect", f"rep_{rep:02d}", "edge_snapshots.json")
        if os.path.exists(p2):
            s = json.load(open(p2))
            if len(s) >= 2:
                x = np.array([d["elapsed_secs"] for d in s], dtype=float)
                y = np.array([d["valid"] for d in s], dtype=float)
                return x, y
        return None
    # Instantaneous valid/s = derivative of cumulative valid_count. Unlike cumulative
    # throughput (whose integral hides the wobble), this exposes the cold-start transient and
    # the per-interval jitter directly. From the probe snapshots (all arms).
    if metric == "throughput_rate":
        p = os.path.join(root, name, "throughput", f"rep_{rep:02d}.json")
        if not os.path.exists(p):
            return None
        snaps = json.load(open(p)).get("snapshots", [])
        if len(snaps) < 3:
            return None
        t = np.array([d["elapsed_secs"] for d in snaps], dtype=float)
        v = np.array([d["valid_count"] for d in snaps], dtype=float)
        dt = np.diff(t)
        rate = np.diff(v) / np.where(dt > 0, dt, 1.0)
        return t[1:], rate  # rate assigned to each interval's end time
    p = os.path.join(root, name, "analyze", f"rep_{rep:02d}.json")
    if not os.path.exists(p):
        return None
    ds = json.load(open(p)).get("diversity_over_time", [])
    if not ds:
        return None
    idx = np.array([d["input_idx"] for d in ds], dtype=float)
    y = np.array([d[metric] for d in ds], dtype=float)
    tm = time_map(root, name, rep)
    x = np.interp(idx, tm[0], tm[1]) if tm else idx
    return x, y


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--metric", default="cumulative_3paths")
    ap.add_argument("--reps", type=int, default=20)
    ap.add_argument("--resamples", type=int, default=5000)
    ap.add_argument("--grid", type=int, default=40, help="time-grid points")
    ap.add_argument("--zoom", action="store_true",
                    help="zoom the y-axis to the actual data range (excluding the (0,0) origin) so "
                         "near-saturated curves show detail")
    ap.add_argument("--early", default=None,
                    help="dir with <arm>/rep_NN_early.json (cov_early.py); drawn in a first-30s INSET")
    ap.add_argument("--early-window", type=float, default=30.0)
    ap.add_argument("--inset-rect", type=float, nargs=4, default=[0.46, 0.16, 0.40, 0.52],
                    metavar=("X0", "Y0", "W", "H"),
                    help="inset position (axes fraction) for the first-30s early detail")
    ap.add_argument("--xscale", default="linear", choices=["linear", "symlog"],
                    help="symlog makes the first-30s dots legible alongside the full hour")
    args = ap.parse_args()

    rng = np.random.default_rng(2024)
    names = approach_names(args.root, args.reps)
    colors = plt.cm.tab10(np.linspace(0, 1, max(len(names), 1)))
    fig, ax = plt.subplots(figsize=(11, 6.5))
    x_is_time = args.metric in ("throughput", "source_lines_covered", "throughput_rate")
    # Instantaneous rate needs fine time resolution to show the cold-start spike + jitter.
    gpts = max(args.grid, 300) if args.metric == "throughput_rate" else args.grid

    # Dense metrics (many regularly-sampled points) read best as a clean LINE; the sparse
    # source-coverage series (≈16 pts/rep) keeps per-sample markers so the few real points show.
    line_only = args.metric != "source_lines_covered"

    arm_series = []   # (name, color, [(x,y)...]) collected first so we can build ONE global time grid
    for ci, name in enumerate(names):
        # Build per-rep series, then DROP incomplete reps. For corpus-indexed metrics the x is
        # wall-clock mapped through the rep's OWN throughput probe, valid only when that rep's
        # collect count-matched the probe (corpus_idx_max ~= probe V_t). Reps whose collect
        # UNDERSHOT (fast generator, I/O-bound drain: e.g. hw-slots-off reps that collected
        # 60k vs the probe's ~480k) would map their small corpus to a fake-early second, so we
        # exclude them rather than distort the median. Kept reps ran the full window -> their
        # curves land on a true, comparable wall-clock axis. (n in the legend reflects kept.)
        # Keep ALL reps with a real series. We deliberately do NOT drop reps whose mapped
        # endpoint is short relative to the throughput probe: a GUIDED arm count-matches to a
        # per-rep V_t and its drain collects a variable-size corpus, so a rep that legitimately
        # collected fewer inputs (and replayed them fully) ends earlier on the wall-clock axis
        # but is COMPLETE — the old `< 0.9*probe_end` rule wrongly discarded ~half of them. The
        # only reps we skip are DEGENERATE ones with no time extent at all (s[0][-1] <= 0), e.g.
        # a shard-failed replay whose coverage never accumulated.
        series = []
        for rep in range(args.reps):
            s = rep_series(args.root, name, rep, args.metric)
            if not s or float(s[0][-1]) <= 0:
                continue
            # Prepend the true origin (t=0, value=0) to each cumulative rep so its curve starts at
            # (0,0) and interpolation on the common grid is anchored (rate is a derivative -> no origin).
            x, y = s
            # Prepend the true origin (t=0, value=0) so the curve starts at (0,0). The early detail
            # (first 30s) lives in an INSET, so the main axes stay the plain overlaid graph.
            if args.metric != "throughput_rate":
                x = np.concatenate([[0.0], x]); y = np.concatenate([[0.0], y])
            series.append((x, y))
        if not series:
            continue
        arm_series.append((name, colors[ci], series))

    # ONE common wall-clock grid for every arm, spanning to the LATEST real sample across all reps
    # (each rep's x is its own probe-mapped time — the probe is the source of truth for timing). Each
    # rep is interpolated onto the grid; grid points BEYOND that rep's last real sample are NaN (never
    # extrapolated), so a rep whose collect undershot the probe simply drops out of the late columns
    # and the median there is taken over the reps that genuinely reached that time (CI widens honestly)
    # — instead of truncating every arm to the shortest rep's end (which cut the hw curve off at ~2500s).
    plotted = []
    xmax = max((x[-1] for _, _, series in arm_series for x, _ in series), default=1.0)
    grid = np.linspace(0.0, xmax, gpts)
    for name, color, series in arm_series:
        M = []
        for x, y in series:
            yi = np.interp(grid, x, y)
            yi[grid > x[-1]] = np.nan                # no fabricated extension past this rep's data
            M.append(yi)
        M = np.vstack(M)
        n = M.shape[0]
        med, lo, hi = boot_median_ci(M, rng, args.resamples)
        # Drop tail (and any) grid columns backed by too FEW reps. Per-rep end-times vary slightly
        # (each maps through its own probe, ~3600-3620s), so the final columns are supported by only
        # the 1-2 longest reps — the median there collapses to those outliers and ticks up/down (a
        # sparse-tail ARTIFACT, not a real jump). Require >= half the reps for a plotted point.
        support = np.sum(~np.isnan(M), axis=0)
        weak = support < max(2, int(np.ceil(n * 0.5)))
        med[weak] = lo[weak] = hi[weak] = np.nan
        plotted.append((grid, med, lo, hi, color, f"{name} (n={n})", name))

    for mx, med, lo, hi, c, lbl, name in plotted:
        # Plain overlaid look: sparse coverage keeps its per-sample markers, dense metrics a line.
        if line_only:
            ax.plot(mx, med, "-", color=c, lw=1.8, label=lbl)
        else:
            mev = max(1, len(mx) // 30)                            # sparse coverage -> ~30 markers
            ax.plot(mx, med, "-o", color=c, lw=1.8, ms=4, markevery=mev, label=lbl)
        ax.fill_between(mx, lo, hi, color=c, alpha=0.18)

    # Early detail lives in an INSET (the main axes stay the plain overlaid graph): first `window`
    # seconds at full resolution — per-arm median + 95% CI band (same method) + the 2 measured dots.
    drew_early = False
    if args.early and args.metric == "source_lines_covered":
        colmap = {name: color for name, color, _ in arm_series}
        axin = ax.inset_axes(args.inset_rect)
        for name, c in colmap.items():
            band = early_band(args.early, name, args.early_window, "covered_lines", rng)
            if not band:
                continue
            eg, em, el, eh = band
            axin.fill_between(eg, el, eh, color=c, alpha=0.18)
            axin.plot(eg, em, "-", color=c, lw=1.6)
            pts = early_two_points(args.early, name, args.early_window, "covered_lines", rng)
            if pts:
                (t1, y1, *_), (t2, y2, *_), _ = pts
                axin.plot([t1, t2], [y1, y2], "o", color=c, ms=5, mec="white", mew=0.7, zorder=6)
            drew_early = True
        axin.set_xlim(0, args.early_window); axin.set_ylim(bottom=0)
        axin.set_title(f"first {int(args.early_window)}s (measured)", fontsize=8)
        axin.tick_params(labelsize=7); axin.grid(alpha=0.3)

    title_tail = "reps resampled onto common probe-time grid; starts at (0,0)"
    if args.zoom and plotted:
        # Zoom y to the PLATEAU (settled region: samples in the second half of the time axis),
        # not the global min — the early rise + wide early CI would otherwise force a low floor and
        # squash the plateau where the arms actually differ. Curves enter steeply from the bottom-left.
        los, his = [], []
        for mx, med, lo, hi, _, _, _ in plotted:
            if len(mx) < 2:
                continue
            half = mx[-1] * 0.5
            keep = mx >= half
            los.append(lo[keep]); his.append(hi[keep])
        if los:
            los = np.concatenate(los); his = np.concatenate(his)
            ymin, ymax = float(np.nanmin(los)), float(np.nanmax(his))
            pad = max((ymax - ymin) * 0.12, 1.0)
            ax.set_ylim(ymin - pad, ymax + pad)
            title_tail = "common probe-time grid; y zoomed to plateau"
    if drew_early:
        title_tail += f" · inset = measured first {int(args.early_window)}s (median + 95% CI)"
    if args.xscale == "symlog":
        ax.set_xscale("symlog", linthresh=max(args.early_window, 1.0))
    ax.set_xlabel("wall-clock time (s) — from throughput probe")
    ax.set_ylabel(args.metric.replace("_", " "))
    ax.set_title(f"{args.metric.replace('_',' ')} over time — per-run median + 95% bootstrap CI of the median\n"
                 f"{title_tail}")
    ax.grid(alpha=0.3)
    ax.legend(fontsize=8, ncol=2)
    ax.set_xlim(left=0)
    fig.tight_layout()
    suffix = ("_early" if drew_early else "") + ("_symlog" if args.xscale == "symlog" else "")
    out = os.path.join(args.root, f"over_time_{args.metric}{suffix}.png")
    fig.savefig(out, dpi=130)
    print("wrote", os.path.abspath(out))


if __name__ == "__main__":
    main()

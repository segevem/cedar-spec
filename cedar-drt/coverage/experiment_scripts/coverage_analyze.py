#!/usr/bin/env python3
"""Input-driven validator LINE-coverage analysis for the generator comparison.

Distinct from the guided fuzzer's sancov edge coverage: replays each rep's corpus
through a `-C instrument-coverage` build of the validator and derives *source line*
coverage via llvm-cov, EXCLUDING the harness (protobuf decode +
`ValidatorSchema::try_from`/construction) via `IGNORE_REGEX`.

Storage rules (important):
  * The CORPUS is never stored locally. With --s3-bucket/--s3-root the replay
    STREAMS the corpus from S3 (in-memory, per batch, dropped).
  * `.profraw` is only *transiently* local while llvm-cov reads it (~MB/rep), then
    UPLOADED to S3 and DELETED locally — never accumulated.

Outputs (uploaded to `s3://<bucket>/<root>/…` in S3 mode; written under
`<root>/…` in local mode):
  * `<approach>/coverage/rep_NN/` — snapshot .profraw + snapshots.json + over_time.json
  * `<approach>/analyze/rep_NN.json` gains `source_lines_covered` (for bootstrap_ci)
  * `results/coverage_compare.json` — per-approach totals + pairwise Jaccard and
    only-A/only-B set differences, localized (demangled) by function.

Instrumented binary (S3 mode needs the `s3` feature too):
  RUSTFLAGS="-C instrument-coverage" cargo build --release \
    --bin cedar-drt-coverage --features profraw,s3
"""
import argparse, json, os, re, shutil, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

# The profraw is now VALIDATION-SCOPED at the source: `ValidationCov` in the collect
# loop resets the LLVM counters right before each `target.run` and folds only that
# delta, so generation / k-path analysis / protobuf decode+encode / schema
# construction (`Schema::try_from`) never appear in the profile at all. That means we
# no longer exclude proto / json_schema / `validator/schema.rs` construction here —
# doing so would now WRONGLY drop *validate-time* schema access (the principals /
# resources / attributes accessors the typechecker uses). This regex only drops what
# is definitionally not the measured target: external deps, the stdlib, tests, and the
# harness crates (which the dynamic scope already keeps out, but belt-and-suspenders).
# Overridable via $COVERAGE_IGNORE_REGEX. Default measures the VALIDATOR (drops
# cedar-policy-symcc). For the SymCC experiment the runner sets COVERAGE_IGNORE_REGEX to a
# regex that KEEPS cedar-policy-symcc (the compiler under test) and instead drops the
# validator crates — matching the flipped INSTRUMENT_CRATES for that run.
IGNORE_REGEX = os.environ.get(
    "COVERAGE_IGNORE_REGEX",
    r"/\.cargo/registry|/rustc/"
    r"|/tests/|/test/|_test\.rs|/test\.rs|test_579"
    r"|/kpath|cedar-policy-generators|cedar-drt|cedar-lean-ffi|cedar-policy-symcc",
)
_IGNORE_RE = re.compile(IGNORE_REGEX)

# LINE-level exclusion on TOP of IGNORE_REGEX: drop specific (file,line) from BOTH
# covered and total, so coverage compares only non-error code. Set
# $COVERAGE_EXCLUDE_LINES to a file of "relpath:line" (relpath = a path suffix like
# cedar-policy-core/src/..). Blank / `#` lines ignored. No-op if the var is unset.
_EXCLUDE = set()
_ex_path = os.environ.get("COVERAGE_EXCLUDE_LINES")
if _ex_path and os.path.exists(_ex_path):
    for _line in open(_ex_path):
        _line = _line.strip()
        if not _line or _line.startswith("#"):
            continue
        _pf, _, _ln = _line.rpartition(":")
        if _pf and _ln.isdigit():
            _EXCLUDE.add((_pf, int(_ln)))

def _excl_norm(p):
    for _a in ("cedar-policy-core/", "cedar-policy-formatter/", "cedar-policy-symcc/", "cedar-policy/"):
        _i = p.find(_a)
        if _i >= 0:
            return p[_i:]
    return p

def _line_excluded(f, ln):
    return bool(_EXCLUDE) and (_excl_norm(f), ln) in _EXCLUDE

# The oracle the replay drives (passed to cedar-drt-coverage --target). Defaults to
# validation-drt so existing validation runs are unchanged; a symcc run exports
# TARGET=symcc-term-never-errors so the replay drives SymccTermDrt (exercising the symbolic
# compiler, which is the instrumented crate) instead of the validator.
REPLAY_TARGET = os.environ.get("TARGET", "validation-drt")

PROFDATA, LLVMCOV = None, None


def demangle(sym):
    """Readable name from a Rust v0/legacy mangled symbol, no external tool."""
    parts = re.findall(r"(\d+)([A-Za-z_][A-Za-z0-9_]*)", sym)
    names = [nm for _, nm in parts if not (nm.startswith("Cs") and len(nm) > 8)]
    return "::".join(names[-4:]) if names else sym


def find_llvm_tools():
    sysroot = subprocess.check_output(["rustc", "--print", "sysroot"]).decode().strip()
    def find(name):
        out = subprocess.check_output(["find", sysroot, "-name", name]).decode().splitlines()
        if not out:
            sys.exit(f"missing {name} (rustup component add llvm-tools-preview)")
        return out[0]
    return find("llvm-profdata"), find("llvm-cov")


def s3_cp(src, dst, recursive=False):
    args = ["aws", "s3", "cp", src, dst, "--quiet"] + (["--recursive"] if recursive else [])
    subprocess.run(args, check=False)


def merge(profraws, out_pd):
    subprocess.run([PROFDATA, "merge", "-sparse", *profraws, "-o", out_pd],
                   check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def export(profdata, summary_only, binary):
    # Each approach is analyzed with the binary that PRODUCED its profraw (fused
    # specimen -> cedar-experiment; guided replay -> cedar-drt-coverage). Both link the
    # same cedar-policy compiled the same way, so llvm-cov maps their profraws to the
    # SAME (file,line) source coordinates — directly comparable across binaries.
    args = [LLVMCOV, "export", binary, f"-instr-profile={profdata}",
            "-format=text", f"--ignore-filename-regex={IGNORE_REGEX}"]
    if summary_only:
        args.append("-summary-only")
    out = subprocess.run(args, check=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL).stdout
    return json.loads(out)


def covered_lines_total(profdata, binary):
    d = export(profdata, True, binary)["data"][0]["totals"]["lines"]
    return int(d["covered"])

def covered_counts(profdata, binary):
    """(raw, excluded) covered REGION-LINE counts from one export. `excluded` drops the
    lines in $COVERAGE_EXCLUDE_LINES (sound error-only elision); `raw` keeps them. Both
    honor IGNORE_REGEX. Used for the raw-vs-excluded over-time overlay."""
    data = export(profdata, False, binary)["data"][0]
    cov = set()
    for fn in data.get("functions", []):
        files = fn.get("filenames", [])
        for r in fn.get("regions", []):
            ls, le, count, fid = r[0], r[2], r[4], r[5]
            if count > 0 and fid < len(files) and not _IGNORE_RE.search(files[fid]):
                for ln in range(ls, le + 1):
                    cov.add((files[fid], ln))
    raw = len(cov)
    exc = sum(1 for (ff, ln) in cov if not _line_excluded(ff, ln))
    return raw, exc


def covered_line_set_by_function(profdata, binary):
    """{function: set((file,line))} covered (region ExecutionCount>0 spans its lines).

    NOTE: `llvm-cov export --ignore-filename-regex` filters the *totals/files* summary
    but still lists every function (incl. from ignored files), so we re-apply the
    exclusion here per-file — otherwise harness/generator code (e.g. the handwritten
    generator's ExprGenerator) would leak into the set/diff and inflate one side."""
    data = export(profdata, False, binary)["data"][0]
    per_fn = {}
    for fn in data.get("functions", []):
        files = fn.get("filenames", [])
        covered = per_fn.setdefault(fn.get("name", "?"), set())
        for r in fn.get("regions", []):
            ls, _, le, _, count, fid = r[0], r[1], r[2], r[3], r[4], r[5]
            if count > 0 and fid < len(files) and not _IGNORE_RE.search(files[fid]):
                for ln in range(ls, le + 1):
                    if not _line_excluded(files[fid], ln):
                        covered.add((files[fid], ln))
        if not covered:
            per_fn.pop(fn.get("name", "?"), None)
    return per_fn


def module_of(path):
    """Coarse module for a source file: the dir segment right after `src/` (e.g.
    validator, ast, proto, entities), else the parent dir name."""
    parts = path.replace("\\", "/").split("/")
    if "src" in parts:
        i = parts.index("src")
        if i + 2 < len(parts):   # src/<module>/<...>/file.rs
            return parts[i + 1]
        if i + 1 < len(parts):   # src/file.rs
            return parts[i + 1].rsplit(".", 1)[0]
    return parts[-2] if len(parts) >= 2 else "?"


def file_sets(profdata, binary):
    """{file: (covered_line_set, total_line_set)} in REGION-LINES (a line is covered if any
    region over it ran). Harness/out-of-crate files dropped via IGNORE_REGEX."""
    data = export(profdata, False, binary)["data"][0]
    out = {}
    for fn in data.get("functions", []):
        fnames = fn.get("filenames", [])
        for r in fn.get("regions", []):
            ls, le, count, fid = r[0], r[2], r[4], r[5]
            if fid >= len(fnames):
                continue
            f = fnames[fid]
            if _IGNORE_RE.search(f):
                continue
            cov, tot = out.setdefault(f, (set(), set()))
            for ln in range(ls, le + 1):
                if _line_excluded(f, ln):
                    continue
                tot.add(ln)
                if count > 0:
                    cov.add(ln)
    return out


def file_coverage(profdata, binary):
    """{file: {"covered","total","module"}} counts — `total` = every executable region-line
    in the file, so uncovered = total - covered."""
    return {f: {"covered": len(cov), "total": len(tot), "module": module_of(f)}
            for f, (cov, tot) in file_sets(profdata, binary).items()}


def diff_map_of(spec_profdata, hw_profdata, binary):
    """Per-file DIFFERENTIAL coverage between the specimen union and the handwritten union:
    who reaches each region-line. {file: {only_spec, only_hw, shared, uncovered, total,
    module}} — shows what each approach finds UNIQUELY vs shared vs nobody."""
    ss = file_sets(spec_profdata, binary)
    hs = file_sets(hw_profdata, binary)
    out = {}
    for f in set(ss) | set(hs):
        sc, st = ss.get(f, (set(), set()))
        hc, ht = hs.get(f, (set(), set()))
        total = st | ht
        out[f] = {"only_spec": len(sc - hc), "only_hw": len(hc - sc),
                  "shared": len(sc & hc), "uncovered": len(total - (sc | hc)),
                  "total": len(total), "module": module_of(f)}
    return out


def flat(set_by_fn):
    out = set()
    for s in set_by_fn.values():
        out |= s
    return out


def over_time_series(snap_dir, manifest, binary):
    """Over-time coverage points. Both fused collect and the faithful replay record an
    in-process region-hit COUNT per point (`counters_hit`, no profraw — nothing
    accumulates). A legacy snapshot-`.profraw` shape is still handled via llvm-cov."""
    series = []
    for m in manifest:
        if "counters_hit" in m:
            covered = m["counters_hit"]
        elif "file" in m:
            pr = os.path.join(snap_dir, m["file"]); pd = pr + ".profdata"
            try:
                merge([pr], pd); covered, covered_excl = covered_counts(pd, binary)
            except subprocess.CalledProcessError:
                continue
        else:
            continue
        pt = {"corpus_idx": m["corpus_idx"], "elapsed_secs": m["elapsed_secs"],
              "covered_lines": covered}
        if "counters_hit" not in m:
            pt["covered_lines_excl"] = covered_excl
        series.append(pt)
    return series


def process_rep(root, approach, rep, snapshots, s3_bucket, s3_root, keep_dir, from_collect, binary):
    """Get the rep's cumulative `.profraw` snapshots, derive the over-time series,
    upload profraw+results to S3, and keep only final.profraw locally (in keep_dir)
    for the per-approach merge. Returns dict or None.

    from_collect=True (FUSED): use the snapshots collect already produced at
    `<rep>/coverage/` — no replay, no re-validation. Else replay: stream from S3
    (`--replay-s3`) or a local corpus (`--replay-proto`)."""
    cov_s3 = f"s3://{s3_bucket}/{s3_root}/{approach}/rep_{rep:02d}/coverage" if s3_bucket else None
    final_local = os.path.join(keep_dir, f"{approach}_rep{rep:02d}_final.profraw")
    replay_tmp = None
    if from_collect:
        # FUSED: over-time counts are in snapshots.json (kept local; profraw was
        # uploaded to S3 and DELETED locally so it never accumulates). Fetch the
        # single final profraw from S3 (or use the local one under local storage).
        cov = os.path.join(root, approach, "collect", f"rep_{rep:02d}", "coverage")
        os.makedirs(cov, exist_ok=True)
        snapf = os.path.join(cov, "snapshots.json")
        if not os.path.isfile(snapf) and cov_s3:
            s3_cp(f"{cov_s3}/snapshots.json", snapf)
        if not os.path.isfile(snapf):
            return None
        with open(snapf) as f:
            manifest = json.load(f)
        series = over_time_series(cov, manifest, binary)
        local_final = os.path.join(cov, "final.profraw")
        if os.path.exists(local_final):
            shutil.copy(local_final, final_local)
        elif cov_s3:
            s3_cp(f"{cov_s3}/final.profraw", final_local)   # transient; deleted after merge
    else:
        # On-demand replay fallback: regenerate/replay and dump snapshot profraws to a
        # temp dir (transient — deleted below). Streams corpus from S3, never stores it.
        replay_tmp = tempfile.mkdtemp(prefix=f"cov_{approach}_{rep:02d}_")
        env = dict(os.environ, LLVM_PROFILE_FILE=os.path.join(replay_tmp, "live.profraw"),
                   REPLAY_PROFRAW_DIR=replay_tmp, REPLAY_SNAPSHOTS=str(snapshots))
        if s3_bucket:
            cmd = [binary, "--replay-s3-bucket", s3_bucket,
                   "--replay-s3-prefix", f"{s3_root}/{approach}/rep_{rep:02d}",
                   "--target", REPLAY_TARGET]
        else:
            corpus = os.path.join(root, approach, "collect", f"rep_{rep:02d}", "corpus")
            if not os.path.isdir(corpus):
                shutil.rmtree(replay_tmp, ignore_errors=True); return None
            cmd = [binary, "--replay-proto", corpus, "--target", REPLAY_TARGET]
        try:
            subprocess.run(cmd, env=env, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            with open(os.path.join(replay_tmp, "snapshots.json")) as f:
                manifest = json.load(f)
        except (subprocess.CalledProcessError, FileNotFoundError):
            shutil.rmtree(replay_tmp, ignore_errors=True); return None
        series = over_time_series(replay_tmp, manifest, binary)
        if os.path.exists(os.path.join(replay_tmp, "final.profraw")):
            shutil.copy(os.path.join(replay_tmp, "final.profraw"), final_local)

    # over-time series to the plot location (plot_over_time.py reads this path).
    cov_dir = os.path.join(root, approach, "coverage")
    os.makedirs(cov_dir, exist_ok=True)
    with open(os.path.join(cov_dir, f"rep_{rep:02d}_over_time.json"), "w") as f:
        json.dump(series, f, indent=2)

    # per-rep harness-excluded line count from the (single) final profraw.
    covered = series[-1]["covered_lines"] if series else 0
    if os.path.exists(final_local):
        pd = final_local + ".pd"
        try:
            merge([final_local], pd); covered = covered_lines_total(pd, binary)
            os.remove(pd)
        except subprocess.CalledProcessError:
            pass
    if replay_tmp:
        shutil.rmtree(replay_tmp, ignore_errors=True)   # drop transient replay profraws
    return {"rep": rep, "final_profraw": final_local if os.path.exists(final_local) else None,
            "final_covered": covered}


def replay_one_shard(approach, rep, shard, shards, s3_bucket, s3_root, root, binary, tmp_root):
    """Replay ONE contiguous shard of a rep's corpus through the instrumented binary and
    dump its `final.profraw`. Returns (shard, profraw_or_None, validated_count). This is
    the unit of the flattened (approach, rep, shard) thread pool — N shards per rep run in
    parallel across the box's cores, each streaming only its ~1/N of the corpus from S3."""
    d = os.path.join(tmp_root, f"{approach}_r{rep:02d}_s{shard:02d}")
    os.makedirs(d, exist_ok=True)
    env = dict(os.environ, LLVM_PROFILE_FILE=os.path.join(d, "live.profraw"),
               REPLAY_PROFRAW_DIR=d, REPLAY_SNAPSHOTS="0")  # over-time comes from shard merges, not intra-shard snaps
    if s3_bucket:
        cmd = [binary, "--replay-s3-bucket", s3_bucket,
               "--replay-s3-prefix", f"{s3_root}/{approach}/rep_{rep:02d}",
               "--replay-shard", str(shard), "--replay-shards", str(shards),
               "--target", REPLAY_TARGET]
    else:
        corpus = os.path.join(root, approach, "collect", f"rep_{rep:02d}", "corpus")
        if not os.path.isdir(corpus):
            return (shard, None, 0)
        # Local proto replay isn't batch-sharded; only shard 0 does the (whole) corpus.
        if shard != 0:
            return (shard, None, 0)
        cmd = [binary, "--replay-proto", corpus]
    # Capture stderr (do NOT discard) and RETRY. A shard that crashes/OOMs/times-out used to
    # be dropped silently (except -> None), which truncated the merged coverage over-time and
    # depressed final coverage for that rep WITH NO WARNING (this is the "line-coverage stage
    # failed" bug — collect drained the full corpus, but ~14/16 replay shards silently died).
    # Now: keep stderr for diagnosis, retry (recovers transient S3 timeouts), and if a shard
    # never yields a profraw, WARN loudly with the exit code + stderr tail.
    errlog = os.path.join(d, "shard_stderr.log")
    last_rc = None
    for _attempt in range(2):
        try:
            with open(errlog, "w") as ef:
                subprocess.run(cmd, env=env, check=True, stdout=subprocess.DEVNULL, stderr=ef)
            last_rc = 0
            break
        except subprocess.CalledProcessError as e:
            last_rc = e.returncode
        except FileNotFoundError:
            last_rc = "binary-not-found"
            break  # retry won't help
    prof = os.path.join(d, "final.profraw")
    if not os.path.exists(prof):
        try:
            tail = "".join(open(errlog).readlines()[-3:]).strip().replace("\n", " | ")
        except OSError:
            tail = ""
        print(f"  WARNING: coverage shard {approach} rep{rep:02d} s{shard:02d} produced NO "
              f"profraw (exit={last_rc}) — rep coverage will be PARTIAL/truncated. stderr: {tail}",
              flush=True)
        return (shard, None, 0)
    validated = 0
    snapf = os.path.join(d, "snapshots.json")
    if os.path.isfile(snapf):
        try:
            man = json.load(open(snapf))
            if man:
                validated = man[-1].get("validated", 0)
        except (ValueError, OSError):
            pass
    return (shard, prof if os.path.exists(prof) else None, validated)


def assemble_rep(approach, rep, shard_results, root, binary, keep_dir):
    """Combine a rep's shard profraws. CONTIGUOUS shards in order → cumulative-merge gives
    the coverage-over-time curve (covered lines vs cumulative corpus_idx, one point per
    shard boundary); the full merge is the rep's final coverage (union). Writes
    `coverage/rep_NN_over_time.json` and returns {rep, final_profdata, final_covered}."""
    shard_results = sorted([r for r in shard_results if r[1]], key=lambda r: r[0])
    if not shard_results:
        return None
    series, cum_inputs, have = [], 0, False
    cum_pd = os.path.join(keep_dir, f"{approach}_r{rep:02d}_cum.profdata")
    for shard, prof, validated in shard_results:
        cum_inputs += validated
        if have:
            merge([cum_pd, prof], cum_pd + ".tmp"); os.replace(cum_pd + ".tmp", cum_pd)
        else:
            merge([prof], cum_pd); have = True
        try:
            covered, covered_excl = covered_counts(cum_pd, binary)
        except subprocess.CalledProcessError:
            covered = series[-1]["covered_lines"] if series else 0
            covered_excl = series[-1].get("covered_lines_excl", covered) if series else 0
        series.append({"snapshot": len(series), "corpus_idx": cum_inputs,
                       "elapsed_secs": 0.0, "covered_lines": covered,
                       "covered_lines_excl": covered_excl})
        try:
            os.remove(prof)  # drop the shard profraw once folded in
        except OSError:
            pass
    final_local = os.path.join(keep_dir, f"{approach}_rep{rep:02d}_final.profdata")
    os.replace(cum_pd, final_local)
    final_covered = series[-1]["covered_lines"] if series else 0
    cov_dir = os.path.join(root, approach, "coverage")
    os.makedirs(cov_dir, exist_ok=True)
    with open(os.path.join(cov_dir, f"rep_{rep:02d}_over_time.json"), "w") as f:
        json.dump(series, f, indent=2)
    return {"rep": rep, "final_profdata": final_local, "final_covered": final_covered}


def compare(per_approach_sets, summary_totals, guided_names):
    """Combine the per-approach (file,line) sets into a cross-approach diff. The guided
    approaches (cargo-fuzz "handwritten") form one side, the fused specimen approaches the
    other. Both sides were measured over the SAME ValidationDrt target, so the sets are
    directly comparable even though they came from different instrumented binaries."""
    flats = {a: flat(s) for a, s in per_approach_sets.items()}
    guided = [a for a in per_approach_sets if a in guided_names]
    specimen = [a for a in per_approach_sets if a not in guided_names]
    doc = {"units_note": "shared/only_*/jaccard are region-lines; source_lines_covered is accurate executable lines",
           "guided_approaches": guided, "specimen_approaches": specimen,
           "approaches": {a: {"source_lines_covered": summary_totals.get(a),
                              "covered_region_lines": len(f)} for a, f in flats.items()},
           "pairs": {}}

    def union_by_fn(names):
        u = {}
        for a in names:
            for fn, s in per_approach_sets[a].items():
                u.setdefault(fn, set()).update(s)
        return u

    def pair(name, a_by_fn, b_by_fn):
        a_set, b_set = flat(a_by_fn), flat(b_by_fn)
        inter, union = a_set & b_set, a_set | b_set
        by_fn = {}
        for fn, s in a_by_fn.items():
            oa = len(s - b_set)
            if oa: by_fn.setdefault(fn, {})["only_a"] = oa
        for fn, s in b_by_fn.items():
            ob = len(s - a_set)
            if ob: by_fn.setdefault(fn, {})["only_b"] = ob
        ranked = sorted(by_fn.items(), key=lambda kv: kv[1].get("only_a", 0) + kv[1].get("only_b", 0), reverse=True)
        doc["pairs"][name] = {
            "shared": len(inter), "only_a": len(a_set - b_set), "only_b": len(b_set - a_set),
            "jaccard": (len(inter) / len(union)) if union else 1.0,
            # Store the RAW mangled symbol; demangling happens at PLOT time (rustfilt),
            # so the chart is fixable without re-running the heavy replay (and a weak
            # built-in demangler never bakes garbage names into the results).
            "by_function": [{"fn": fn, **d} for fn, d in ranked[:50]],
        }

    # specimen (a=only_a) vs the guided/handwritten baseline (b=only_b). "handwritten" is
    # kept in the pair names for plot continuity (= the guided union).
    if guided and specimen:
        gunion = union_by_fn(guided)
        for a in specimen:
            pair(f"{a}_vs_handwritten", per_approach_sets[a], gunion)
        pair("specimen_union_vs_handwritten", union_by_fn(specimen), gunion)
        # ALSO diff each specimen approach against EACH individual guided arm, not just the
        # union. The union folds coverage unique to ONE guided arm (e.g. slot/template lines
        # from a slots-on target) into the gap, inflating "handwritten-only" against a
        # specimen that structurally can't produce that arm's inputs. Per-arm pairs give the
        # true apples-to-apples comparison (e.g. static specimen vs a slot-free handwritten arm).
        for a in specimen:
            for g in guided:
                pair(f"{a}_vs_{g}", per_approach_sets[a], per_approach_sets[g])
    # If there are exactly two guided variants (e.g. plain vs well-typed), diff them too.
    if len(guided) == 2:
        pair(f"{guided[0]}_vs_{guided[1]}", per_approach_sets[guided[0]], per_approach_sets[guided[1]])
    return doc


def main():
    global PROFDATA, LLVMCOV
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--binary", required=True, help="the instrumented cedar-drt-coverage replay binary (one for all)")
    ap.add_argument("--manifest", default=None, help="manifest.json — labels approaches guided vs specimen for the diff")
    ap.add_argument("--reps", type=int, default=20)
    ap.add_argument("--snapshots", type=int, default=20)
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) - 1))
    ap.add_argument("--replay-shards", type=int, default=1,
                    help="split each rep's replay into N contiguous batch-shards run in "
                         "parallel across the box's cores (profraw-merged back per rep). "
                         "N>1 turns the ~single-threaded per-rep replay into an all-cores job.")
    ap.add_argument("--s3-bucket", default=None, help="upload results to S3; (replay mode) stream corpus from S3")
    ap.add_argument("--s3-root", default=None, help="S3 root prefix (with --s3-bucket)")
    ap.add_argument("--from-collect", action="store_true",
                    help="legacy: use collect's inline profraw instead of replaying the corpus")
    args = ap.parse_args()
    PROFDATA, LLVMCOV = find_llvm_tools()

    # UNIFIED: every approach's coverage comes from REPLAYING its streamed corpus through the
    # one instrumented binary (reset-once cumulative). The manifest is used ONLY to label
    # which approaches are guided (the "handwritten" side) vs specimen for the cross-approach
    # diff — not to pick a binary or mode (all identical now).
    guided_names, fused_names = set(), set()
    if args.manifest and os.path.isfile(args.manifest):
        with open(args.manifest) as f:
            man = json.load(f)
        for e in man.get("approaches", []):
            (guided_names if e.get("guided") else fused_names).add(e["name"])
        approaches = sorted(guided_names | fused_names)
    elif args.s3_bucket:
        out = subprocess.run(["aws", "s3", "ls", f"s3://{args.s3_bucket}/{args.s3_root}/"],
                             stdout=subprocess.PIPE).stdout.decode()
        approaches = sorted(l.split()[-1].rstrip("/") for l in out.splitlines()
                            if l.strip().startswith("PRE") and "results" not in l)
        fused_names.update(approaches)
    else:
        approaches = sorted(d for d in os.listdir(args.root)
                            if os.path.isdir(os.path.join(args.root, d, "collect")))
        fused_names.update(approaches)

    print("approaches:", approaches, "| guided:", sorted(guided_names), "| specimen:", sorted(fused_names))

    keep_dir = tempfile.mkdtemp(prefix="cov_finals_")
    per_approach_sets, summary_totals, approach_merged = {}, {}, {}
    shards = max(1, args.replay_shards)
    rep_results = {a: [] for a in approaches}
    try:
        if args.from_collect or shards == 1:
            # NON-SHARDED per-rep path: one process per rep. With --from-collect, reuse collect's
            # inline snapshots (fused). With --replay-shards 1 (and NOT --from-collect), REPLAY each
            # rep's WHOLE corpus in ONE process streamed once from S3, taking intra-process snapshots
            # (REPLAY_SNAPSHOTS) for the over-time curve. This avoids the concurrent per-shard S3
            # streaming that silently kills shards on the guided corpus (contiguous shards die ->
            # covIdxMax truncated -> curve ends early). Reliable single stream + real snapshot curve.
            fc = args.from_collect
            for approach in approaches:
                with ThreadPoolExecutor(max_workers=args.jobs) as ex:
                    futs = [ex.submit(process_rep, args.root, approach, r, args.snapshots,
                                      args.s3_bucket, args.s3_root, keep_dir, fc, args.binary)
                            for r in range(args.reps)]
                    for r in (f.result() for f in futs):
                        if not r:
                            continue
                        fp = r.get("final_profraw")
                        if fp and os.path.exists(fp):
                            pd = fp + ".pd"; merge([fp], pd); os.remove(fp)
                            rep_results[approach].append(
                                {"rep": r["rep"], "final_profdata": pd, "final_covered": r["final_covered"]})
        else:
            # PRIMARY: flatten EVERY (approach, rep, shard) into ONE pool so the whole box
            # saturates (not just ~reps cores). Each shard replays a contiguous ~1/N slice of
            # a rep's corpus in its own process; results regroup per (approach, rep) and
            # `assemble_rep` merges the shards (union = final; cumulative = over-time curve).
            tasks = [(a, r, s) for a in approaches for r in range(args.reps) for s in range(shards)]
            print(f"replaying {len(tasks)} shard-units "
                  f"({len(approaches)} approaches x {args.reps} reps x {shards} shards) on {args.jobs} workers")
            shard_out = {}
            with ThreadPoolExecutor(max_workers=args.jobs) as ex:
                futs = {ex.submit(replay_one_shard, a, r, s, shards, args.s3_bucket, args.s3_root,
                                  args.root, args.binary, keep_dir): (a, r) for (a, r, s) in tasks}
                for f in futs:
                    a, r = futs[f]
                    shard_out.setdefault((a, r), []).append(f.result())
            for (a, r), sresults in shard_out.items():
                rep = assemble_rep(a, r, sresults, args.root, args.binary, keep_dir)
                if rep:
                    rep_results[a].append(rep)

        for approach in approaches:
            results = sorted(rep_results.get(approach, []), key=lambda x: x["rep"])
            if not results:
                print(f"  {approach}: no reps"); continue
            # Incremental merge across reps: never hold more than the running profdata + one
            # rep final. Delete each rep's final profdata right after folding it in (no pile-up).
            merged = os.path.join(keep_dir, f"{approach}_merged.profdata")
            have = False
            for r in results:
                fp = r.get("final_profdata")
                if not fp or not os.path.exists(fp):
                    continue
                if have:
                    merge([merged, fp], merged + ".tmp"); os.replace(merged + ".tmp", merged)
                else:
                    merge([fp], merged); have = True
                os.remove(fp)
            if not have:
                print(f"  {approach}: no coverage profraw"); continue
            approach_merged[approach] = merged
            per_approach_sets[approach] = covered_line_set_by_function(merged, args.binary)
            summary_totals[approach] = covered_lines_total(merged, args.binary)
            print(f"  {approach}: {len(results)} reps, union covered lines = {summary_totals[approach]}")
            for r in results:  # stamp per-rep into analyze json (for bootstrap_ci)
                p = os.path.join(args.root, approach, "analyze", f"rep_{r['rep']:02d}.json")
                if os.path.exists(p):
                    with open(p) as f: rec = json.load(f)
                    rec["source_lines_covered"] = r["final_covered"]
                    with open(p, "w") as f: json.dump(rec, f, indent=2)
                    if args.s3_bucket:
                        s3_cp(p, f"s3://{args.s3_bucket}/{args.s3_root}/{approach}/analyze/rep_{r['rep']:02d}.json")

        doc = compare(per_approach_sets, summary_totals, guided_names)

        # Per-file covered/total region-lines for the coverage TREEMAP (what our testing
        # leaves uncovered, mapped over the program). Compute for the specimen union and the
        # guided union separately (merging each side's per-approach profdata), so the treemap
        # can show "gaps our best generators leave" vs the guided baseline. Modules distinguish
        # in-scope validator code from out-of-scope crate code (auth/eval/parse).
        def union_profdata(names, tag):
            ms = [approach_merged[a] for a in names if a in approach_merged]
            if not ms:
                return None
            out = os.path.join(keep_dir, f"union_{tag}.profdata")
            if len(ms) == 1:
                merge([ms[0]], out)
            else:
                merge(ms, out)
            return out
        coverage_map = {}
        specimen = [a for a in approaches if a not in guided_names]
        guided = [a for a in approaches if a in guided_names]
        spec_up = union_profdata(specimen, "specimen_union")
        hw_up = union_profdata(guided, "handwritten_union")
        for tag, up in (("specimen_union", spec_up), ("handwritten_union", hw_up)):
            if up:
                try:
                    coverage_map[tag] = file_coverage(up, args.binary)
                except subprocess.CalledProcessError:
                    pass
        doc["coverage_map"] = coverage_map
        # Differential map: what specimen vs handwritten each cover UNIQUELY, per file.
        if spec_up and hw_up:
            try:
                doc["diff_map"] = diff_map_of(spec_up, hw_up, args.binary)
            except subprocess.CalledProcessError:
                pass

        out_local = os.path.join(args.root, "coverage_compare.json")
        os.makedirs(args.root, exist_ok=True)
        with open(out_local, "w") as f:
            json.dump(doc, f, indent=2)
        if args.s3_bucket:
            s3_cp(out_local, f"s3://{args.s3_bucket}/{args.s3_root}/results/coverage_compare.json")
        print("wrote", out_local)
    finally:
        shutil.rmtree(keep_dir, ignore_errors=True)


if __name__ == "__main__":
    main()

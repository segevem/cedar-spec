# Experiment scripts

Multi-run generator-comparison experiments with **bootstrap confidence
intervals around the median**. Compares Specimen-derived generators (via the
Lean FFI) against the handwritten ABAC generator on a coverage target.

## Files

| file | role |
|---|---|
| `run_experiment.sh` | end-to-end driver: throughput → collect `REPS` reps in parallel → analyze → CI + plots |
| `bootstrap_ci.py`   | percentile bootstrap 95% CI around the median, per approach/metric → `bootstrap_ci.json` + table |
| `plot_ci.py`        | median + CI error-bar comparison across approaches → `bootstrap_ci.png` |
| `plot_over_time.py` | coverage-over-time with median + bootstrap CI band across reps |

## Prerequisites

```bash
# Lean static libs (needed after any change to CedarGen / the generators):
cd ../../cedar-lean
../cedar-drt/build_lean_lib.sh
lake build CedarGen:static          # build_lean_lib.sh omits this one

# The experiment binary (lean-gen + s3 features):
cd ../cedar-drt/coverage
source ../set_env_vars.sh
cargo build --release --features lean-gen,s3
```

## Run

```bash
# defaults: 5 reps, validation-drt, S3 storage, 5-min throughput to size N
./experiment_scripts/run_experiment.sh

# 10 reps per approach, fixed N, local storage, offline:
REPS=10 STORAGE=local VALID_COUNT=3000 ./experiment_scripts/run_experiment.sh
```

### Settings (environment variables)

| var | default | meaning |
|---|---|---|
| `REPS` | 5 | **runs per approach** — the bootstrap sample size |
| `TARGET` | `validation-drt` | `validation-drt` \| `rust-only` \| `level-validation-drt` |
| `VALID_COUNT` | *(unset)* | fixed N per rep; if unset, N is sized per-approach from a throughput run |
| `DURATION` | 300 | throughput seconds used to size N (when `VALID_COUNT` unset) |
| `SEED_BASE` | 0 | master seed; rep *i* uses `SEED_BASE + i*SEED_STRIDE` |
| `SEED_STRIDE` | 1000000 | spacing between rep seeds (must exceed max N so rep corpora are disjoint) |
| `STORAGE` | `s3` | `s3` \| `local` |
| `BUCKET` / `S3ROOT` | `__S3_BUCKET__` / `typecheck-ci-<tag>` | S3 destination |
| `OUT` | `../exp_ci_results` | local output root |
| `MAX_PARALLEL` | `nproc-1` | max concurrent jobs |
| `CPU_PIN` | 1 | pin each job to a rotating core with `taskset` |
| `BOOTSTRAP` | 10000 | bootstrap resamples |
| `APPROACHES_SET` + `APPROACHES` | *(built-in list)* | override the approach list; each entry is `"name generator strategy lean_size"` |

## Output layout

```
$OUT/
  manifest.json                 # settings + per-rep seeds + git commit (reproducibility)
  bootstrap_ci.json             # median + 95% CI per approach/metric
  bootstrap_ci.png              # CI comparison plot
  over_time_*.png               # coverage-over-time bands (run plot_over_time.py)
  <approach>/
    throughput/rep_00.json      # N sizing (time mode)
    collect/rep_NN/             # per-rep corpus + metadata (local storage)
    analyze/rep_NN.json         # per-rep metrics (3-paths, unique, skeletons, …)
```

## How a run flows

1. **Throughput (distinct):** per approach, a short run measures the generation
   rate → sets `N = rate × RUN_SECS`. This is the *only* source of counts.
2. **Collect = analysis (inline, pipelined):** each rep generates N inputs,
   streams the corpus to S3, **and computes the full `AnalyzeResult` in one pass**
   (unique inputs/skeletons, k-paths, diversity-over-time), writing
   `analyze/rep_NN.json` as it finishes. No replay, no collect→analyze barrier —
   reps/approaches complete independently.
3. **Bootstrap:** reads the per-rep JSONs → median + 95% CI.

`REPLAY_ANALYZE=1` re-runs the heavy replay analysis from the saved corpus (for
source coverage / different k); off by default since collect already produced it.

### Reproducibility & DRT bugs

- Each rep starts at a distinct SplitMix-diffused seed → reps are independent and
  a rep is exactly reproducible from its `start_seed`. Per-input repro uses the
  `provenance` (`base_seed`, `index`) recorded in `per_input.jsonl` — not the
  meaningless attempt counter.
- On a Rust/Lean **DRT mismatch** the target returns a violation (no crash). The
  harness captures a repro — schema + policy proto (round-trippable) + Cedar text
  + provenance — to `collect/rep_NN/violations/` and **streams it to
  `s3://…/rep_NN/violations/` immediately** (survives interruption). Default is
  continue-and-log; set `ON_VIOLATION=stop` to halt the rep at the first mismatch.
  Violation counts appear in each rep's `metadata.json`.

## Modifying an experiment

One config file (`configs/example.conf`, copy it) drives the local driver *and*
both EC2 scripts — pass it with `CONFIG=`. Precedence is **env > config > script
default**, so a one-off `REPS=8 CONFIG=...` still wins.

- **Change what's run:** edit the `APPROACHES` array in the config — each line is
  `name  generator  strategy  lean_size`. `generator` is `type-directed`
  (handwritten) or `lean-schema-typeof` (Specimen); `strategy` is the Specimen
  variant (`budget-aware`/`steep`/`steep-tags`/`typeof-check`). Add/remove sizes
  or strategies freely; the instance auto-sizes to the new job count.
- **Change run length / reps:** `RUN_SECS` (1h=3600, 12h=43200) and `REPS`.
- **Change the spec version:** point `CEDAR_SPEC_DIR` (and/or `SPECIMEN_DIR`,
  `CEDAR_DIR`) at a different checkout or **git worktree**. `package_and_upload.sh`
  snapshots exactly those dirs — including uncommitted edits — into the required
  `specimen/ + cedar-spec/ + cedar/` layout, so you can compare spec versions by
  packaging each and launching with a distinct `S3ROOT`.
- **Add a brand-new Specimen variant:** that's code — add the variant file under
  `CedarGen/Relational/Variants/`, wire it into `dispatchGenerate`/`listStrategies`
  in `CedarFFI/Generate.lean`, then reference its strategy name in `APPROACHES`.

```bash
cp configs/example.conf configs/my.conf   # edit approaches / RUN_SECS / spec dirs
CONFIG=configs/my.conf ./run_experiment.sh                    # local
CONFIG=configs/my.conf aws/package_and_upload.sh              # snapshot that version
CONFIG=configs/my.conf CONFIRM=1 aws/launch.sh                # EC2
```

## Running on EC2 (long / high-rep runs)

For hour- and 12-hour-scale runs the grid is `REPS × approaches` independent
single-core jobs, so a big on-demand instance runs them all in **one wave**
(total wall-clock ≈ the run length, not a multiple). The `aws/` scripts do this
end to end; the instance builds the *local* code — including uncommitted changes
and the patched Specimen fork — from a source tarball.

```bash
cd experiment_scripts/aws
# 1. snapshot local specimen + cedar-spec + cedar -> S3
./package_and_upload.sh
# 2. review the plan (dry run: prints instance sizing, cost surface, S3 paths)
REPS=20 RUN_SECS=43200 ./launch.sh
# 3. launch for real (creates IAM role if absent, launches on-demand, pauses when done)
REPS=20 RUN_SECS=43200 CONFIRM=1 ./launch.sh
```

`launch.sh` auto-sizes the instance so vCPU ≥ (reps × approaches). Results —
`bootstrap_ci.json/png` and logs — land at `s3://<bucket>/<S3ROOT>/results/`;
corpora stream to `…/<approach>/rep_NN/` during the run. `RUN_SECS` sizes N per
approach from the throughput rate (throughput itself stays short at `DURATION`).
Watch progress via SSM Session Manager (`aws ssm start-session --target <id>`,
then `tail -f /var/log/cedar-exp.log`). Re-`package_and_upload.sh` after any
local code change before relaunching.

Files: `package_and_upload.sh` (tarball → S3), `launch.sh` (IAM + sized on-demand
launch, dry-run unless `CONFIRM=1`), `user_data_body.sh` (instance bootstrap:
build → run → upload → terminate), `approaches.default.txt` (approach list),
`run_on.sh` (fire another run on a warm instance — see below).

### Reusing a warm instance (skip the rebuild)

On finish the instance **pauses (stops)** by default (`ON_FINISH=stop`), keeping
its built EBS volume so you can reuse it without the ~15-min rebuild. Options:
`ON_FINISH=terminate` (destroy) or `keep` (leave running). To iterate:

```bash
# launch; it pauses when the first run finishes:
REPS=20 RUN_SECS=3600 CONFIRM=1 ./launch.sh                     # note the instance id
# later: resume the paused instance and fire another run (no rebuild):
aws ec2 start-instances --region us-east-1 --instance-ids i-abc
INSTANCE_ID=i-abc REPS=20 RUN_SECS=43200 ./run_on.sh           # new run
INSTANCE_ID=i-abc CONFIG=configs/other.conf ./run_on.sh        # another
# done for good:
aws ec2 terminate-instances --region us-east-1 --instance-ids i-abc
```

**Each run lands in its own bucket portion.** `launch.sh`/`run_on.sh` default
`S3ROOT` to a timestamped name, and everything (corpora, results, the
on-instance work dir) is namespaced under it — so repeated runs never overwrite.
Override `S3ROOT=<name>` for a stable name, but don't reuse one across runs.

Changing the *spec version* still needs a rebuild (re-`package_and_upload.sh` +
fresh `launch.sh`); changing approaches / reps / run length on the same spec does
not — `run_on.sh` just reruns the driver.

## Why the reps are independent (and the CI is honest)

Each rep starts the generator at a distinct seed (`SEED_BASE + i*SEED_STRIDE`),
and `SEED_STRIDE ≫ N` guarantees the reps' seed ranges are disjoint. Crucially,
the Lean generator passes every seed through a **SplitMix64 diffuser**
(`scrambleSeed` in `CedarGen/Relational/TypeOfLeanBase.lean`) before it reaches
`mkStdGen` — otherwise contiguous integer seeds map to nearly-identical RNG
states (`mkStdGen s = ⟨s+1,1⟩` for small `s`) and would produce structurally
correlated policies, collapsing the CI. With diffusion, each rep is an
independent sample, so the between-run spread reflects real generator variance.
The handwritten generator uses `SmallRng::seed_from_u64`, which already
SplitMix-expands its seed.

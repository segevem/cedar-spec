#!/bin/bash
#
# EC2 user-data BODY (Amazon Linux 2023). launch.sh prepends an exports block
# (REPS, RUN_SECS, TARGET, BUCKET, S3ROOT, SRC_PREFIX, RESULTS_PREFIX, DURATION,
# SEED_BASE, SEED_STRIDE, BOOTSTRAP, ON_FINISH, and writes APPROACHES to
# $WORK/approaches.txt) before this body. Runs as root at first boot.
#
# Flow: install toolchains -> fetch src tarball from S3 -> build Lean static
# libs + coverage binary -> run the multi-rep experiment (streams corpora to
# S3) -> upload results/logs to S3 -> terminate the instance.
set -uo pipefail
exec > >(tee -a /var/log/cedar-exp.log) 2>&1
echo "===== cedar-exp bootstrap $(date -u +%FT%TZ) ====="

WORK=/opt/exp
mkdir -p "$WORK"; cd "$WORK"
export HOME=/root
export CARGO_HOME=/root/.cargo RUSTUP_HOME=/root/.rustup ELAN_HOME=/root/.elan
export PATH="$CARGO_HOME/bin:$ELAN_HOME/bin:$WORK/protoc/bin:$PATH"

REGION="$(curl -s -H "X-aws-ec2-metadata-token: $(curl -s -X PUT http://169.254.169.254/latest/api/token -H 'X-aws-ec2-metadata-token-ttl-seconds: 300')" http://169.254.169.254/latest/meta-data/placement/region)"
IID="$(curl -s -H "X-aws-ec2-metadata-token: $(curl -s -X PUT http://169.254.169.254/latest/api/token -H 'X-aws-ec2-metadata-token-ttl-seconds: 300')" http://169.254.169.254/latest/meta-data/instance-id)"

# GUIDED run iff any approach has a 5th column (a cargo-fuzz target name). Guided runs
# need nightly + cargo-fuzz (to build/run the sancov targets) and the instrumented
# cedar-drt-coverage REPLAY binary (coverage comes from replaying the streamed corpus,
# not fused into collect). approaches.txt was written by launch.sh's prepended block.
GUIDED_RUN=0; FUSED_RUN=0
if [[ -f "$WORK/approaches.txt" ]]; then
  awk 'NF>=5 && $1!~/^#/{f=1} END{exit !f}' "$WORK/approaches.txt" && GUIDED_RUN=1
  awk 'NF>=1 && NF<5 && $1!~/^#/{f=1} END{exit !f}' "$WORK/approaches.txt" && FUSED_RUN=1
fi
echo "GUIDED_RUN=$GUIDED_RUN FUSED_RUN=$FUSED_RUN"

on_finish() {
  echo "===== done $(date -u +%FT%TZ); uploading logs ====="
  aws s3 cp /var/log/cedar-exp.log "s3://$BUCKET/$RESULTS_PREFIX/bootstrap.log" || true
  case "${ON_FINISH:-stop}" in
    terminate) aws ec2 terminate-instances --region "$REGION" --instance-ids "$IID" || shutdown -h now ;;
    keep)      echo "ON_FINISH=keep: leaving instance running" ;;
    stop|*)    echo "ON_FINISH=stop: pausing instance (built state preserved for reuse)"
               aws ec2 stop-instances --region "$REGION" --instance-ids "$IID" || shutdown -h now ;;
  esac
}
trap on_finish EXIT

# All toolchain installs below are IDEMPOTENT — each is skipped if already present, so the
# SAME user-data works on a bare Amazon Linux 2023 AMI (installs everything) AND on a GOLDEN
# AMI that baked the toolchains (skips it all, saving ~10-13 min). Build a golden AMI with
# aws/make_base_ami.sh; point launch.sh at it via AMI_ID.
echo "--- system packages ---"
if command -v git >/dev/null && command -v clang >/dev/null && command -v unzip >/dev/null && command -v python3 >/dev/null; then
  echo "  present; skipping dnf"
else
  dnf -y install git clang gcc gcc-c++ make wget tar xz unzip python3 python3-pip
fi

echo "--- python deps for CI + plots ---"
if python3 -c "import numpy, scipy, matplotlib, squarify" 2>/dev/null; then
  echo "  present; skipping pip"
else
  python3 -m pip install --quiet numpy scipy matplotlib squarify
fi

echo "--- rust ---"
if command -v cargo >/dev/null; then
  echo "  present; skipping rustup install"
else
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable
fi
rustup component add rust-src >/dev/null 2>&1 || true
# llvm-cov / llvm-profdata for the line-coverage analysis.
rustup component add llvm-tools-preview >/dev/null 2>&1 || true
# rustfilt (rustc-demangle) — plot_coverage_compare.py demangles the raw v0 symbols in
# coverage_compare.json at plot time; without it the by-function labels stay mangled.
command -v rustfilt >/dev/null || cargo install rustfilt >/dev/null 2>&1 || echo "WARN: cargo install rustfilt failed (coverage_compare labels will be mangled)"

# Guided runs build/run cargo-fuzz sancov targets, which require the nightly toolchain
# (for -Cpasses=sancov-module) and the cargo-fuzz subcommand.
if [[ "$GUIDED_RUN" == "1" ]]; then
  echo "--- nightly + cargo-fuzz (guided) ---"
  rustup toolchain list 2>/dev/null | grep -q nightly || rustup toolchain install nightly --profile minimal >/dev/null 2>&1 || true
  rustup component add rust-src --toolchain nightly >/dev/null 2>&1 || true
  rustup component add llvm-tools-preview --toolchain nightly >/dev/null 2>&1 || true
  if command -v cargo-fuzz >/dev/null; then
    echo "  cargo-fuzz present; skipping cargo install"
  else
    cargo install cargo-fuzz >/dev/null 2>&1 || echo "WARN: cargo install cargo-fuzz failed"
  fi
fi

echo "--- lean (elan) ---"
if command -v elan >/dev/null || command -v lean >/dev/null; then
  echo "  present; skipping elan install"
else
  wget -q https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -O /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y --default-toolchain none
fi

echo "--- protoc ---"
if command -v protoc >/dev/null || [[ -x "$WORK/protoc/bin/protoc" ]]; then
  echo "  present; skipping protoc download"
else
  wget -q https://github.com/protocolbuffers/protobuf/releases/download/v29.0/protoc-29.0-linux-x86_64.zip -O /tmp/protoc.zip
  mkdir -p "$WORK/protoc"; unzip -oq /tmp/protoc.zip -d "$WORK/protoc"
fi

echo "--- fetch source tarball ---"
aws s3 cp "s3://$BUCKET/$SRC_PREFIX/src.tgz" "$WORK/src.tgz"
tar xzf "$WORK/src.tgz" -C "$WORK"
ls -la "$WORK"

CEDAR_SPEC="$WORK/cedar-spec"
echo "--- build Lean static libs (incl CedarGen + all dep static libs) ---"
cd "$CEDAR_SPEC/cedar-lean"
elan toolchain install "$(cat lean-toolchain)" || true
# Prebuilt Lean cache (optional, uploaded by package_and_upload.sh LEAN_CACHE=1): extract
# cedar-lean/.lake so the `lake build` below is a fast VERIFY instead of a ~15-min compile.
# lake re-checks source hashes and rebuilds only anything stale, so a mismatched/absent
# cache is safe — it just falls back to a full build. tar preserves mtimes so unchanged
# sources stay "up-to-date".
# The cache is rooted at $WORK: it lands cedar-spec/cedar-lean/.lake AND specimen/.lake
# (Specimen is a path dep built in its own .lake — libspecimen_Specimen.a lives there).
if aws s3 cp "s3://$BUCKET/$SRC_PREFIX/lean_cache.tgz" "$WORK/lean_cache.tgz" 2>/dev/null; then
  echo "--- extracting prebuilt Lean cache ($(du -h "$WORK/lean_cache.tgz" | cut -f1)) ---"
  tar xzf "$WORK/lean_cache.tgz" -C "$WORK" || echo "WARN: Lean cache extract failed; full build"
  rm -f "$WORK/lean_cache.tgz"
  # Stamp the cached build artifacts NEWER than the extracted sources so `lake` treats them
  # as up-to-date (the cache was built from the SAME shipped sources, so this is safe) —
  # avoids spurious rebuilds from tar/extraction mtime skew. `lake build` below still runs,
  # so any genuine content drift is caught and rebuilt.
  find "$CEDAR_SPEC/cedar-lean/.lake" "$WORK/specimen/.lake" -exec touch {} + 2>/dev/null || true
  echo "  cached static libs present: $(find "$CEDAR_SPEC/cedar-lean/.lake" "$WORK/specimen/.lake" -name '*.a' 2>/dev/null | wc -l)"
else
  echo "--- no Lean cache in S3; full lake build ---"
fi
lake update
# cedar-lean-ffi (build.rs + #[link]) links the Cedar_* libs AND the dependency
# static libs specimen_Specimen / plausible_Plausible / proofwidgets_ProofWidgets
# / batteries_Batteries. `:static` builds only the named lib, not its deps, so
# every dep lib the FFI links must be built explicitly here.
lake build Cedar:static Protobuf:static CedarProto:static Cedar.SymCC:static \
           CedarFFI:static CedarGen:static \
           Batteries:static Plausible:static ProofWidgets:static Specimen:static

echo "--- lean env vars ---"
source "$CEDAR_SPEC/cedar-drt/set_env_vars.sh"

# A symcc-* target needs the `symcc` feature in BOTH binaries (cedar-experiment runs the
# SymccTermDrt oracle during the throughput probe; cedar-drt-coverage runs it on replay).
PHASE1_FEATURES="lean-gen,s3"
DRTCOV_FEATURES="profraw,s3,lean-gen"
if [[ "${TARGET:-}" == symcc-* ]]; then
  PHASE1_FEATURES="$PHASE1_FEATURES,symcc"
  DRTCOV_FEATURES="$DRTCOV_FEATURES,symcc"
  # Measure the symbolic COMPILER, not the validator: instrument ONLY cedar_policy_symcc (+ the
  # cedar_drt_coverage bin, for the __llvm_profile_* runtime link) — so validator crates
  # (cedar_policy_core / cedar_policy) are not instrumented and produce NO coverage at all.
  # The analyze filter then KEEPS cedar-policy-symcc and EXPLICITLY drops the validator crates
  # (cedar-policy-core, cedar-policy-validator) plus harness/deps — belt-and-suspenders so the
  # validator is excluded both at instrumentation and reporting. `cedar-policy-symcc` is kept
  # because the ignore terms use `cedar-policy-core`/`-validator` (not a bare `cedar-policy`).
  # Exported so both the instrumented build below AND the run_experiment.sh analyze inherit them.
  export INSTRUMENT_CRATES="cedar_policy_symcc cedar_drt_coverage"
  export COVERAGE_IGNORE_REGEX='/\.cargo/registry|/rustc/|/tests/|/test/|_test\.rs|/test\.rs|/kpath|cedar-policy-generators|cedar-drt|cedar-lean-ffi|cedar-policy-core|cedar-policy-validator'
fi

echo "--- build Phase-1 (throughput) binary: uninstrumented ($PHASE1_FEATURES) ---"
cd "$CEDAR_SPEC/cedar-drt/coverage"
cargo build --release --features "$PHASE1_FEATURES"

if [[ "$GUIDED_RUN" == "1" ]]; then
  # Guided: build the sancov cargo-fuzz targets referenced by the approaches, so the
  # timed throughput probe (Phase 1) doesn't pay the compile. Build every distinct
  # 5th-column target. These link the Lean FFI (env vars sourced above).
  echo "--- build guided cargo-fuzz targets ---"
  for ft in $(awk 'NF>=5 && $1!~/^#/{print $5}' "$WORK/approaches.txt" | sort -u); do
    echo "    cargo fuzz build -s none $ft"
    ( cd "$CEDAR_SPEC/cedar-drt/fuzz" && cargo +nightly fuzz build -s none "$ft" ) \
      || echo "WARN: cargo fuzz build failed for $ft"
  done
fi
if [[ "${SOURCE_COV:-1}" == "1" ]]; then
  # UNIFIED coverage replay binary (both specimen + guided): instrument-coverage
  # `cedar-drt-coverage` with lean-gen, so the replay drives the ACTUAL ValidationDrt
  # target (Rust validate + Lean FFI + compare) with reset-once cumulative counters.
  # This is the ONLY instrumented binary needed — collect is always uninstrumented ($BIN).
  # Instrument ONLY the cedar-policy crates (RUSTC_WRAPPER), not the generators/FFI/harness:
  # small counter array + instrument overhead confined to the code under test.
  echo "--- build coverage replay binary cedar-drt-coverage (cedar-only instrumentation, lean-gen, target_cov) ---"
  RUSTC_WRAPPER="$CEDAR_SPEC/cedar-drt/coverage/experiment_scripts/instrument_cedar_only.sh" \
    cargo build --release --bin cedar-drt-coverage \
    --features "$DRTCOV_FEATURES" --target-dir target_cov \
    || echo "WARN: instrumented replay build failed; coverage will be skipped"
fi

echo "===== running experiment ($(date -u +%FT%TZ)) ====="
# The box authenticates via its instance role; there is no named AWS profile here,
# so tell run_experiment.sh to use the default credential chain (not cedar-experiment).
export USE_INSTANCE_ROLE=1
export STORAGE=s3 BUCKET S3ROOT
export OUT="$CEDAR_SPEC/cedar-drt/coverage/exp_ci_results"
export APPROACHES_FILE="$WORK/approaches.txt"
export MAX_PARALLEL="${MAX_PARALLEL:-$(( $(nproc) - 1 ))}"
bash "$CEDAR_SPEC/cedar-drt/coverage/experiment_scripts/run_experiment.sh" || echo "run_experiment.sh returned $?"

echo "--- upload results to S3 ---"
aws s3 cp --recursive "$OUT" "s3://$BUCKET/$RESULTS_PREFIX/" \
  --exclude "*/collect/*" || true    # corpora already streamed; skip re-upload
echo "===== experiment complete ====="

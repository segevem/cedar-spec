#!/bin/bash
#
# Fire a NEW experiment run on an already-built, warm instance (one launched with
# SELF_TERMINATE=0) — reusing the compiled binary + Lean libs, no rebuild, no
# teardown. Streams corpora to S3 and uploads results, just like the boot run.
#
# Usage:
#   INSTANCE_ID=i-abc REPS=20 RUN_SECS=43200 S3ROOT=big-run ./run_on.sh
#   INSTANCE_ID=i-abc CONFIG=configs/my.conf ./run_on.sh
#
# The instance keeps running afterward. Pause billing between runs with:
#   aws ec2 stop-instances  --region us-east-1 --instance-ids i-abc   # keeps EBS
#   aws ec2 start-instances --region us-east-1 --instance-ids i-abc   # resume
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export AWS_PROFILE="${AWS_PROFILE:-cedar-experiment}"
REGION="${REGION:-us-east-1}"
CONFIG="${CONFIG:-}"
[[ -n "$CONFIG" && -f "$CONFIG" ]] && source "$CONFIG"

IID="${INSTANCE_ID:-${1:-}}"
[[ -n "$IID" ]] || { echo "ERROR: set INSTANCE_ID=i-... (or pass as arg 1)" >&2; exit 1; }

REPS="${REPS:-20}"; RUN_SECS="${RUN_SECS:-3600}"; DURATION="${DURATION:-$RUN_SECS}"
TARGET="${TARGET:-validation-drt}"; SEED_BASE="${SEED_BASE:-0}"
SEED_STRIDE="${SEED_STRIDE:-1000000000}"; BOOTSTRAP="${BOOTSTRAP:-10000}"
BUCKET="${BUCKET:-__S3_BUCKET__}"
# Default S3ROOT is timestamped so repeated runs on the same warm instance land
# in DISTINCT bucket portions (never overwrite). Override for a stable name, but
# don't reuse a name across runs.
S3ROOT="${S3ROOT:-warm-run-${REPS}reps-${RUN_SECS}s-$(date -u +%Y%m%dT%H%M%SZ)}"
RESULTS_PREFIX="${RESULTS_PREFIX:-$S3ROOT/results}"
ON_FINISH="${ON_FINISH:-keep}"   # keep (default, iterate) | stop (pause) | terminate

# Approaches: inline array from CONFIG, else the default file.
APPROACHES_FILE="${APPROACHES_FILE:-$SCRIPT_DIR/approaches.default.txt}"
if [[ -n "${APPROACHES_SET:-}" && "${#APPROACHES[@]}" -gt 0 ]]; then
  APP_LINES="$(printf '%s\n' "${APPROACHES[@]}")"
else
  APP_LINES="$(grep -vE '^[[:space:]]*(#|$)' "$APPROACHES_FILE")"
fi

echo "Firing run '$S3ROOT' on $IID (reps=$REPS run_secs=$RUN_SECS target=$TARGET)…"

# Remote script: source env, write approaches, run in background (nohup), upload.
REMOTE=$(cat <<REMOTE_EOF
set -uo pipefail
export HOME=/root CARGO_HOME=/root/.cargo RUSTUP_HOME=/root/.rustup ELAN_HOME=/root/.elan
export PATH="/root/.cargo/bin:/root/.elan/bin:/opt/exp/protoc/bin:\$PATH"
SPEC=/opt/exp/cedar-spec
[[ -x \$SPEC/cedar-drt/coverage/target/release/cedar-experiment ]] || { echo "binary missing — instance not built?"; exit 1; }
cd \$SPEC/cedar-lean && source \$SPEC/cedar-drt/set_env_vars.sh
mkdir -p /opt/exp/runs/$S3ROOT
cat > /opt/exp/runs/$S3ROOT/approaches.txt <<'APP_EOF'
$APP_LINES
APP_EOF
cd \$SPEC/cedar-drt/coverage
# The box authenticates via its instance role — no named AWS profile — so tell
# run_experiment.sh to use the default credential chain (else it forces the missing
# cedar-experiment profile and every S3 call fails).
export USE_INSTANCE_ROLE=1
export STORAGE=s3 BUCKET=$BUCKET S3ROOT=$S3ROOT TARGET=$TARGET
export REPS=$REPS RUN_SECS=$RUN_SECS DURATION=$DURATION SEED_BASE=$SEED_BASE
export SEED_STRIDE=$SEED_STRIDE BOOTSTRAP=$BOOTSTRAP
export APPROACHES_FILE=/opt/exp/runs/$S3ROOT/approaches.txt
export OUT=/opt/exp/runs/$S3ROOT/out
export MAX_PARALLEL=\$(( \$(nproc) - 1 ))
LOG=/var/log/cedar-exp-$S3ROOT.log
nohup bash -c '
  bash experiment_scripts/run_experiment.sh
  aws s3 cp --recursive "\$OUT" "s3://$BUCKET/$RESULTS_PREFIX/" --exclude "*/collect/*" || true
  aws s3 cp "'"\$LOG"'" "s3://$BUCKET/$RESULTS_PREFIX/run.log" || true
  case "$ON_FINISH" in
    terminate) aws ec2 terminate-instances --region $REGION --instance-ids $IID || true ;;
    stop)      aws ec2 stop-instances --region $REGION --instance-ids $IID || true ;;
  esac
' > "\$LOG" 2>&1 &
echo "started run $S3ROOT (pid \$!), logging to \$LOG"
REMOTE_EOF
)

# Ship the multi-line remote script base64-encoded as a SINGLE command that decodes +
# runs it. (Passing the raw script via `commands=[...]` shorthand keeps newlines as
# literal "\n" → syntax error on the box.)
REMOTE_B64="$(printf '%s' "$REMOTE" | base64 -w0)"
CID=$(aws ssm send-command --region "$REGION" --instance-ids "$IID" \
  --document-name AWS-RunShellScript --timeout-seconds 120 \
  --parameters "{\"commands\":[\"echo $REMOTE_B64 | base64 -d | bash\"]}" \
  --query 'Command.CommandId' --output text)
sleep 8
aws ssm get-command-invocation --region "$REGION" --command-id "$CID" --instance-id "$IID" \
  --query '{Status:Status,Out:StandardOutputContent,Err:StandardErrorContent}' --output text

cat <<EOF

Run '$S3ROOT' launched on $IID (background). It keeps running after this returns.
Watch:   aws ssm start-session --region $REGION --target $IID   # tail -f /var/log/cedar-exp-$S3ROOT.log
Results: s3://$BUCKET/$RESULTS_PREFIX/
Pause:   aws ec2 stop-instances --region $REGION --instance-ids $IID
EOF

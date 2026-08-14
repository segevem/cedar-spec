#!/bin/bash
#
# Configure + launch a single on-demand EC2 instance that builds the local code
# (via the S3 src tarball) and runs the multi-rep bootstrap-CI experiment,
# streaming results to S3 and self-terminating.
#
# Prereq: run ./package_and_upload.sh first (uploads src.tgz to S3).
#
# Everything is overridable by env var. With CONFIRM=1 it actually creates the
# IAM role (if missing) and launches; otherwise it prints the plan and exits
# (dry run) so you can review.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export AWS_PROFILE="${AWS_PROFILE:-cedar-experiment}"
REGION="${REGION:-us-east-1}"

# One config file drives run_experiment.sh, package_and_upload.sh, and this.
CONFIG="${CONFIG:-}"
[[ -n "$CONFIG" && -f "$CONFIG" ]] && { echo "sourcing config: $CONFIG"; source "$CONFIG"; }

# ---- experiment settings (passed into the instance) ----
REPS="${REPS:-20}"
RUN_SECS="${RUN_SECS:-3600}"            # 3600=1h, 43200=12h; sizes N via throughput rate
DURATION="${DURATION:-$RUN_SECS}"       # throughput window; defaults to RUN_SECS (== run length) for a
                                        #   representative rate. Override only to shorten it deliberately.
TARGET="${TARGET:-validation-drt}"
SEED_BASE="${SEED_BASE:-0}"
SEED_STRIDE="${SEED_STRIDE:-1000000000}"
BOOTSTRAP="${BOOTSTRAP:-10000}"
# Per-generate wall-clock timeout: a pathological seed (e.g. Specimen backtrackFuel
# exploding in CapMerge/TypeOfCheck) is logged as SLOW_SEED and skipped, and
# generation continues — one bad seed never aborts a rep. 50s: legitimate sz20
# batches (1 schema + 100 policies) were observed taking up to ~22s to generate, so
# the timeout must clear that tail (a lower value would false-skip real inputs).
GENERATE_TIMEOUT_SECS="${GENERATE_TIMEOUT_SECS:-50}"
BUCKET="${BUCKET:-__S3_BUCKET__}"
SRC_PREFIX="${SRC_PREFIX:-bootstrap}"
S3ROOT="${S3ROOT:-ci-run-${REPS}reps-${RUN_SECS}s-$(date -u +%Y%m%dT%H%M%SZ)}"
RESULTS_PREFIX="${RESULTS_PREFIX:-$S3ROOT/results}"
APPROACHES_FILE="${APPROACHES_FILE:-$SCRIPT_DIR/approaches.default.txt}"
# What the instance does when the run finishes:
#   stop      -> pause (keep the built EBS volume for warm reuse via run_on.sh) [default]
#   terminate -> destroy the instance
#   keep      -> leave it running
ON_FINISH="${ON_FINISH:-stop}"

# If the config defined an inline APPROACHES array, materialize it to a file so
# both the job-count sizing and the instance use the same list.
if [[ -n "${APPROACHES_SET:-}" && "${#APPROACHES[@]}" -gt 0 ]]; then
  APPROACHES_FILE="$(mktemp)"
  printf '%s\n' "${APPROACHES[@]}" > "$APPROACHES_FILE"
fi

# ---- infra settings ----
ROLE_NAME="${ROLE_NAME:-cedar-exp-runner}"
PROFILE_NAME="${PROFILE_NAME:-cedar-exp-runner}"
EBS_GB="${EBS_GB:-120}"
AMI_ID="${AMI_ID:-$(aws ssm get-parameter --region "$REGION" \
  --name /aws/service/ami-amazon-linux-latest/al2023-ami-kernel-default-x86_64 \
  --query 'Parameter.Value' --output text)}"

# ---- size the instance to the job count (one wave, no time-doubling) ----
# Both guided and fused now run TWO core-pinned processes per rep in true parallel
# (throughput probe ‖ count-matched collect), so they need 2 cores/rep — UNLESS a fixed
# VALID_COUNT is set (then no probe: 1 collect/rep).
NAPPROACH="$(grep -vcE '^[[:space:]]*(#|$)' "$APPROACHES_FILE")"
GUIDED_LAUNCH=0; FUSED_LAUNCH=0
awk 'NF>=5 && $1!~/^#/{f=1} END{exit !f}' "$APPROACHES_FILE" && GUIDED_LAUNCH=1
awk 'NF>=1 && NF<5 && $1!~/^#/{f=1} END{exit !f}' "$APPROACHES_FILE" && FUSED_LAUNCH=1
if (( GUIDED_LAUNCH == 1 && FUSED_LAUNCH == 1 )); then MODE_LABEL=MIXED
elif (( GUIDED_LAUNCH == 1 )); then MODE_LABEL=GUIDED
else MODE_LABEL=fused/specimen; fi
if [[ -n "${VALID_COUNT:-}" ]]; then
  PROCS_PER_REP=1
else
  PROCS_PER_REP=2
fi
JOBS=$(( NAPPROACH * REPS * PROCS_PER_REP ))
autosize() { # smallest c7i with vCPU >= JOBS
  for t in "8:c7i.2xlarge" "16:c7i.4xlarge" "32:c7i.8xlarge" "48:c7i.12xlarge" \
           "64:c7i.16xlarge" "96:c7i.24xlarge" "192:c7i.48xlarge"; do
    v="${t%%:*}"; name="${t#*:}"; [[ "$JOBS" -le "$v" ]] && { echo "$name"; return; }
  done
  echo "c7i.48xlarge"   # cap; >192 jobs -> shard across instances instead
}
INSTANCE_TYPE="${INSTANCE_TYPE:-$(autosize)}"
VCPU_OF() { case "$1" in *48xlarge)echo 192;; *24xlarge)echo 96;; *16xlarge)echo 64;; \
  *12xlarge)echo 48;; *8xlarge)echo 32;; *4xlarge)echo 16;; *2xlarge)echo 8;; *)echo 0;; esac; }

echo "=== launch plan ==="
cat <<EOF
  region          $REGION
  AMI             $AMI_ID  (Amazon Linux 2023)
  instance type   $INSTANCE_TYPE  (~$(VCPU_OF "$INSTANCE_TYPE") vCPU, on-demand)
  mode            ${MODE_LABEL}, ${PROCS_PER_REP} proc(s)/rep$([[ "$PROCS_PER_REP" == "2" ]] && echo " (throughput ‖ count-matched collect)")
  jobs            = $JOBS   -> want vCPU >= $JOBS  (${PROCS_PER_REP} x $NAPPROACH approaches x $REPS reps)
  EBS             ${EBS_GB} GiB gp3
  reps            $REPS
  run length      RUN_SECS=$RUN_SECS  (throughput DURATION=$DURATION)
  gen timeout     ${GENERATE_TIMEOUT_SECS}s per generate -> SLOW_SEED skip+log+continue (no abort)
  target          $TARGET
  approaches      $APPROACHES_FILE
  src             s3://$BUCKET/$SRC_PREFIX/src.tgz
  corpora ->      s3://$BUCKET/$S3ROOT/<approach>/rep_NN/
  results ->      s3://$BUCKET/$RESULTS_PREFIX/  (bootstrap_ci.json/png, logs)
  IAM role        $ROLE_NAME (S3 + Stop/TerminateInstances + SSM)
  on finish       $ON_FINISH   (stop = pause & keep built volume for reuse)
EOF

if [[ "${CONFIRM:-0}" != "1" ]]; then
  echo; echo "DRY RUN. Re-run with CONFIRM=1 to create the role and launch."; exit 0
fi

# ---- ensure src tarball exists ----
aws s3 ls "s3://$BUCKET/$SRC_PREFIX/src.tgz" >/dev/null 2>&1 || {
  echo "ERROR: src tarball missing. Run ./package_and_upload.sh first." >&2; exit 1; }

# ---- IAM role + instance profile (idempotent) ----
if ! aws iam get-role --role-name "$ROLE_NAME" >/dev/null 2>&1; then
  echo "Creating IAM role $ROLE_NAME…"
  aws iam create-role --role-name "$ROLE_NAME" --assume-role-policy-document '{
    "Version":"2012-10-17","Statement":[{"Effect":"Allow",
    "Principal":{"Service":"ec2.amazonaws.com"},"Action":"sts:AssumeRole"}]}' >/dev/null
  aws iam attach-role-policy --role-name "$ROLE_NAME" \
    --policy-arn arn:aws:iam::aws:policy/AmazonSSMManagedInstanceCore >/dev/null
fi
# Always (re)write the inline policy so existing roles pick up Stop/Terminate.
aws iam put-role-policy --role-name "$ROLE_NAME" --policy-name cedar-exp-inline \
  --policy-document "{
    \"Version\":\"2012-10-17\",\"Statement\":[
      {\"Effect\":\"Allow\",\"Action\":[\"s3:GetObject\",\"s3:PutObject\",\"s3:ListBucket\"],
       \"Resource\":[\"arn:aws:s3:::$BUCKET\",\"arn:aws:s3:::$BUCKET/*\"]},
      {\"Effect\":\"Allow\",\"Action\":[\"ec2:StopInstances\",\"ec2:TerminateInstances\"],\"Resource\":\"*\"}]}" >/dev/null
if ! aws iam get-instance-profile --instance-profile-name "$PROFILE_NAME" >/dev/null 2>&1; then
  aws iam create-instance-profile --instance-profile-name "$PROFILE_NAME" >/dev/null
  aws iam add-role-to-instance-profile --instance-profile-name "$PROFILE_NAME" --role-name "$ROLE_NAME" >/dev/null
  echo "Waiting for instance profile to propagate…"; sleep 15
fi

# ---- render user-data (exports + approaches.txt + body) ----
UD="$(mktemp)"; trap 'rm -f "$UD"' EXIT
{
  echo '#!/bin/bash'
  echo "export REPS=$REPS RUN_SECS=$RUN_SECS DURATION=$DURATION TARGET=$TARGET"
  echo "export SEED_BASE=$SEED_BASE SEED_STRIDE=$SEED_STRIDE BOOTSTRAP=$BOOTSTRAP"
  echo "export GENERATE_TIMEOUT_SECS=$GENERATE_TIMEOUT_SECS"
  echo "export BUCKET=$BUCKET SRC_PREFIX=$SRC_PREFIX S3ROOT=$S3ROOT"
  echo "export RESULTS_PREFIX=$RESULTS_PREFIX ON_FINISH=$ON_FINISH"
  # Only export COLLECT_WELLTYPED_ONLY when set — the binaries check presence, not value,
  # so exporting an empty string would wrongly enable the well-typed reject gate.
  [[ -n "${COLLECT_WELLTYPED_ONLY:-}" ]] && echo "export COLLECT_WELLTYPED_ONLY=1"
  [[ -n "${REUSE_CORPUS_S3ROOT:-}" ]] && echo "export REUSE_CORPUS_S3ROOT=$REUSE_CORPUS_S3ROOT"
  [[ -n "${COV_FEATURES:-}" ]] && echo "export COV_FEATURES=$COV_FEATURES"
  echo 'mkdir -p /opt/exp'
  echo "cat > /opt/exp/approaches.txt <<'APPROACHES_EOF'"
  grep -vE '^[[:space:]]*(#|$)' "$APPROACHES_FILE"
  echo 'APPROACHES_EOF'
  cat "$SCRIPT_DIR/user_data_body.sh"
} > "$UD"

echo "Launching $INSTANCE_TYPE…"
IID="$(aws ec2 run-instances --region "$REGION" \
  --image-id "$AMI_ID" --instance-type "$INSTANCE_TYPE" --count 1 \
  --iam-instance-profile "Name=$PROFILE_NAME" \
  --instance-initiated-shutdown-behavior stop \
  --block-device-mappings "[{\"DeviceName\":\"/dev/xvda\",\"Ebs\":{\"VolumeSize\":$EBS_GB,\"VolumeType\":\"gp3\",\"DeleteOnTermination\":true}}]" \
  --user-data "file://$UD" \
  --tag-specifications "ResourceType=instance,Tags=[{Key=Name,Value=cedar-exp-$S3ROOT},{Key=purpose,Value=cedar-specimen-experiment}]" \
  --query 'Instances[0].InstanceId' --output text)"

echo "Launched $IID ($INSTANCE_TYPE) in $REGION."
cat <<EOF

Watch:
  aws ec2 describe-instances --region $REGION --instance-ids $IID \\
    --query 'Reservations[0].Instances[0].State.Name' --output text
  aws ssm start-session --region $REGION --target $IID      # then: tail -f /var/log/cedar-exp.log
Results will appear at:
  s3://$BUCKET/$RESULTS_PREFIX/
On finish the instance will: $ON_FINISH  (stop = paused & reusable via run_on.sh).
Reuse later:    aws ec2 start-instances --region $REGION --instance-ids $IID ; then run_on.sh
Terminate:      aws ec2 terminate-instances --region $REGION --instance-ids $IID
EOF

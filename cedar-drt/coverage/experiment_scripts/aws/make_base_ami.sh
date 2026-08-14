#!/bin/bash
#
# Bake a GOLDEN AMI from an instance that already has the toolchains installed (system
# pkgs, rust + nightly + llvm-tools, cargo-fuzz, elan + Lean toolchain, protoc, python
# deps). Every guided experiment instance installs all of these, so any STOPPED one is a
# ready source. Future launches then SKIP the ~10-13min install phase — user_data_body.sh's
# installs are idempotent (each is guarded by a "command -v … || install" check), so the
# same user-data works on both a bare AL2023 AMI and this golden AMI.
#
# Usage:   INSTANCE_ID=i-abc123 ./make_base_ami.sh
# Then:    AMI_ID=<printed-ami> REPS=... RUN_SECS=... CONFIRM=1 ./launch.sh
#
# The AMI also captures whatever /opt/exp build exists, which warms cargo's registry/target
# cache for faster Rust rebuilds. It does NOT freeze the experiment code — launch.sh still
# ships fresh src.tgz (+ the Lean cache) and rebuilds.
set -euo pipefail
export AWS_PROFILE="${AWS_PROFILE:-cedar-experiment}"
REGION="${REGION:-us-east-1}"
IID="${INSTANCE_ID:-${1:-}}"
[[ -n "$IID" ]] || { echo "ERROR: set INSTANCE_ID=i-… (a stopped instance with toolchains)"; exit 1; }
NAME="${NAME:-cedar-exp-base-$(date -u +%Y%m%dT%H%M%SZ)}"

STATE="$(aws ec2 describe-instances --region "$REGION" --instance-ids "$IID" \
  --query 'Reservations[0].Instances[0].State.Name' --output text)"
echo "Source instance $IID is '$STATE'. Creating image '$NAME' (--no-reboot)…"

AMI="$(aws ec2 create-image --region "$REGION" --instance-id "$IID" --name "$NAME" \
  --description "cedar experiment base: rust+nightly+cargo-fuzz+elan+lean+protoc+python" \
  --no-reboot --query ImageId --output text)"
echo "AMI $AMI creating; waiting for it to become available (a few min)…"
aws ec2 wait image-available --region "$REGION" --image-ids "$AMI"
echo "AMI ready: $AMI"
echo
echo "Launch with it (skips the install phase):"
echo "  AMI_ID=$AMI REPS=20 RUN_SECS=3600 SEED_BASE=… CONFIRM=1 ./launch.sh"

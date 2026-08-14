#!/bin/bash
#
# Snapshot the LOCAL working tree (cedar-spec + its local Specimen fork + the
# cedar checkout) into a tarball and upload it to S3, so a fresh EC2 instance
# builds the *exact* code — including uncommitted changes and the patched
# Specimen (`require specimen from "../../specimen"`).
#
# Layout preserved (parent of all three):  specimen/  cedar-spec/  cedar/
# The cedar-spec/cedar symlink (-> ../cedar) is kept as-is and resolves after
# extraction because we ship cedar/ alongside.
set -euo pipefail

# Optional config file (shared with run_experiment.sh / launch.sh) can set the
# source dirs below to package a different spec version / worktree.
CONFIG="${CONFIG:-}"
[[ -n "$CONFIG" && -f "$CONFIG" ]] && source "$CONFIG"

# Source dirs — override any of these to package a different version/worktree.
# They need NOT be siblings on disk; the tarball is assembled into the required
# layout (specimen/ + cedar-spec/ + cedar/) so `require specimen from
# "../../specimen"` and the cedar-spec/cedar symlink resolve on the instance.
PARENT="${PARENT:-/local/home/segevem}"
CEDAR_SPEC_DIR="${CEDAR_SPEC_DIR:-$PARENT/cedar-spec}"   # <- point at a worktree to change spec version
SPECIMEN_DIR="${SPECIMEN_DIR:-$PARENT/specimen}"
CEDAR_DIR="${CEDAR_DIR:-$PARENT/cedar}"
BUCKET="${BUCKET:-__S3_BUCKET__}"
SRC_PREFIX="${SRC_PREFIX:-bootstrap}"
export AWS_PROFILE="${AWS_PROFILE:-cedar-experiment}"

for d in "$CEDAR_SPEC_DIR" "$SPECIMEN_DIR" "$CEDAR_DIR"; do
  [[ -e "$d" ]] || { echo "ERROR: source dir not found: $d" >&2; exit 1; }
done

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
TARBALL="$TMP/src.tgz"

EXCLUDES=(
  --exclude-vcs --exclude='*/.claude' --exclude='.claude'
  --exclude='*/.lake' --exclude='.lake'
  --exclude='*/target' --exclude='target'            # build dir (NOT src/target.rs)
  --exclude='*/target_cov' --exclude='target_cov' --exclude='*/target_sancov' --exclude='target_sancov'
  --exclude='*/build' --exclude='*.profraw' --exclude='*.rlib' --exclude='*.rmeta'
  --exclude='*/exp_*' --exclude='exp_*'
  --exclude='*/corpus*' --exclude='*/repeated_results' --exclude='*/coverage_results*'
  --exclude='*/fuzz_binary' --exclude='fuzz_binary'
  --exclude='*/dumped_tests*' --exclude='*/crash_dump'
  --exclude='*/kept_examples' --exclude='*/pruned_examples' --exclude='*/validation_dump*'
  --exclude='*/.experiment_holding' --exclude='*/node_modules' --exclude='*.png'
)

# Provenance: record commits + dirty files so the run is traceable.
PROV="$TMP/PROVENANCE.txt"
{
  echo "packaged (UTC): $(date -u +%FT%TZ)"
  echo "sources: cedar-spec=$CEDAR_SPEC_DIR  specimen=$SPECIMEN_DIR  cedar=$CEDAR_DIR"
  for d in "$CEDAR_SPEC_DIR" "$SPECIMEN_DIR" "$CEDAR_DIR"; do
    echo "== $d =="
    echo "  HEAD: $(git -C "$d" rev-parse HEAD 2>/dev/null || echo n/a)"
    echo "  branch: $(git -C "$d" rev-parse --abbrev-ref HEAD 2>/dev/null || echo n/a)"
    echo "  dirty:"; git -C "$d" status -s 2>/dev/null | sed 's/^/    /' || true
  done
} > "$PROV"

echo "Assembling tarball with layout specimen/ + cedar-spec/ + cedar/ …"
# Build one archive, forcing each source dir's top-level name via --transform,
# so the sources can live anywhere (e.g. a git worktree).
add() { # <src_dir> <top_name>
  local src="$1" top="$2" base; base="$(basename "$src")"
  tar rf "$TMP/src.tar" "${EXCLUDES[@]}" \
    --transform "s,^${base}\(/\|$\),${top}\1," \
    -C "$(dirname "$src")" "$base"
}
tar cf "$TMP/src.tar" -C "$TMP" PROVENANCE.txt
add "$SPECIMEN_DIR"   specimen
add "$CEDAR_SPEC_DIR" cedar-spec
add "$CEDAR_DIR"      cedar
gzip -c "$TMP/src.tar" > "$TARBALL"

SIZE="$(du -h "$TARBALL" | cut -f1)"
DEST="s3://$BUCKET/$SRC_PREFIX/src.tgz"
echo "Uploading $SIZE -> $DEST"
aws s3 cp "$TARBALL" "$DEST"
echo "Done: $DEST"

# Optional prebuilt Lean cache: ship the compiled Lean build so a fresh instance SKIPS the
# ~15-min `lake build` — `user_data` extracts it and lake just verifies. Must include BOTH
# builds the FFI links against:
#   cedar-lean/.lake  — the Cedar_* libs + git deps (batteries/plausible/proofwidgets).
#   specimen/.lake    — libspecimen_Specimen.a: Specimen is a PATH dependency
#                       (`require specimen from "../../specimen"`), so lake builds it in
#                       specimen's OWN .lake, NOT under cedar-lean/.lake.
# Rooted so `tar x -C $WORK` lands them at cedar-spec/cedar-lean/.lake and specimen/.lake
# (the on-instance layout). ~600MB gz; valid only while the Lean SOURCES + toolchain are
# unchanged (lake rebuilds any stale delta, so a mismatch is safe, just slower). Re-run
# with LEAN_CACHE=1 whenever the Lean spec changes.
if [[ "${LEAN_CACHE:-0}" == "1" ]]; then
  CLK="$CEDAR_SPEC_DIR/cedar-lean/.lake"; SLK="$SPECIMEN_DIR/.lake"
  if [[ ! -d "$CLK" || ! -d "$SLK" ]]; then
    echo "WARN: missing Lean build ($CLK and/or $SLK) — build first (../cedar-drt/build_lean_lib.sh); skipping cache" >&2
  else
    echo "Packaging Lean cache: cedar-lean/.lake ($(du -sh "$CLK"|cut -f1)) + specimen/.lake ($(du -sh "$SLK"|cut -f1)) …"
    CACHE_TAR="$TMP/lean_cache.tar"
    tar cf  "$CACHE_TAR" -C "$CEDAR_SPEC_DIR/cedar-lean" --transform 's,^[.]lake,cedar-spec/cedar-lean/.lake,' .lake
    tar rf  "$CACHE_TAR" -C "$SPECIMEN_DIR"              --transform 's,^[.]lake,specimen/.lake,'            .lake
    gzip -c "$CACHE_TAR" > "$TMP/lean_cache.tgz"
    LDEST="s3://$BUCKET/$SRC_PREFIX/lean_cache.tgz"
    echo "Uploading $(du -h "$TMP/lean_cache.tgz" | cut -f1) -> $LDEST"
    aws s3 cp "$TMP/lean_cache.tgz" "$LDEST"
    echo "Done: $LDEST"
  fi
fi

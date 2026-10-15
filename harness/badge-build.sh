#!/usr/bin/env bash
# Build the badge executables `harness-verify` and `harness-index` (harness/lean/Main.lean.in,
# harness/badge-main.py) against a submission module, in a fresh tree that `require`s the organiser
# package by path, sandboxed (scripts/bwrap-landrun.sh; only the tree's `.lake` is writable, so
# every organiser and package object file must be prebuilt: scripts/org-build.sh). This is the
# production gate tree's stage 3a (scripts/harness.sh --badge-build) without the comparator and the
# gate (the same tree generator, harness/mk-tree.py): for the smoke test (harness/smoke/) and for
# submitters' local checks.
#
#   harness/badge-build.sh --org ORG --work DIR [--landrun PATH] SRC_DIR MODULE SUBMISSION
#
# SRC_DIR holds the submission's .lean files (module MODULE defines the constant SUBMISSION, a
# `Submission`, `SubmissionR` or any structure with fields `P` and `cfg`). Prints the two paths.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
ORG=""; WORK=""; LANDRUN=$HERE/scripts/bwrap-landrun.sh
while [[ $# -gt 0 && "$1" == --* ]]; do
  case "$1" in
    --org) ORG=$(cd "$2" && pwd); shift 2 ;;
    --work) WORK=$2; shift 2 ;;
    --landrun) LANDRUN=$(realpath "$2"); shift 2 ;;
    *) echo "badge-build: unknown option $1" >&2; exit 2 ;;
  esac
done
[[ $# -eq 3 && -n "$ORG" && -n "$WORK" ]] || { sed -n '2,13p' "$0"; exit 2; }
SRC=$(realpath "$1"); MOD=$2; SUB=$3
mkdir -p "$WORK"; T=$(cd "$WORK" && pwd)/tree
[[ ! -e "$T" ]] || { echo "badge-build: $T exists; use a fresh --work" >&2; exit 2; }
mkdir -p "$T/submission" "$T/badge" "$T/.lake"
cp "$ORG/lean-toolchain" "$T/"
(cd "$SRC" && find . -name '*.lean' -not -path '*/.lake/*' -exec cp --parents {} "$T/submission/" \;)
for e in verify index; do python3 -I "$HERE/harness/badge-main.py" "$T/badge/Harness${e^}.lean" "$MOD" "$SUB" $e; done
python3 -I "$HERE/harness/mk-tree.py" "$ORG" "$T" badge
mkdir -p "$T/.lake/tmp"   # the linker's temporary files (the rest of the file system is read-only)
(cd "$T" && TMPDIR=$T/.lake/tmp "$LANDRUN" --env PATH --env HOME --env TMPDIR --rwx "$T/.lake" -- \
  lake build harness-verify harness-index) \
  > "$WORK/badge-build.log" 2>&1 || { tail -20 "$WORK/badge-build.log"; echo "badge-build: FAILED" >&2; exit 1; }
echo "$T/.lake/build/bin/harness-verify"
echo "$T/.lake/build/bin/harness-index"

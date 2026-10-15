#!/usr/bin/env bash
# S9 feasibility: build and run the compiled-cost probe against an organiser package (unsandboxed,
# a scratch tree; the same tree layout as harness/badge-build.sh via harness/mk-tree.py).
#   run.sh ORG REPO WORK
set -euo pipefail
ORG=$1; REPO=$2; W=$3; HERE=$(cd "$(dirname "$0")" && pwd)
rm -rf "$W"; mkdir -p "$W"; cp -r "$HERE/src/submission" "$HERE/src/badge" "$W/"
python3 -I "$REPO/harness/mk-tree.py" "$ORG" "$W" S9Bench
cp "$REPO/lean-toolchain" "$W/"
(cd "$W" && /usr/bin/time -f "build: %e s wall, %M KB" lake build harness-bench 2>&1 | grep -v "^✔\|^⣿\|^ℹ" | tail -5)
for n in 16 20; do (cd "$W" && /usr/bin/time -f "run: %e s wall, %M KB" .lake/build/bin/harness-bench $n); done

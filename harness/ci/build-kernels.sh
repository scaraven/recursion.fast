#!/usr/bin/env bash
# Builds the pinned proof checkers of the certificate job (CI; scripts/tools.env has the pins):
# leanprover/comparator at d03acab with its lean4export (076e8e5, pinned by the comparator's
# manifest) and, with RF_NANODA=1, ammkrn/nanoda_lib at 3a24072. Prints the environment lines
# (COMPARATOR_HOME, COMPARATOR_LEAN4EXPORT, COMPARATOR_NANODA) for $GITHUB_ENV. A checkout already
# at its pin with its binaries built is kept (the evaluation's `setup` job may restore an earlier
# core commit's); with --env-only nothing is built, and a missing binary is an error (the
# certificate job, after restoring the setup job's cache).
#
# Both are built with the organiser's Lean toolchain (this repository's `lean-toolchain`, v4.34.1):
# the pin d03acab names v4.34.0, and a lean4export built with another Lean than the one that wrote
# the oleans fails with "incompatible header" (CI run 39960437824). The development machine's
# checkout carries the same one-line change.
#   harness/ci/build-kernels.sh [--env-only] DIR >> "$GITHUB_ENV"
set -euo pipefail
ENV_ONLY=0; [[ "${1:-}" == --env-only ]] && { ENV_ONLY=1; shift; }
D=$(mkdir -p "$1" && cd "$1" && pwd)
TOOLCHAIN=$(cd "$(dirname "$0")/../.." && pwd)/lean-toolchain
CMP=$D/comparator/.lake/build/bin/comparator
EXPORT=$D/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export
NANODA=$D/nanoda_lib/target/release/nanoda_bin
at_pin() { [[ -d "$1/.git" && "$(git -C "$1" rev-parse --short=7 HEAD)" == "$2" ]]; }
if ! { at_pin "$D/comparator" d03acab && [[ -x "$CMP" && -x "$EXPORT" ]] && cmp -s "$TOOLCHAIN" "$D/comparator/lean-toolchain"; }; then
  [[ $ENV_ONLY == 0 ]] || { echo "build-kernels: the comparator is not built in $D" >&2; exit 1; }
  {
    rm -rf "$D/comparator"
    git -c advice.detachedHead=false clone -q https://github.com/leanprover/comparator "$D/comparator"
    git -C "$D/comparator" checkout -q d03acab
    cp "$TOOLCHAIN" "$D/comparator/lean-toolchain"
    (cd "$D/comparator" && timeout 600 lake build && timeout 600 lake build lean4export)
  } >&2
fi
echo "COMPARATOR_HOME=$D/comparator"
echo "COMPARATOR_LEAN4EXPORT=$EXPORT"
if [[ "${RF_NANODA:-0}" == 1 ]]; then
  if ! { at_pin "$D/nanoda_lib" 3a24072 && [[ -x "$NANODA" ]]; }; then
    [[ $ENV_ONLY == 0 ]] || { echo "build-kernels: nanoda is not built in $D" >&2; exit 1; }
    {
      rm -rf "$D/nanoda_lib"
      git clone -q https://github.com/ammkrn/nanoda_lib "$D/nanoda_lib"
      git -C "$D/nanoda_lib" checkout -q 3a24072
      (cd "$D/nanoda_lib" && timeout 900 cargo build --release)
    } >&2
  fi
  echo "COMPARATOR_NANODA=$NANODA"
fi

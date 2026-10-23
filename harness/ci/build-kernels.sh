#!/usr/bin/env bash
# Builds the pinned proof checkers of the certificate job (CI; scripts/tools.env has the pins):
# leanprover/comparator at d03acab with its lean4export (076e8e5, pinned by the comparator's
# manifest) and, with RF_NANODA=1, ammkrn/nanoda_lib at 3a24072. Prints the environment lines
# (COMPARATOR_HOME, COMPARATOR_LEAN4EXPORT, COMPARATOR_NANODA) for $GITHUB_ENV.
#   harness/ci/build-kernels.sh DIR >> "$GITHUB_ENV"
set -euo pipefail
D=$(mkdir -p "$1" && cd "$1" && pwd)
{
  git -c advice.detachedHead=false clone -q https://github.com/leanprover/comparator "$D/comparator"
  git -C "$D/comparator" checkout -q d03acab
  (cd "$D/comparator" && timeout 3600 lake build && timeout 3600 lake build lean4export)
} >&2
echo "COMPARATOR_HOME=$D/comparator"
echo "COMPARATOR_LEAN4EXPORT=$D/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
if [[ "${RF_NANODA:-0}" == 1 ]]; then
  {
    git clone -q https://github.com/ammkrn/nanoda_lib "$D/nanoda_lib"
    git -C "$D/nanoda_lib" checkout -q 3a24072
    (cd "$D/nanoda_lib" && timeout 3600 cargo build --release)
  } >&2
  echo "COMPARATOR_NANODA=$D/nanoda_lib/target/release/nanoda_bin"
fi

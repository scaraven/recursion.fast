#!/usr/bin/env bash
# Stage 8 probe: leanerVM's BLAKE2s table through `toLayout` (docs/stages/S8-RESULT.md).
# Copies the 13 leanerVM modules of the table's import closure (verbatim, leanerVM 485d0465) and
# the 7 repository modules `toLayout` needs into this directory (both gitignored), then
#   cd probes/s8/blake2s && lake build        # ≈ 1 min 45 s cold; prints the chip statistics
# `ProbeFib.lean` translates Clean's own `FibonacciWithChannels` over `F 521` (builds 4 more Clean
# modules in ext/Clean, ≈ 1 min).
# `.lake/packages` must be the shared prebuilt tree (as for the repository root).
#   probes/s8/blake2s/setup.sh LEANERVM_CHECKOUT
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
lvm=${1:?usage: setup.sh LEANERVM_CHECKOUT}
want=485d0465d1db38a471fb387aa0dd6baf5a5a1ac7
have=$(git -C "$lvm" rev-parse HEAD)
[ "$have" = "$want" ] || echo "warning: $lvm is at $have, the probe used $want" >&2
for f in Parameters/Field Parameters/CleanField Parameters/Blake2s Semantics/Blake2s \
    Parameters/Generator Parameters/Isa Semantics/Memory Semantics/Instruction Semantics/Step \
    Arithmetization/Bytecode Arithmetization/Channels Arithmetization/Tables/Basic \
    Arithmetization/Tables/Blake2s; do
  mkdir -p "$here/LeanerVM/$(dirname "$f")"
  cp "$lvm/LeanerVM/$f.lean" "$here/LeanerVM/$f.lean"
done
for f in Contract/Field Contract/Layout Library/Field Library/Layout Clean/FiniteField \
    Clean/Gadget Clean/ToLayout; do
  mkdir -p "$here/RecursionFast/$(dirname "$f")"
  cp "$root/RecursionFast/$f.lean" "$here/RecursionFast/$f.lean"
done
echo "copied; now: cd $here && lake build"

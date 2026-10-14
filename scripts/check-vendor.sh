#!/usr/bin/env bash
# Check that RecursionFast/Vendor/RiscvZkvm is byte-identical to riscv-zkvm at the commit named in
# RecursionFast/Vendor/RiscvZkvm/SOURCE, file by file, and that nothing else was added there.
#
#   scripts/check-vendor.sh [RISCV_ZKVM_CHECKOUT]
#
# Without an argument the upstream repository is cloned (bare, blobless) into a temp directory.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
vendor=$root/RecursionFast/Vendor/RiscvZkvm
commit=$(sed -n 's/^commit: *//p' "$vendor/SOURCE")
url=$(sed -n 's/^repo: *//p' "$vendor/SOURCE")
if [ $# -ge 1 ]; then repo=$1; else
  repo=$(mktemp -d); trap 'rm -rf "$repo"' EXIT
  git clone -q --bare --filter=blob:none "$url" "$repo"
fi
fail=0
while read -r sum upstream; do
  local_path=$vendor/${upstream#RiscvZkvm/}
  [ -f "$local_path" ] || { echo "MISSING  $upstream"; fail=1; continue; }
  have=$(sha256sum < "$local_path" | cut -d' ' -f1)
  want=$(git -C "$repo" show "$commit:$upstream" | sha256sum | cut -d' ' -f1)
  if [ "$have" = "$want" ] && [ "$have" = "$sum" ]; then echo "OK       $upstream"
  else echo "MISMATCH $upstream (local $have, manifest $sum, $commit $want)"; fail=1; fi
done < "$vendor/MANIFEST.sha256"
# No unlisted files may sit in the vendor directory.
listed=$(sed 's/^[0-9a-f]*  //; s|^RiscvZkvm/||' "$vendor/MANIFEST.sha256" | sort)
present=$(cd "$vendor" && find . -type f ! -name SOURCE ! -name MANIFEST.sha256 | sed 's|^\./||' | sort)
if [ "$listed" != "$present" ]; then
  echo "UNLISTED FILES:"; comm -13 <(echo "$listed") <(echo "$present"); fail=1; fi
[ $fail = 0 ] && echo "vendor check passed: byte-identical to $url@$commit" || { echo "vendor check FAILED"; exit 1; }

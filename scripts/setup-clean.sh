#!/usr/bin/env bash
# Fetch Clean, the UNTRUSTED circuit frontend (DESIGN §9.3; Stage 8), at the pinned revision into
# the gitignored ext/Clean, where `lakefile.toml` requires it by path. A fresh clone runs this
# before any `lake` command (Lake resolves every `[[require]]` when it loads the workspace, so the
# default targets need the directory to exist even though only `RecursionFastClean` imports it).
#
#   scripts/setup-clean.sh [CLEAN_GIT_CHECKOUT]
#
# ext/Clean is always a git checkout. Without an argument the upstream repository is cloned; with
# one, the given local git repository (which must contain the pinned commit) is cloned instead
# (offline). In every case, and also when ext/Clean already exists, the script then VERIFIES it:
# `.git` present, `git rev-parse HEAD` = the pinned revision, and no tracked file modified.
# Anything else is an error (a copy without `.git`, another revision, a tampered file).
# The root's mathlib v4.34.1 and CompPoly 572f997 pins override Clean's own v4.33.1 requires.
set -euo pipefail
rev=42fe4b268132a46604d40cc73f642a1995f26547
url=https://github.com/Verified-zkEVM/clean
root=$(cd "$(dirname "$0")/.." && pwd)
dst=$root/ext/Clean
fail() { echo "setup-clean: $*" >&2; exit 1; }
verify() {
  [ -d "$dst/.git" ] || fail "ext/Clean is not a git checkout (no .git); remove it and rerun"
  have=$(git -C "$dst" rev-parse HEAD) || fail "ext/Clean: git rev-parse failed"
  [ "$have" = "$rev" ] || fail "ext/Clean is at $have, expected $rev"
  git -C "$dst" diff --quiet HEAD -- || fail "ext/Clean has modified tracked files (git diff HEAD)"
  [ -z "$(git -C "$dst" status --porcelain --untracked-files=no)" ] ||
    fail "ext/Clean has staged or modified tracked files"
}
if [ ! -e "$dst" ]; then
  mkdir -p "$root/ext"
  src=${1:-$url}
  git clone -q --no-checkout "$src" "$dst"
  git -C "$dst" -c advice.detachedHead=false checkout -q "$rev"
fi
verify
echo "ext/Clean verified at $rev"

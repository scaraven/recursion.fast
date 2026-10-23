#!/usr/bin/env bash
# Fetches one entry root of one commit as data (TRUSTED; CI). No checkout of the pull request, no
# credentials, no hook: a bare fetch of the commit, `git archive` of the root, and a refusal of any
# entry holding something other than regular files and directories (a symbolic link could point
# the harness at a host file).
#   harness/ci/fetch-entry.sh OWNER/REPO SHA ROOT [refs/pull/N/head] OUT
set -euo pipefail
REPO=$1 SHA=$2 ROOT=$3 REF=${4:-} OUT=$5
[[ "$SHA" =~ ^[0-9a-f]{40}$ ]] || { echo "fetch-entry: not a full commit SHA: $SHA" >&2; exit 2; }
[[ "$ROOT" =~ ^[A-Za-z0-9._/-]+$ && "$ROOT" != *..* && "$ROOT" != /* ]] || { echo "fetch-entry: bad root $ROOT" >&2; exit 2; }
G=$(mktemp -d); trap 'rm -rf "$G"' EXIT
git -C "$G" init -q
git -C "$G" -c protocol.version=2 fetch -q --no-tags --depth=1 "https://github.com/$REPO.git" "${REF:-$SHA}"
got=$(git -C "$G" rev-parse FETCH_HEAD)
[[ "$got" == "$SHA" ]] || { echo "fetch-entry: fetched $got, expected $SHA (the pull request moved)" >&2; exit 1; }
mkdir -p "$OUT"
git -C "$G" archive --format=tar "$SHA:$ROOT" | tar -x -C "$OUT" --no-same-owner --no-same-permissions
bad=$(find "$OUT" ! -type f ! -type d | head -5)
[[ -z "$bad" ]] || { echo "fetch-entry: the entry holds non-regular files: $bad" >&2; exit 1; }
echo "fetch-entry: $REPO@$SHA:$ROOT ($(find "$OUT" -type f | wc -l) files)"

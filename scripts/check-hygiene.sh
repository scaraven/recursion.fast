#!/usr/bin/env bash
# Hygiene scan of our own Lean sources (not vendored, not audit/): no `sorry`, `admit`,
# `native_decide`, declaration-local `maxRecDepth`/`maxHeartbeats` (A3-M3: comparator replay
# ignores them), `implemented_by`/`extern`/`csimp`, or new `axiom`s. Comments are stripped first.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
fail=0
for f in $(find "$root/RecursionFast" -name '*.lean' -not -path '*/Vendor/*'); do
  hits=$(python3 - "$f" <<'PY'
import re, sys
s = open(sys.argv[1]).read()
s = re.sub(r'/-.*?-/', '', s, flags=re.S)          # block + doc comments (not nested-aware; fine here)
s = re.sub(r'--[^\n]*', '', s)
bad = r'\b(sorry|admit|native_decide|implemented_by|extern|csimp|axiom)\b|set_option\s+(maxRecDepth|maxHeartbeats)'
for i, line in enumerate(s.split('\n'), 1):
    if re.search(bad, line): print(f"{sys.argv[1]}: {line.strip()}")
PY
)
  if [ -n "$hits" ]; then echo "$hits"; fail=1; fi
done
[ $fail = 0 ] && echo "hygiene OK: no sorry/admit/native_decide/implemented_by/extern/csimp/axiom/local limits" || { echo "hygiene FAILED"; exit 1; }

#!/usr/bin/env bash
# Hygiene scan of our own Lean sources (not vendored): no `sorry`, `admit`, `native_decide` or
# `native` (`decide +native`), declaration-local `maxRecDepth`/`maxHeartbeats` (A3-M3: comparator
# replay ignores them), `implemented_by`/`extern`/`csimp`, or new `axiom`s. Comments (nested, as
# Lean nests them) are stripped first.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
fail=0
for f in $(find "$root/RecursionFast" -name '*.lean' -not -path '*/Vendor/*'); do
  hits=$(python3 - "$f" <<'PY'
import re, sys
def strip(s):  # block + doc comments, nested as Lean nests them, and line comments; newlines kept
    out, i, depth, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith("/-", i): depth += 1; i += 2
        elif depth and s.startswith("-/", i): depth -= 1; i += 2
        elif depth: out.append("\n" if s[i] == "\n" else ""); i += 1
        elif s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j
        else: out.append(s[i]); i += 1
    return "".join(out)
s = strip(open(sys.argv[1]).read())
bad = r'\b(sorry|admit|native_decide|native|implemented_by|extern|csimp|axiom)\b|set_option\s+(maxRecDepth|maxHeartbeats)'
for i, line in enumerate(s.split('\n'), 1):
    if re.search(bad, line): print(f"{sys.argv[1]}: {line.strip()}")
PY
)
  if [ -n "$hits" ]; then echo "$hits"; fail=1; fi
done
[ $fail = 0 ] && echo "hygiene OK: no sorry/admit/native_decide/native/implemented_by/extern/csimp/axiom/local limits" || { echo "hygiene FAILED"; exit 1; }

#!/usr/bin/env bash
# Hygiene scan of the baseline's Lean sources (the organiser's scripts/check-hygiene.sh rules, plus
# `noncomputable`, as v0.3's baseline): no sorry/admit/native_decide/implemented_by/extern/csimp/axiom/
# noncomputable, no declaration-local maxRecDepth/maxHeartbeats. Comments are stripped first. The
# rendered challenge (audit/BaselineChallenge.lean) is organiser data and holds the two `sorry`
# placeholders by design; it is not scanned.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
fail=0
for f in $(find "$root/RecursionFastCandidate" "$root/RecursionFastCandidate.lean" "$root/audit/BaselineSolution.lean" -name '*.lean'); do
  hits=$(python3 -I - "$f" <<'PY'
import re, sys
s = open(sys.argv[1]).read()
s = re.sub(r'/-.*?-/', '', s, flags=re.S)
s = re.sub(r'--[^\n]*', '', s)
bad = r'\b(sorry|admit|native_decide|implemented_by|extern|csimp|axiom|noncomputable)\b|set_option\s+(maxRecDepth|maxHeartbeats)'
for i, line in enumerate(s.split('\n'), 1):
    if re.search(bad, line): print(f"{sys.argv[1]}: {line.strip()}")
PY
)
  if [ -n "$hits" ]; then echo "$hits"; fail=1; fi
done
[ $fail = 0 ] && echo "hygiene OK: no sorry/admit/native_decide/implemented_by/extern/csimp/axiom/noncomputable/local limits" || { echo "hygiene FAILED"; exit 1; }

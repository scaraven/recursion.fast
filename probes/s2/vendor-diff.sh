#!/usr/bin/env bash
# S2 review probe: (1) regenerate iv/sigma from the RFC 7693 text (SHA-256 c9437548…) with leanerVM's
# dump script and compare with the spec; (2) diff the vendored compression against leanerVM 485d0465
# at the quoted line ranges (blank lines ignored). Run from the repository root.
set -euo pipefail
L=${1:-/home/devops/Verified-zkEVM/leanerVM}
S=RecursionFast/Contract/Hash/Blake2s.lean
echo "== constants: RFC dump vs spec"
diff <(python3 -I "$L/scripts/dump-blake2s.py" constants probes/s2/rfc7693.txt | tail -n +2 | grep -v '^$') \
     <(sed -n '/^def iv/,/0x5be0cd19\]/p;/^def sigma/,/13,  0\]\]/p' "$S") && echo "identical"
echo "== vendored code: leanerVM 485d0465 (Parameters 29-47, Semantics 64-110) vs spec"
diff <({ git -C "$L" show 485d0465:LeanerVM/Parameters/Blake2s.lean | sed -n 29,47p
         git -C "$L" show 485d0465:LeanerVM/Semantics/Blake2s.lean | sed -n 64,110p; } | grep -v '^$') \
     <(sed -n '/^\/-- The BLAKE2s initialization/,/h\[6\] ^^^ v\[6\] ^^^ v\[14\]/p' "$S" | grep -v '^$') || true

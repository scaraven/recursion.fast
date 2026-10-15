#!/usr/bin/env bash
# A6-G1/G2 regressions (probes/s6b/pipeline/gateproj, Lean core only; v0.3 probes/a6/gateproj), against the gate binary $1
# (default: this tree's .lake/build/bin/gate). Each must be REJECTED:
#   G1  InitSol: `@[init evilInit] def vk := 0` (kernel 0, compiled 1337) -> gate rejects the [init] entry;
#       ExportSol: an `@[export]` symbol -> rejected.
#   G2  TamperSol/TamperCert: the solution build rewrites the contract root `.olean` and adds a module
#       `RecursionFast.Contract.Evil` with an `implemented_by` -> the manifest check fails, and the gate
#       (trust by content hash) rejects the tampered root and the untrusted Evil module.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/../.." && pwd)
GATE=$(realpath "${1:-$HERE/.lake/build/bin/gate}")
P=$HERE/probes/s6b/pipeline/gateproj
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
manifest() { python3 -I "$HERE/scripts/olean-manifest.py" "$1" --org "$2" --packages '' --prefix RecursionFast.Contract "$3"; }
setup() {  # dir: organiser build of the stand-in contract + manifest, before any solution code
  mkdir -p "$1"; cp -r "$P"/. "$1/"
  (cd "$1" && lake build Contract > /dev/null)
  manifest gen "$1" "$1.manifest" > /dev/null
}
expect_reject() {  # name, pattern, command...
  local n=$1 pat=$2; shift 2
  if "$@" > "$T/$n.log" 2>&1; then echo "gateproj $n: ACCEPTED (regression)"; cat "$T/$n.log"; exit 1; fi
  grep -q -- "$pat" "$T/$n.log" || { echo "gateproj $n: rejected, but not for: $pat"; cat "$T/$n.log"; exit 1; }
  echo "gateproj $n: rejected: $(grep -h -- "$pat" "$T/$n.log" | head -2 | tr '\n' ' ')"
}
# G1 (clean tree: no tampering, only the [init] divergence)
setup "$T/g1"
(cd "$T/g1" && lake build InitSol badge > /dev/null 2>&1)
manifest check "$T/g1" "$T/g1.manifest" > /dev/null
echo "gateproj G1: kernel: InitSol.cert proves vk = 0; badge (own process): $("$T/g1/.lake/build/bin/badge")"
expect_reject G1 "\[init\]" bash -c "cd '$T/g1' && lake env '$GATE' InitSol InitSol.cert --manifest '$T/g1.manifest' \
  --computable InitSol.submission,InitSol.vk"
expect_reject G1-export "@\[export lean_recursionfast_evil\]" bash -c "cd '$T/g1' && lake build ExportSol > /dev/null && \
  lake env '$GATE' ExportSol ExportSol.cert --manifest '$T/g1.manifest' --computable ExportSol.submission"
# G2 (A6's order: the solution is built in the tree that the gate then reads)
setup "$T/g2"
(cd "$T/g2" && lake build TamperCert > /dev/null 2>&1)
expect_reject G2-manifest "olean-manifest: FAIL" manifest check "$T/g2" "$T/g2.manifest"
expect_reject G2-gate "does not match the manifest" bash -c "cd '$T/g2' && lake env '$GATE' TamperCert cert \
  --manifest '$T/g2.manifest' --computable submission"
grep -q "Contract.Evil: @\[implemented_by RecursionFast.shownVk\]" "$T/G2-gate.log" || { echo "gateproj G2: Evil's implemented_by not reported"; exit 1; }
echo "gateproj regression OK"

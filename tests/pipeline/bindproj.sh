#!/usr/bin/env bash
# A7-M3 regression (probes/s6b/pipeline/bindproj, Lean core only; v0.3 probes/a7/bindproj), against the gate binary $1 (default: the
# organiser build's): the gate and the badge must run on the build the comparator verified.
#   H  Honest.lean through the harness (comparator, then gate): ACCEPT, and the gate tree's build
#      reproduces the comparator tree's artifacts byte for byte (Lean builds are deterministic; its
#      linter warning puts the absolute source path into the .olean, so the rebuild is at the same path).
#   S  SwitchSol.lean: honest in the comparator's build (kept as WORK/cmp); in the gate's rebuild
#      (WORK/tree) it elaborates `submission.vk = 1337` and a false `certified` (ill-typed proof added
#      under debug.skipKernelTC). The comparator accepts its
#      cmp build and the gate ALONE passes its gate-tree build (both shown), but the harness REJECTS:
#      "gate tree build differs from the comparator-verified build".
# (S6b fix pass) `--source-rule off`: this regression tests one layer alone; its probes use `#eval`
# and `import Lean` on purpose, which the source rule (scripts/source-rule.py) would reject first.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/../.." && pwd)
GATE=$(realpath "${1:-$HERE/.lake/org/.lake/build/bin/gate}")
P=$HERE/probes/s6b/pipeline/bindproj
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
manifest() { python3 -I "$HERE/scripts/olean-manifest.py" "$1" --org "$2" --packages '' --prefix RecursionFast.Contract "$3"; }
# organiser package: the stand-in contract (built before any solution code exists) and the gate
mkdir -p "$T/org/RecursionFast" "$T/org/.lake/build/bin"
cp "$P/RecursionFast/Contract.lean" "$T/org/RecursionFast/"; cp "$P/lean-toolchain" "$P/lake-manifest.json" "$T/org/"
printf 'name = "bindproj"\n[[lean_lib]]\nname = "Contract"\nroots = ["RecursionFast.Contract"]\n' > "$T/org/lakefile.toml"
(cd "$T/org" && lake build Contract > /dev/null)
cp "$GATE" "$T/org/.lake/build/bin/gate"
manifest gen "$T/org" "$T/org.manifest" > /dev/null
harness() {  # solution module
  mkdir -p "$T/sol-$1"; cp "$P/$1.lean" "$T/sol-$1/"
  "$HERE/scripts/harness.sh" --source-rule off --org "$T/org" --manifest "$T/org.manifest" --packages '' --prefix RecursionFast.Contract \
    --work "$T/w-$1" --gate certified --computable submission "$P/Challenge.lean" "$T/sol-$1" "$P/config-$1.json"
}
vk() { printf 'import %s\n#eval submission.vk\n' "$2" > "$T/vk.lean"; (cd "$1" && lake env lean "$T/vk.lean"); }

harness Honest > "$T/H.log" 2>&1 || { cat "$T/H.log"; echo "bindproj H: honest solution REJECTED (regression)"; exit 1; }
grep -q "HARNESS: ACCEPT" "$T/H.log"
grep -aq "$T/w-Honest/tree/submission/Honest.lean" "$T/w-Honest/cmp/.lake/build/lib/lean/Honest.olean" \
  || { echo "bindproj H: expected the .olean to record the absolute source path (linter log)"; exit 1; }
echo "bindproj H: accepted (its .olean records the absolute source path; same-path rebuild): $(grep -h "gate tree build = " "$T/H.log")"

if harness SwitchSol > "$T/S.log" 2>&1; then cat "$T/S.log"; echo "bindproj S: ACCEPTED (regression)"; exit 1; fi
grep -q "Your solution is okay" "$T/w-SwitchSol/comparator.log" || { cat "$T/S.log"; echo "bindproj S: expected the comparator to accept the cmp build"; exit 1; }
grep -q "HARNESS: REJECT (gate tree build differs from the comparator-verified build" "$T/S.log" \
  || { cat "$T/S.log"; echo "bindproj S: rejected, but not by the build binding"; exit 1; }
echo "bindproj S: comparator accepted its build (submission.vk = $(vk "$T/w-SwitchSol/cmp" SwitchSol))"
(cd "$T/w-SwitchSol/tree" && lake env "$GATE" SwitchSol certified --manifest "$T/org.manifest" --computable submission) > "$T/S-gate.log" 2>&1 \
  || { cat "$T/S-gate.log"; echo "bindproj S: expected the gate alone to pass the gate-tree build"; exit 1; }
echo "bindproj S: the gate alone PASSES the gate-tree build (submission.vk = $(vk "$T/w-SwitchSol/tree" SwitchSol), false certified)"
echo "bindproj S: harness: $(grep -h "differs from the comparator-verified build:" "$T/S.log" | head -2 | tr '\n' ' ')$(grep -h "HARNESS:" "$T/S.log")"
echo "bindproj regression OK"

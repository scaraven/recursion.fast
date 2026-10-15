#!/usr/bin/env bash
# Full check of the v2 baseline submission `P_triv` (Stage 7). Logs go to logs/S7/.
#
#   submissions/baseline/scripts/check.sh
#       extractor image (if riscv64-unknown-elf-as is installed), hygiene, `lake build
#       RecursionFastCandidate`, render the challenge from claim.json (the organiser's
#       RecursionFast/Challenge/L.lean.in and scripts/render-challenge.py), make the solution, elaborate
#       both, axioms, leanchecker, negative claims (one image bit, another arity), tape sizes.
#   HARNESS=1 ORG=DIR MANIFEST=FILE submissions/baseline/scripts/check.sh
#       also the production harness (comparator with the Lean kernel and nanoda, then the gate), on
#       an organiser package built by scripts/org-build.sh DIR and its manifest
#       (scripts/olean-manifest.py gen --org DIR FILE). COMPARATOR_HOME / COMPARATOR_NANODA as for
#       scripts/harness.sh.
set -euo pipefail
B=$(cd "$(dirname "$0")/.." && pwd); C=$(cd "$B/../.." && pwd); L=$C/logs/S7; mkdir -p "$L"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
cd "$C"
if command -v riscv64-unknown-elf-as > /dev/null; then
  cp "$B/extractor/extractor.bin" "$T/committed.bin"
  "$B/extractor/build.sh"
  cmp "$B/extractor/extractor.bin" "$T/committed.bin" && echo "extractor.bin reassembled byte-identically"
fi
"$B/scripts/check-hygiene.sh" | tee "$L/hygiene.log"
rm -rf .lake/build/lib/lean/RecursionFastCandidate .lake/build/lib/lean/RecursionFastCandidate.*
/usr/bin/time -f "candidate build: %e s wall, %M KB max" lake build RecursionFastCandidate 2>&1 \
  | grep -v "^⣿" | tee "$L/build-candidate.log" | grep -E "error|warning|candidate build|Built RecursionFastCandidate"
python3 -I scripts/render-challenge.py RecursionFast/Challenge/L.lean.in "$B/claim.json" "$B/audit/BaselineChallenge.lean"
python3 -I "$B/scripts/make-solution.py" "$B/audit/BaselineChallenge.lean" "$B/audit/BaselineSolution.lean"
lake env lean "$B/audit/BaselineChallenge.lean" 2>&1 | tee "$L/challenge.log"
[ "$(grep -c "declaration uses \`sorry\`" "$L/challenge.log")" = 2 ] && [ "$(grep -c error "$L/challenge.log" || true)" = 0 ] \
  || { echo "challenge: expected exactly the two sorry placeholders"; exit 1; }
lake env lean -o "$T/BaselineSolution.olean" "$B/audit/BaselineSolution.lean" 2>&1 | tee "$L/solution.log"
LP="$(lake env printenv LEAN_PATH):$T"
LEAN_PATH=$LP lake env lean "$B/scripts/Axioms.lean" 2>&1 | tee "$L/axioms.log"
if grep -vE "depends on axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$|does not depend on any axioms$" "$L/axioms.log"; then
  echo "axiom audit FAILED"; exit 1; fi
TCBIN=$(dirname "$(lake env which lean)")
(cd "$T" && /usr/bin/time -f "leanchecker: %e s wall, %M KB max" env PATH="$TCBIN:$PATH" LEAN_PATH="$LP" \
  leanchecker BaselineSolution) 2>&1 | tee "$L/leanchecker.log"
# Negative claims: the certificate binds the configuration and the extractor image to the claim.
mkdir -p "$T/img/extractor" "$T/ar/extractor"
cp "$B/extractor/extractor.data" "$T/img/extractor/"; cp "$B/extractor/extractor."* "$T/ar/extractor/"
python3 -I - "$B" "$T" <<'PY'
import json, sys
b, t = sys.argv[1:]
d = bytearray(open(f"{b}/extractor/extractor.bin", "rb").read()); d[0] ^= 1
open(f"{t}/img/extractor/extractor.bin", "wb").write(bytes(d))
c = json.load(open(f"{b}/claim.json")); json.dump(c, open(f"{t}/img/claim.json", "w"))
c["arity"] = 4; json.dump(c, open(f"{t}/ar/claim.json", "w"))
PY
for v in img ar; do
  python3 -I scripts/render-challenge.py RecursionFast/Challenge/L.lean.in "$T/$v/claim.json" "$T/$v/Ch.lean"
  python3 -I "$B/scripts/make-solution.py" "$T/$v/Ch.lean" "$T/$v/Sol.lean"
  if lake env lean "$T/$v/Sol.lean" > "$T/$v/out.log" 2>&1; then echo "negative claim $v ACCEPTED (bad)"; exit 1; fi
  echo "negative claim $v rejected: $(grep -m1 error "$T/$v/out.log")"
done | tee "$L/negative-claims.log"
# Tape sizes: L_chain(2^10) measured in Lean, then the arithmetic.
python3 -I harness/gen-chain-layout.py layout --n 1024 "$T/L.json"
python3 -I harness/gen-chain-layout.py report --n 1024 > "$L/chain-report-1024.log"
python3 -I harness/render-layout.py "$T/Lc.lean" "L_chain(1024) for the S7 tape sizes" Lc=$T/L.json
python3 -I - "$T/Lc.lean" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
s = s.replace("import RecursionFast.Contract.Layout\n", "import RecursionFast.Contract.Layout\nimport RecursionFast.Library.Codec\n", 1)
s += '\nopen RecursionFast RecursionFast.Controls.Chain in\n#eval s!"SIZES chips {Lc.chips.length} elayout {(Codec.eLayout Lc).length} admissible24 {decide (Lc.Admissible 24)} admissible23 {decide (Lc.Admissible 23)}"\n'
open(p, "w").write(s)
PY
lake env lean "$T/Lc.lean" | tee "$L/lchain1024-sizes.log"
read -r chips elay < <(sed -n 's/.*SIZES chips \([0-9]*\) elayout \([0-9]*\).*/\1 \2/p' "$L/lchain1024-sizes.log")
cells=$(sed -n 's/^n = 1024: cells \([0-9]*\).*/\1/p' "$L/chain-report-1024.log")
fixed=$(sed -n 's/^n = 1024: .*fixed cells \([0-9]*\).*/\1/p' "$L/chain-report-1024.log")
python3 -I "$B/scripts/tape-size.py" "$cells" "$chips" "$elay" "$fixed" | tee "$L/tape-size.log"
python3 -I scripts/loc.py "$B/RecursionFastCandidate.lean" "$B"/RecursionFastCandidate/*.lean "$B/audit/BaselineSolution.lean" | tee "$L/loc.log"
if [ "${HARNESS:-0}" = 1 ]; then
  mkdir -p "$T/sol"; cp -r "$B/RecursionFastCandidate" "$B/RecursionFastCandidate.lean" "$B/audit/BaselineSolution.lean" "$T/sol/"
  /usr/bin/time -f "HARNESS: %e s wall, %M KB max" scripts/harness.sh --org "${ORG:?}" --manifest "${MANIFEST:?}" --work "$T/h" \
    --gate RecursionFast.Challenge.certified --computable RecursionFast.Challenge.submission \
    "$B/audit/BaselineChallenge.lean" "$T/sol" "$B/audit/comparator-nanoda.json" > "$L/harness-L.log" 2>&1 || true
  grep -E "HARNESS|kernel|gate:|TIME" "$L/harness-L.log"
  grep -q "HARNESS: ACCEPT" "$L/harness-L.log" || { echo "harness REJECTED"; exit 1; }
fi
echo "CHECK OK"

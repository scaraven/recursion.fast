#!/usr/bin/env bash
# Gate rule 4's fixtures (V3-S2R-A3; review V3-S2R-m4). Usage: tests/gate/check.sh
# Needs the gate and the organiser targets built (`lake build`, `lake build gate`). The manifest is
# generated here from this tree, so the fixtures check rule 4's behaviour, not S3's reference build
# (V3-S2R-A4 item 3).
#   ws        the witness-sending submission, computable as a whole: PASS
#   backdoor  the backdoor submission, noncomputable as a whole (`ε := errorCap`): PASS, with each
#             badge-path field V, P, ext compiled one by one
#   neg       tests/gate/GateNeg.lean, a submission with a noncomputable `ext`: REJECT `badS.ext`
set -euo pipefail
HERE=$(cd "$(dirname "$0")/../.." && pwd); cd "$HERE"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "gate fixtures: $*"; exit 1; }
python3 scripts/olean-manifest.py gen "$T/manifest.sha256" > "$T/manifest.log"
G=(.lake/build/bin/gate)
gate() { lake env bash -c "LEAN_PATH=$T/olean:\$LEAN_PATH ${G[*]} $*"; }
mkdir -p "$T/olean"
lake env lean -o "$T/olean/GateNeg.olean" tests/gate/GateNeg.lean

gate RecursionFast.Controls.Certificate RecursionFast.Controls.Certificate.ws_certificate \
  --manifest "$T/manifest.sha256" --computable RecursionFast.WitnessSending.submission > "$T/ws.log" 2>&1 \
  || { cat "$T/ws.log"; fail "ws: rejected"; }
grep -q "^gate: PASS" "$T/ws.log" || { cat "$T/ws.log"; fail "ws: no PASS"; }
echo "ws: PASS"

B=RecursionFast.Controls.Backdoor
gate $B $B.certified --manifest "$T/manifest.sha256" --computable $B.S > "$T/backdoor.log" 2>&1 \
  || { cat "$T/backdoor.log"; fail "backdoor: rejected"; }
for f in V P ext; do
  grep -q "^gate: rule 4: $B.S.$f: compiled code" "$T/backdoor.log" \
    || { cat "$T/backdoor.log"; fail "backdoor: badge-path field $f not checked"; }
done
grep -q "^gate: PASS" "$T/backdoor.log" || { cat "$T/backdoor.log"; fail "backdoor: no PASS"; }
echo "backdoor: PASS, fields V, P, ext compiled one by one"

if gate GateNeg badS_fact --manifest "$T/manifest.sha256" --computable badS > "$T/neg.log" 2>&1; then
  cat "$T/neg.log"; fail "neg: ACCEPTED a noncomputable ext"
fi
grep -q "^gate: REJECT badS.ext: badExt has no compiled code" "$T/neg.log" \
  || { cat "$T/neg.log"; fail "neg: not rejected for badS.ext"; }
[[ $(grep -c "^gate: REJECT" "$T/neg.log") == 1 ]] || { cat "$T/neg.log"; fail "neg: unexpected rejection"; }
echo "neg: REJECT badS.ext"
echo "gate fixtures OK"

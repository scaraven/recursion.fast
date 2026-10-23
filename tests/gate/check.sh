#!/usr/bin/env bash
# The gate's fixtures (v4). Usage: tests/gate/check.sh (from anywhere)
# Needs the organiser built (`lake build`), the harness tools (harness/lean-tools: `lake build gate`)
# and the olean manifest of `harness/org-setup.sh` (.lake/rf/manifest.sha256; generated here
# without the closure restriction if it is missing).
#   ws        the witness-sending submission, computable as a whole: PASS
#   backdoor  the backdoor submission (Controls/Backdoor), noncomputable as a whole: PASS, with each
#             badge-path field V, P, ext compiled one by one
#   neg       tests/gate/GateNeg.lean: REJECT `badS.ext` (rule 4), `@[implemented_by]` (rule 3),
#             the `partial` definition (rule 2)
set -euo pipefail
HERE=$(cd "$(dirname "$0")/../.." && pwd); cd "$HERE"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "gate fixtures: $*"; exit 1; }
M=.lake/rf/manifest.sha256
[[ -f $M ]] || { M=$T/manifest.sha256; python3 -I scripts/olean-manifest.py gen "$M" > "$T/manifest.log"; }
G=$HERE/harness/lean-tools/.lake/build/bin/gate
[[ -x $G ]] || fail "build the gate first (harness/lean-tools)"
gate() { lake env bash -c "LEAN_PATH=$T/olean:\$LEAN_PATH $G $*"; }
mkdir -p "$T/olean"
lake env lean -o "$T/olean/GateNeg.olean" tests/gate/GateNeg.lean

C=RecursionFast.Controls.Certificate
gate $C $C.ws_certificate --manifest "$M" --computable RecursionFast.WitnessSending.submission > "$T/ws.log" 2>&1 \
  || { cat "$T/ws.log"; fail "ws: rejected"; }
grep -q "^gate: PASS" "$T/ws.log" || { cat "$T/ws.log"; fail "ws: no PASS"; }
echo "ws: PASS ($(grep 'closure of' "$T/ws.log" | sed 's/.*closure of //'))"

B=RecursionFast.Controls.Backdoor
gate $B $B.certified --manifest "$M" --computable $B.S > "$T/backdoor.log" 2>&1 \
  || { cat "$T/backdoor.log"; fail "backdoor: rejected"; }
for f in V P ext; do
  grep -q "^gate: rule 4: $B.S.$f: compiled code" "$T/backdoor.log" \
    || { cat "$T/backdoor.log"; fail "backdoor: badge-path field $f not checked"; }
done
grep -q "^gate: PASS" "$T/backdoor.log" || { cat "$T/backdoor.log"; fail "backdoor: no PASS"; }
echo "backdoor: PASS, fields V, P, ext compiled one by one"

neg() {  # ROOT_THEOREM SUBMISSION EXPECTED_REJECT_SUBSTRING
  if gate GateNeg "$1" --manifest "$M" --computable "$2" > "$T/neg.log" 2>&1; then
    cat "$T/neg.log"; fail "$2: ACCEPTED"
  fi
  grep "^gate: REJECT" "$T/neg.log" | grep -q -- "$3" || { cat "$T/neg.log"; fail "$2: not rejected for $3"; }
  echo "$2: REJECT ($(grep -m1 "^gate: REJECT" "$T/neg.log" | grep -- "$3" | cut -c14-120 || grep -m1 -- "$3" "$T/neg.log" | cut -c14-120))"
}
neg badS_fact badS "badS.ext: badExt has no compiled code"
neg implS_fact implS "@\[implemented_by"
neg partialS_fact partialS "partial"
echo "gate fixtures OK"

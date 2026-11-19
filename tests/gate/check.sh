#!/usr/bin/env bash
# The gate's fixtures. Usage: tests/gate/check.sh (from anywhere)
# Needs the organiser built (`lake build`), the harness tools (harness/lean-tools: `lake build gate`)
# and the olean manifest of `harness/org-setup.sh` (.lake/rf/manifest.sha256; generated here
# without the closure restriction if it is missing).
#   ws        the witness-sending submission, computable as a whole: PASS
#   backdoor  the backdoor submission (Controls/Backdoor), noncomputable as a whole: PASS, with each
#             badge-path field V, P, ext compiled one by one
#   comppoly  tests/gate/GateCompPoly.lean, importing CompPoly's BF64/Ext3: PASS, its `@[csimp]`
#             lemma reported as a pinned dependency's note
#   neg       tests/gate/GateNeg.lean: REJECT `badS.ext` (rule 4), `@[implemented_by]` (rule 3),
#             the `partial` definition (rule 2)
#   wiring    the badge's per-entry module (harness/badge/Verify.lean.in) rendered around
#             tests/gate/GateWiringSub.lean: PASS (rule 9, `--wiring`); around
#             tests/gate/GateWiringHijack.lean, whose notation turns `RFBadge.main` into an
#             accept-all `main`: REJECT; around tests/gate/GateWiringSubst.lean, whose notation
#             turns `RecursionFast.Challenge.submission` into an accept-all one: REJECT; and the
#             honest rendering with one more declaration: REJECT
set -euo pipefail
HERE=$(cd "$(dirname "$0")/../.." && pwd); cd "$HERE"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "gate fixtures: $*"; exit 1; }
M=.lake/rf/manifest.sha256
# (regenerated here also if it predates the badge's glue, `RecursionFast.Badge`, which rule 9 trusts by hash)
[[ -f $M ]] && grep -q "project/RecursionFast/Badge.olean" "$M" \
  || { M=$T/manifest.sha256; python3 -I scripts/olean-manifest.py gen "$M" > "$T/manifest.log"; }
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
lake env lean -o "$T/olean/GateCompPoly.olean" tests/gate/GateCompPoly.lean
A=.lake/rf/allowlist.txt; [[ -f $A ]] || fail "run harness/org-setup.sh first (the allowlist)"
gate GateCompPoly compS_fact --manifest "$M" --computable compS --allowed-imports "$A" > "$T/comppoly.log" 2>&1 \
  || { cat "$T/comppoly.log"; fail "comppoly: rejected"; }
grep -q "^gate: note: pinned dependency CompPoly.Fields.Extension.Arithmetic registers" "$T/comppoly.log" \
  || { cat "$T/comppoly.log"; fail "comppoly: the csimp lemma is not reported as a pinned note"; }
echo "comppoly: PASS ($(grep -c '^gate: note:' "$T/comppoly.log") note(s) on pinned dependencies)"

neg badS_fact badS "badS.ext: badExt has no compiled code"
neg implS_fact implS "@\[implemented_by"
neg partialS_fact partialS "partial"

# rule 9: the badge's per-entry module, rendered from the template as harness/evaluate.py does
wiring() {  # NAME SOLUTION_MODULE EXTRA_LINE
  sed "s/{{solution_module}}/$2/" harness/badge/Verify.lean.in > "$T/$1.lean"
  [[ -z $3 ]] || echo "$3" >> "$T/$1.lean"
  lake env bash -c "LEAN_PATH=$T/olean:\$LEAN_PATH lean --root=$T -o $T/olean/$1.olean $T/$1.lean"
  lake env bash -c "LEAN_PATH=$T/olean:\$LEAN_PATH $G --wiring $1 --manifest $M" > "$T/$1.log" 2>&1
}
for f in GateWiringSub GateWiringHijack GateWiringSubst; do lake env lean -o "$T/olean/$f.olean" tests/gate/$f.lean; done
wiring WiringGood GateWiringSub "" || { cat "$T/WiringGood.log"; fail "wiring: the honest per-entry module rejected"; }
grep -q "^gate: PASS" "$T/WiringGood.log" || { cat "$T/WiringGood.log"; fail "wiring: no PASS"; }
echo "wiring: PASS (main := RFBadge.main RecursionFast.Challenge.submission)"
wneg() {  # NAME SOLUTION_MODULE EXTRA_LINE EXPECTED_REJECT_SUBSTRING
  if wiring "$1" "$2" "$3"; then cat "$T/$1.log"; fail "wiring $1: ACCEPTED"; fi
  grep "^gate: REJECT" "$T/$1.log" | grep -q -- "$4" || { cat "$T/$1.log"; fail "wiring $1: not rejected for $4"; }
  echo "wiring $1: REJECT ($(grep -m1 "^gate: REJECT" "$T/$1.log" | cut -c14-120))"
}
wneg WiringHijack GateWiringHijack "" "main is not RFBadge.main RecursionFast.Challenge.submission: its value is fakeMain"
wneg WiringSubst GateWiringSubst "" "its value is RFBadge.main RecursionFast.Challenge.other"
wneg WiringExtra GateWiringSub "def extra : Nat := 0" "besides main"
echo "gate fixtures OK"

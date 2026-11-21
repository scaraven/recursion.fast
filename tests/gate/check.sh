#!/usr/bin/env bash
# The gate's fixtures. Usage: tests/gate/check.sh (from anywhere)
# Needs the organiser built (`lake build`), the harness tools (harness/lean-tools: `lake build gate`)
# and the olean manifest of `harness/org-setup.sh` (.lake/rf/manifest.sha256; generated here
# without the closure restriction if it is missing).
#   ws        the witness-sending submission, computable as a whole: PASS
#   masked    the masked-leaf submission (Controls/MaskedLeaf: V asks the oracle, E reads the log),
#             its CertificateR: PASS
#   backdoor  the backdoor submission (Controls/Backdoor), noncomputable as a whole: PASS, with each
#             badge-path field V, P, ext compiled one by one
#   comppoly  tests/gate/GateCompPoly.lean, importing CompPoly's BF64/Ext3: PASS, its `@[csimp]`
#             lemma reported as a pinned dependency's note
#   neg       tests/gate/GateNeg.lean: REJECT `badS.ext` (rule 4), `@[implemented_by]` (rule 3),
#             the `partial` definition (rule 2)
#   manifest-dup  the manifest with one more line, a core module's path under a pinned package's
#             tag: the gate refuses it (a path's class must not depend on the line order)
#   tamper    a copy of the organiser module RecursionFast.Contract.Tree with one more theorem,
#             compiled under the same module name into a directory that precedes LEAN_PATH (a
#             stale or tampered organiser .olean): REJECT for rule 5 alone
#   import    tests/gate/GateImport.lean, importing Lean.Compiler.LCNF.PhaseExt (outside the
#             allowlist), with --allowed-imports: REJECT for rule 6 alone (the direct import and
#             rule 6t's transitive reach); with --badge-root importS: REJECT for rule 8 too
#   badgeroot a badge root declared in a trusted module outside the allowlist (the core module
#             Lean.Compiler.LCNF.PhaseExt, gated as the environment's module): REJECT for rule 8
#             alone (rules 6 and 6t see only untrusted modules; rule 8 is what remains)
#   meta      tests/gate/GateMeta.lean, a definition whose value is Lean.modifyEnv, reached through
#             allowlisted imports, with --allowed-imports: REJECT for rule 7 alone
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
gate() { lake env bash -c "LEAN_PATH=${GP:-$T/olean}:\$LEAN_PATH $G $*"; }   # GP: the search path prefix
mkdir -p "$T/olean"
lake env lean -o "$T/olean/GateNeg.olean" tests/gate/GateNeg.lean

C=RecursionFast.Controls.Certificate
gate $C $C.ws_certificate --manifest "$M" --computable RecursionFast.WitnessSending.submission > "$T/ws.log" 2>&1 \
  || { cat "$T/ws.log"; fail "ws: rejected"; }
grep -q "^gate: PASS" "$T/ws.log" || { cat "$T/ws.log"; fail "ws: no PASS"; }
echo "ws: PASS ($(grep 'closure of' "$T/ws.log" | sed 's/.*closure of //'))"

ML=RecursionFast.Controls.MaskedLeaf
gate $ML $ML.certificateR --manifest "$M" --computable $ML.submission > "$T/masked.log" 2>&1 \
  || { cat "$T/masked.log"; fail "masked: rejected"; }
grep -q "^gate: PASS" "$T/masked.log" || { cat "$T/masked.log"; fail "masked: no PASS"; }
echo "masked: PASS ($(grep 'closure of' "$T/masked.log" | sed 's/.*closure of //'))"

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

rej() {  # NAME EXPECTED_SUBSTRING GATE_ARGS...: REJECT, every REJECT line holding EXPECTED_SUBSTRING
  local name=$1 want=$2; shift 2
  if gate "$@" > "$T/$name.log" 2>&1; then cat "$T/$name.log"; fail "$name: ACCEPTED"; fi
  local rejs; rejs=$(grep "^gate: REJECT" "$T/$name.log" || true)
  grep -qF -- "$want" <<< "$rejs" || { cat "$T/$name.log"; fail "$name: not rejected for $want"; }
  [[ -z $(grep -vF -- "$want" <<< "$rejs") ]] || { cat "$T/$name.log"; fail "$name: rejected by another rule too"; }
  echo "$name: REJECT ($(grep -m1 -F -- "$want" <<< "$rejs" | cut -c14-160))"
}
# the manifest: two keys with one module path (the class would follow the line order) are an error
{ cat "$M"; grep -m1 "  core/Init/Prelude.olean$" "$M" | sed 's#  core/#  packages/CompPoly/#'; } > "$T/dup.sha256"
gate GateNeg badS_fact --manifest "$T/dup.sha256" > "$T/dup.log" 2>&1 && { cat "$T/dup.log"; fail "manifest-dup: ACCEPTED"; }
grep -qF "packages/CompPoly/Init/Prelude.olean have one module path Init/Prelude.olean" "$T/dup.log" \
  || { cat "$T/dup.log"; fail "manifest-dup: not refused for the duplicate path"; }
echo "manifest-dup: error ($(grep -m1 -oF "manifest keys core/Init/Prelude.olean and packages/CompPoly/Init/Prelude.olean have one module path Init/Prelude.olean" "$T/dup.log"))"
# rule 5: a tampered (or stale) organiser .olean, found before the organiser's own (Lean resolves
# a module's package root `RecursionFast` on the search path, so the tampered tree is a copy of the
# organiser's with one module recompiled)
mkdir -p "$T/tamper" "$T/tsrc/RecursionFast/Contract"
cp -r .lake/build/lib/lean/RecursionFast "$T/tamper/"
{ cat RecursionFast/Contract/Tree.lean; echo; echo "theorem gateTampered : True := trivial"; } > "$T/tsrc/RecursionFast/Contract/Tree.lean"
lake env lean --root="$T/tsrc" -o "$T/tamper/RecursionFast/Contract/Tree.olean" "$T/tsrc/RecursionFast/Contract/Tree.lean"
GP=$T/tamper:$T/olean rej tamper "organiser module RecursionFast.Contract.Tree: .olean does not match the manifest" \
  RecursionFast.Contract.Tree gateTampered --manifest "$M"
# rules 6 and 8: an import outside the allowlist
lake env lean -o "$T/olean/GateImport.olean" tests/gate/GateImport.lean
rej import "outside the allowed imports" GateImport importS_fact --manifest "$M" --allowed-imports "$A"
gate GateImport importS_fact --manifest "$M" --allowed-imports "$A" --badge-root importS > "$T/import8.log" 2>&1 \
  && { cat "$T/import8.log"; fail "import8: ACCEPTED"; }
grep -qF "REJECT badge root importS is declared in module GateImport, which imports (transitively)" "$T/import8.log" \
  || { cat "$T/import8.log"; fail "import8: not rejected for rule 8"; }
echo "import8: REJECT ($(grep -m1 -F "REJECT badge root importS" "$T/import8.log" | cut -c14-160))"
rej badgeroot "badge root Lean.Compiler.LCNF.impureExt is declared in module Lean.Compiler.LCNF.PhaseExt, which imports (transitively)" \
  Lean.Compiler.LCNF.PhaseExt Nat.le_refl --manifest "$M" --allowed-imports "$A" --badge-root Lean.Compiler.LCNF.impureExt
# rule 7: a definition over the environment's API, through allowlisted imports
lake env lean -o "$T/olean/GateMeta.olean" tests/gate/GateMeta.lean
rej meta "module GateMeta: wipeEnv refers to the compiler/environment API" GateMeta meta_fact --manifest "$M" --allowed-imports "$A"

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

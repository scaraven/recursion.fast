#!/usr/bin/env bash
# S7 review probes (docs/reviews/S7-review.md). Logs go to logs/S7-review/.
#
#   probes/s7/run.sh ORG MANIFEST
#
# ORG: an organiser package built by scripts/org-build.sh (with its `gate`), MANIFEST its olean
# manifest (scripts/olean-manifest.py gen --org ORG MANIFEST). Scratch work is in a temp dir.
set -euo pipefail
ORG=$(cd "${1:?usage: run.sh ORG MANIFEST}" && pwd); MANIFEST=$(realpath "${2:?}")
HERE=$(cd "$(dirname "$0")" && pwd); C=$(cd "$HERE/../.." && pwd); L=$C/logs/S7-review; mkdir -p "$L"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
LP=$(cd "$ORG" && lake env printenv LEAN_PATH 2>/dev/null)
GATE=$ORG/.lake/build/bin/gate

echo "== 1. baseline probes (eps, fuel split, class, S7-A1 prototype, axioms of every theorem)"
(cd "$C" && lake env lean probes/s7/Baseline.lean) 2>&1 | tee "$L/baseline-probes.log"

echo "== 2. IR forgery, Lean only: kernel says vk 1 = false, the executable prints true"
mkdir -p "$T/irforge"; cp "$HERE"/irforge/{IrForge.lean,Main.lean,lakefile.toml,lean-toolchain} "$T/irforge/"
(cd "$T/irforge" && lake build irforge > build.log 2>&1 && ./.lake/build/bin/irforge
 python3 -I "$C/scripts/olean-manifest.py" gen --org . --packages '' --prefix NoSuchPrefix man.sha256 > /dev/null
 LEAN_PATH=$(lake env printenv LEAN_PATH) "$GATE" IrForge vk_one --manifest man.sha256 --computable vk) \
  2>&1 | tee "$L/irforge.log"

run_gate() {  # FILE MODULE THEOREM COMPUTABLE
  mkdir -p "$T/$2"; cp "$HERE/$1" "$T/$2/$2.lean"; cp "$ORG/lean-toolchain" "$T/$2/"
  (cd "$T/$2" && LEAN_PATH=$LP lean -o "$2.olean" -c "$2.c" "$2.lean" &&
   LEAN_PATH=$T/$2:$LP "$GATE" "$2" "$3" --manifest "$MANIFEST" ${4:+--computable $4}) || true
}
echo "== 3. forged verify in a v2 Submission: the v2 gate PASSES; the emitted C of dec calls acceptAll"
run_gate ForgeGate.lean S7Forge S7Forge.certified S7Forge.submission 2>&1 | tee "$L/forge-gate.log"
grep -A6 '^LEAN_EXPORT uint8_t l_S7Forge_dec(' "$T/S7Forge/S7Forge.c" | tee -a "$L/forge-gate.log"
echo "== 4. v0.3 SpoofCert analogue (implemented_by in the contract's namespace): REJECT"
run_gate SpoofNs.lean SpoofNs RecursionFast.Contract.Spoof.submission "" 2>&1 | tee "$L/spoof-gate.log"
echo "== 5. noncomputable eps: the gate checks badge-path fields one by one: PASS"
run_gate EpsGate.lean EpsGate S7Eps.certified S7Eps.submission 2>&1 | tee "$L/eps-gate.log"
echo "== 6. a non-module submission file registers a @[cpass] (not covered by gate rule 3)"
mkdir -p "$T/cp"; cp "$HERE/CpassRegister.lean" "$T/cp/Cp.lean"; cp "$ORG/lean-toolchain" "$T/cp/"
(cd "$T/cp" && lean -o Cp.olean Cp.lean && echo "Cp.olean written: @[cpass] accepted") 2>&1 | tee "$L/cpass.log"
echo "== 7. recursion (structural, well-founded) passes the gate; the kernel cannot evaluate the wf one"
mkdir -p "$T/wf"; cp "$HERE/WfRec.lean" "$T/wf/"; cp "$ORG/lean-toolchain" "$T/wf/"
(cd "$T/wf" && lean -o WfRec.olean WfRec.lean &&
 LEAN_PATH=$T/wf:$(lean --print-prefix)/lib/lean "$GATE" WfRec wf_ok --manifest "$T/irforge/man.sha256" --computable lg2,sumTo) \
  2>&1 | tee "$L/wfrec.log"

#!/usr/bin/env bash
# Full CI pass (v0.3 + round-3 fixes, A6, + round-4 fixes, A7-M2/M3). ORDER MATTERS (A6-G0, RESULT.md "Round-3 fixes"):
#   1-6  organiser-only steps, in a separate organiser package ($CI_ORG, default .lake/org;
#        scripts/org-build.sh) that never holds a solution, a rendered challenge or a probe;
#        its trusted .oleans are checked against the committed hash manifest;
#   7    the toy solution through the production harness (scripts/harness.sh): comparator FIRST in a
#        fresh tree (bwrap sandbox, organiser package read-only, manifest checked before and after),
#        then the gate in a second fresh tree; negative toy rejected;
#   8    A4 gate probes, compiled in a scratch directory (never in the organiser package); A7-M2 gate
#        rule 4 probes (ε := errorCap passes, a noncomputable indexer or VK is rejected);
#   9    pipeline regressions: A6 cmpproj (G0, scenario B must be rejected), gateproj (G1/G2),
#        A7 bindproj (M3: the gate tree's build must equal the comparator-verified build);
#   10   manifest re-check of the organiser package.
#   scripts/ci.sh [RISCV_ZKVM_CHECKOUT]
set -euo pipefail
cd "$(dirname "$0")/.."
HERE=$PWD
ORG=${CI_ORG:-$HERE/.lake/org}
MAN=$HERE/scripts/olean-manifest.sha256
mkdir -p logs/v03
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
step() { echo "== [${SECONDS}s] $*"; }

step "1 source checks (vendor, hygiene lint)"
scripts/check-vendor.sh "$@"
scripts/check-hygiene.sh          # text lint only (defense in depth); the gate below is binding

step "2 organiser build in $ORG"
scripts/org-build.sh "$ORG"

step "3 organiser .olean manifest"
python3 -I scripts/olean-manifest.py check --org "$ORG" "$MAN" | tee logs/v03/manifest.log

step "4 axiom audit, line counts"
(cd "$ORG" && lake env .lake/build/bin/axiomaudit) | tee logs/v03/axioms.log
python3 scripts/loc.py RecursionFast/Contract.lean RecursionFast/Contract/*.lean | tee logs/v03/loc-contract.log

step "5 score-function probes (A4 coercions, A6-P1 leaf pricing)"
(cd "$ORG" && lake env lean "$HERE/probes/a4/Coercions.lean" && lake env lean "$HERE/probes/a6/Pricing.lean") \
  | tee logs/v03/pricing.log

step "6 renderer tests (A4-F5, A6-R1) and stubs"
scripts/test-render.sh | tee logs/v03/render-tests.log
for t in T0 T1 T2 L1; do
  python3 scripts/dummy-claim.py RecursionFast/Challenge/$t.lean.in "$T/$t.json"
  python3 scripts/render-challenge.py RecursionFast/Challenge/$t.lean.in "$T/$t.json" "$T/$t.lean"
  if (cd "$ORG" && lake env lean "$T/$t.lean") 2>&1 | grep -v "declaration uses .sorry."; then echo "stub $t FAILED"; exit 1; fi
  echo "stub $t elaborates"
done

step "7 toy through the production harness (comparator first, fresh trees, sandbox)"
python3 scripts/render-challenge.py RecursionFast/Challenge/Toy.lean.in audit/toy-claim.json "$T/ToyChallenge.lean"
cmp -s "$T/ToyChallenge.lean" audit/ToyChallenge.lean || { echo "audit/ToyChallenge.lean is stale"; exit 1; }
mkdir -p "$T/toysol" "$T/toybad"; cp audit/ToySolution.lean "$T/toysol/"; cp audit/ToySolutionBad.lean "$T/toybad/"
scripts/harness.sh --org "$ORG" --work "$T/h-toy" --gate RecursionFast.Challenge.certified \
  --computable RecursionFast.Challenge.protocol "$T/ToyChallenge.lean" "$T/toysol" audit/comparator-nanoda.json \
  | tee logs/v03/harness-toy.log
grep -q "nanoda kernel accepts" logs/v03/harness-toy.log
grep -q "Lean default kernel accepts" logs/v03/harness-toy.log
grep -q "gate tree build = comparator-verified build" logs/v03/harness-toy.log   # A7-M3 binding (determinism)
grep -q "gate: PASS" logs/v03/harness-toy.log
grep -q "HARNESS: ACCEPT" logs/v03/harness-toy.log
if scripts/harness.sh --org "$ORG" --work "$T/h-bad" "$T/ToyChallenge.lean" "$T/toybad" audit/comparator-bad.json \
    > logs/v03/harness-toy-negative.log 2>&1; then echo "negative toy ACCEPTED"; exit 1; fi
grep -q "Const does not match" logs/v03/harness-toy-negative.log
echo "negative toy rejected: $(grep -h "Const does not match\|HARNESS:" logs/v03/harness-toy-negative.log | tr '\n' ' ')"

step "8 gate on the A4 and A7-M2 probes (scratch directory; trust by content hash)"
A4=$T/a4; SP=$T/spoofroot; mkdir -p "$A4" "$SP/RecursionFast"
# the spoof root: byte copies of the contract and vendored .oleans (trusted by hash wherever they
# lie) plus a solution module named RecursionFast.Contract.Spoof (not in the manifest: untrusted)
cp -r "$ORG/.lake/build/lib/lean/RecursionFast/Contract" "$ORG/.lake/build/lib/lean/RecursionFast/Contract.olean" "$SP/RecursionFast/"
cp -r "$ORG/.lake/build/lib/lean/RiscvZkvm" "$SP/"
gp() { (cd "$ORG" && lake env bash -c "LEAN_PATH=$A4:\$LEAN_PATH $*"); }
gps() { (cd "$ORG" && lake env bash -c "LEAN_PATH=$SP:$A4:\$LEAN_PATH $*"); }   # spoof root first
for p in GateBypass UnboundImage HygieneBypass SkipKernel; do  # (they elaborate with warnings)
  gp lean --root="$HERE/probes/a4" -o "$A4/$p.olean" "$HERE/probes/a4/$p.lean" > /dev/null 2>&1 || true
  [[ -f "$A4/$p.olean" ]] || { echo "probe $p did not compile"; exit 1; }
done
gps lean --root="$HERE/probes/a4/spoof" -o "$SP/RecursionFast/Contract/Spoof.olean" \
  "$HERE/probes/a4/spoof/RecursionFast/Contract/Spoof.lean"
gps lean --root="$HERE/probes/a4" -o "$A4/SpoofCert.olean" "$HERE/probes/a4/SpoofCert.lean"
for p in SpoofCert GateBypass UnboundImage HygieneBypass; do
  g=gp; [[ $p == SpoofCert ]] && g=gps
  if $g .lake/build/bin/gate $p cert --manifest "$MAN" > "$T/gate-$p.log"; then cat "$T/gate-$p.log"; echo "gate ACCEPTED probe $p"; exit 1; fi
  grep -q "gate: REJECT" "$T/gate-$p.log" || { cat "$T/gate-$p.log"; echo "gate failed on $p without a verdict"; exit 1; }
  echo "probe $p: $(grep REJECT "$T/gate-$p.log" | head -2 | tr '\n' ' ')"
done | tee logs/v03/gate-probes.log
if gp leanchecker SkipKernel > /dev/null 2>&1; then echo "leanchecker ACCEPTED SkipKernel"; exit 1; fi
echo "A4 probes: all rejected (SkipKernel by leanchecker)"
# A7-M2: rule 4 constrains only the badge-path fields (VK, IDX, prover, extractor)
gp lean --root="$HERE/probes/a7/m2" -o "$A4/M2Err.olean" "$HERE/probes/a7/m2/M2Err.lean"
{
  gp .lake/build/bin/gate M2Err M2.cert --manifest "$MAN" --computable M2.submission,M2.toyErr,M2.accErr > "$T/m2-pos.log" \
    || { cat "$T/m2-pos.log"; echo "gate REJECTED the errorCap probes (A7-M2 regression)"; exit 1; }
  grep -q "gate: PASS" "$T/m2-pos.log"
  echo "M2 positive (ε := errorCap; Submission1, Protocol, Accumulation): PASS, $(grep -c ': compiled code$' "$T/m2-pos.log") badge-path fields compiled"
  for n in submissionBadIdx:'M2.submissionBadIdx.protocol\[[0-2]\].IDX' toyBadVK:'M2.toyBadVK.VK'; do
    c=${n%%:*} pat=${n#*:}
    if gp .lake/build/bin/gate M2Err M2.cert --manifest "$MAN" --computable M2.$c > "$T/m2-$c.log"; then cat "$T/m2-$c.log"; echo "gate ACCEPTED M2.$c"; exit 1; fi
    grep REJECT "$T/m2-$c.log" | grep -qv -- "$pat" && { cat "$T/m2-$c.log"; echo "M2.$c: unexpected rejection"; exit 1; }
    grep -q -- "REJECT $pat" "$T/m2-$c.log" || { cat "$T/m2-$c.log"; echo "M2.$c: not rejected at $pat"; exit 1; }
    echo "M2 negative $c: $(grep REJECT "$T/m2-$c.log" | head -1)"
  done
} | tee logs/v03/gate-m2.log

step "9 pipeline regressions (A6-G0 cmpproj, A6-G1/G2 gateproj, A7-M3 bindproj)"
tests/pipeline/cmpproj.sh | tee logs/v03/regress-cmpproj.log
tests/pipeline/gateproj.sh "$ORG/.lake/build/bin/gate" | tee logs/v03/regress-gateproj.log
tests/pipeline/bindproj.sh "$ORG/.lake/build/bin/gate" | tee logs/v03/regress-bindproj.log

step "10 organiser .olean manifest re-check"
python3 -I scripts/olean-manifest.py check --org "$ORG" "$MAN"
step "CI OK"

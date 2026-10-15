#!/usr/bin/env bash
# Full CI pass of the v2 contract and harness (Stage 6b; carried over from v0.3 with the round-3
# and round-4 fixes, A6-G0/G1/G2, A7-M2/M3). ORDER MATTERS (A6-G0): steps 2-6 are organiser-only,
# in a separate organiser package ($CI_ORG, default .lake/org; scripts/org-build.sh) that never
# holds a solution, a rendered challenge or a probe; its trusted .oleans are checked against the
# committed hash manifest before and after everything that runs solution-like code.
#   1   source checks: vendored Rv64 byte-identical, hygiene lint (text only; the gate is binding),
#       the source rule's fixtures (tests/source-rule/: each rejected form reported, the allowed pass)
#   2   organiser build (contract, library, controls, bridge, gate, axiomaudit, harness driver,
#       harness-linkcheck: built, which prebuilds the badge executables' object files, and run)
#   3   organiser .olean manifest
#   4   axiom audit, trusted line budget
#   5   reference tests: BLAKE2s against hashlib (probes/s2/Diff.lean, 8,432 cases), L_chain against
#       its Python oracle at n = 16 (harness/check-chain.py experiments), the benchmark runner's
#       self-test (its statement tree against the kernel-checked treeKat/rootOK_xT)
#   6   renderer tests (malformed claims rejected), the L and R stubs elaborate (dummy claims, and R
#       with L_chain(16) as C), the indexer's layout reader = the renderer (probes/s6b/layout)
#   7   the v2 toy (audit/, board L) through the production harness: comparator first (Lean kernel
#       and nanoda, fresh tree, bwrap sandbox), gate, badge executables built in the gate tree and
#       run; the negative toy (one image word changed) rejected; the source rule (S6b-M3) passes the
#       toy and rejects ForgeRaw before any build; a claim that does not render the challenge is
#       rejected (S6b-M2); stage 3b's plumbing with the claim-derived configuration
#   8   gate probes in a scratch directory: v2 rule 4 (probes/s6b/gate/GateV2.lean: positives pass,
#       each negative rejected at exactly its field), the S7-M1 forgeries (rules 3, 6, 7; the forgery
#       does not elaborate within the allowed imports), the A4 probes (v2 ports), leanchecker
#   9   pipeline regressions: cmpproj (A6-G0), gateproj (A6-G1/G2), bindproj (A7-M3)
#   10  badge path smoke test on the NOT SECURE cmpToy (O-10): verify/index built sandboxed against
#       harness/smoke, the benchmark runner end to end (64 leaves, 63 steps, 3 repeats), and its
#       rejections (S5-A13 digests, a bad proof, a timeout, no proof, the board-L cap; fix pass: no
#       sandbox (S6b-M1), a layout file not the claimed one (S6b-M2), the cgroup memory cap
#       (S6b-m1)) and the minimal sandbox root (S6b-m3)
#   11  the Clean frontend (S8-A12), in the repository tree, never in the organiser package, and the
#       axiom audit of RecursionFast.Clean*
#   12  organiser .olean manifest re-check
# Concurrency (wall time; the steps and their checks are unchanged): steps 5 and 6 run as concurrent
# jobs after step 4; steps 7, 8, 9 and step 10's executable builds run as concurrent jobs after
# them (each harness run keeps its own order, A6-G0). Jobs write disjoint paths of $T and $LOG and
# only read the organiser package; their outputs are replayed in step order, each with its wall
# time. Step 10's timed benchmark run starts after every job has ended and runs alone.
#
#   scripts/ci.sh [RISCV_ZKVM_CHECKOUT]
# Environment: COMPARATOR_HOME, COMPARATOR_NANODA (scripts/harness.sh; the local defaults below
# are this machine's read-only checkouts), CI_ORG. Logs: logs/S6b/ci/.
set -euo pipefail
cd "$(dirname "$0")/.."
HERE=$PWD
ORG=${CI_ORG:-$HERE/.lake/org}
MAN=$HERE/scripts/olean-manifest.sha256
AL=$HERE/scripts/import-allowlist.txt; FR=$HERE/scripts/import-frontend.txt
export COMPARATOR_HOME=${COMPARATOR_HOME:-/home/devops/CambridgePQ/recursion.fast/contract/tools/comparator}
export COMPARATOR_NANODA=${COMPARATOR_NANODA:-/home/devops/CambridgePQ/recursion.fast/contract-v03/tools/ext/nanoda_lib/target/release/nanoda_bin}
LOG=$HERE/logs/S6b/ci; mkdir -p "$LOG"
T=$(mktemp -d); trap 'wait; rm -rf "$T"' EXIT
step() { echo "== [${SECONDS}s] $*"; }
titled() { step "$1"; "${@:2}"; }
# `job NAME CMD...`: CMD in the background, its output in $T/job-NAME.out, then its wall time.
# `join NAME...`: wait for each job, replay its output in the order given; fail if any failed.
declare -A PID
job() { local n=$1; shift; { local t0=$SECONDS; "$@"; echo "-- $n: $((SECONDS - t0)) s"; } > "$T/job-$n.out" 2>&1 & PID[$n]=$!; }
join() {
  local n bad=""
  for n; do wait "${PID[$n]}" || bad="$bad $n"; cat "$T/job-$n.out"; done
  [[ -z $bad ]] || { echo "CI FAILED:$bad"; exit 1; }
}

step "1 source checks (vendor, hygiene lint, source-rule fixtures)"
scripts/check-vendor.sh "$@" > "$LOG/vendor.log"; tail -1 "$LOG/vendor.log"
scripts/check-hygiene.sh | tee "$LOG/hygiene.log"
tests/source-rule/check.sh | tee "$LOG/source-rule.log"

step "2 organiser build in $ORG"
scripts/org-build.sh "$ORG" | tee "$LOG/org-build.log"

step "3 organiser .olean manifest; the gate's import allowlist (rule 6) is current"
python3 -I scripts/olean-manifest.py check --org "$ORG" "$MAN" | tee "$LOG/manifest.log"
for f in import-allowlist import-frontend; do
  cmp -s "$ORG/$f.txt" "scripts/$f.txt" || { echo "scripts/$f.txt is stale (cp $ORG/$f.txt)"; exit 1; }
done
echo "import allowlist: $(wc -l < "$AL") modules; frontend (Clean) list: $(wc -l < "$FR") modules; current"

step "4 axiom audit, line counts"
(cd "$ORG" && lake env .lake/build/bin/axiomaudit) > "$LOG/axioms.log" 2>&1 || { tail -20 "$LOG/axioms.log"; exit 1; }
grep -v "manifest out of date" "$LOG/axioms.log" | tail -3
python3 -I scripts/loc.py RecursionFast/Contract.lean RecursionFast/Contract/*.lean > "$LOG/loc-contract.log"
tail -1 "$LOG/loc-contract.log"

# ---- steps 5, 6 (organiser-only), concurrent ------------------------------------------------
reference_tests() {
  (cd "$ORG" && lake env lean --run "$HERE/probes/s2/Diff.lean") > "$T/b2s-diff.out" 2> "$LOG/b2s-diff.err"
  python3 -I probes/s2/diff.py "$T/b2s-diff.out" | tee "$LOG/b2s-diff.log"
  : > "$LOG/check-chain-n16.log"   # check-chain.py appends to its log
  python3 -I harness/check-chain.py experiments --gen harness/gen-chain-layout.py --dir "$T/chain" --n 16 \
    --seeds 1 --mutations 50 --log "$LOG/check-chain-n16.log" > /dev/null
  grep -h "^(c) 8 mutants\|^(b)" "$LOG/check-chain-n16.log" | cut -c1-140
  python3 -I harness/run-benchmark.py selftest --lean-data RecursionFast/Controls/RecursionData.lean \
    --gen harness/gen-chain-layout.py | tee "$LOG/runner-selftest.log"
}
render_tests() {
  scripts/test-render.sh "$T/render" > "$LOG/render-tests.log"; tail -1 "$LOG/render-tests.log"
  echo "render: $(grep -c ' rejected' "$LOG/render-tests.log") malformed claims rejected"
  for s in L R Rchain; do
    (cd "$ORG" && lake env lean "$T/render/$s.lean") > "$T/stub-$s.log" 2>&1 || { cat "$T/stub-$s.log"; echo "stub $s FAILED"; exit 1; }
    if grep -v "declaration uses .sorry.\|manifest out of date" "$T/stub-$s.log"; then echo "stub $s: unexpected output"; exit 1; fi
    echo "stub $s elaborates (only the sorry placeholders)"
  done | tee "$LOG/stubs.log"
}
layout_check() { probes/s6b/layout/check.sh "$ORG" | tee "$LOG/layout-check.log"; }
job 5 titled "5 reference tests (BLAKE2s vs hashlib, L_chain vs its oracle at n = 16, runner self-test)" reference_tests
job 6-render titled "6 renderer tests and stubs (L, R; R with L_chain(16)); layout reader = renderer" render_tests
job 6-layout layout_check
join 5 6-render 6-layout

# ---- steps 7, 8, 9 and step 10's builds (solution-like code), concurrent ----------------------
step "7 the v2 toy through the production harness (comparator first, fresh trees, sandbox, gate, badge build)"
python3 -I scripts/toy-solution.py "$T/toy"
for f in ToyChallenge.lean ToySolution.lean ToySolutionBad.lean toy-claim.json; do
  cmp -s "$T/toy/$f" "audit/$f" || { echo "audit/$f is stale (python3 -I scripts/toy-solution.py)"; exit 1; }
done
mkdir -p "$T/toysol" "$T/toybad"; cp audit/ToySolution.lean "$T/toysol/"; cp audit/ToySolutionBad.lean "$T/toybad/"
TOY=(--gate RecursionFast.Challenge.certified --computable RecursionFast.Challenge.submission
     --badge-build RecursionFast.Challenge.submission)
toy() {
  scripts/harness.sh --org "$ORG" --work "$T/h-toy" "${TOY[@]}" audit/ToyChallenge.lean "$T/toysol" \
    audit/comparator-nanoda.json > "$LOG/harness-toy.log" 2>&1 || { tail -30 "$LOG/harness-toy.log"; exit 1; }
  for p in "nanoda kernel accepts" "Lean default kernel accepts" "gate tree build = comparator-verified build" \
           "gate: badge-root-module ToySolution" "gate: PASS" "badge executables built" "HARNESS: ACCEPT"; do
    grep -q "$p" "$LOG/harness-toy.log" || { tail -30 "$LOG/harness-toy.log"; echo "harness toy: missing '$p'"; exit 1; }
  done
  grep -h "TIME\|gate: rule 4\|gate tree build\|badge executables\|HARNESS" "$LOG/harness-toy.log"
  # the gate tree's verify (the toy's NARG) on a random key and tape: rejects, in its own process
  head -c 40 /dev/urandom > "$T/vk"; head -c 256 /dev/urandom > "$T/x"; head -c 100 /dev/urandom > "$T/t"
  local rc=0; "$T/h-toy/tree/.lake/build/bin/harness-verify" "$T/vk" "$T/x" "$T/t" > /dev/null || rc=$?
  [[ $rc -eq 1 ]] || { echo "gate-tree harness-verify: expected REJECT (1), got $rc"; exit 1; }
  echo "gate-tree harness-verify on a random tape: REJECT (exit 1)"
}
# stage 3b plumbing: the toy cannot be indexed (oracles of 2^28 elements, O-10), so a benchmark run
# with a 5 s indexing budget must end in a REJECT from the runner, reported by the harness
toy_bench() {
  python3 -I -c 'import json, sys
here = sys.argv[2]
json.dump({"k": 24, "boards": ["L"], "prover": ["python3", "-I", here + "/harness/smoke/toy_prover.py"],
           "gen": here + "/harness/gen-chain-layout.py", "sandbox": here + "/scripts/bwrap-landrun.sh",
           "tree": {"n": 16, "leaves": 2}, "leafboard": {}, "classes": {"16": 20}, "repeats": 1,
           "dos": {"tapes": 0}, "budgets": {"index_total_s": 5}}, open(sys.argv[1], "w"))' "$T/toy-bench.json" "$HERE"
  python3 -I harness/run-benchmark.py secrets 2 "$T/toy-secrets.txt"
  if scripts/harness.sh --org "$ORG" --work "$T/h-bench" "${TOY[@]}" --bench "$T/toy-bench.json" --secrets "$T/toy-secrets.txt" \
      --claim "$T/toy/toy-claim.json" --stub RecursionFast/Challenge/L.lean.in \
      audit/ToyChallenge.lean "$T/toysol" audit/comparator.json > "$LOG/harness-toy-bench.log" 2>&1; then
    tail -20 "$LOG/harness-toy-bench.log"; echo "harness --bench ACCEPTED the infeasible toy"; exit 1; fi
  grep -q "HARNESS: REJECT (benchmark: index L_chain(16): timeout" "$LOG/harness-toy-bench.log" \
    || { tail -20 "$LOG/harness-toy-bench.log"; echo "harness --bench: not rejected by the indexing budget"; exit 1; }
  echo "harness stage 3b (toy, 5 s indexing budget): $(grep -h 'HARNESS:' "$LOG/harness-toy-bench.log")"
  # S6b-M2: the challenge must be the stub rendered with the claim the benchmark reads
  mkdir -p "$T/badclaim"; cp "$T/toy/firstmsg.code" "$T/toy/firstmsg.data" "$T/badclaim/"
  python3 -I -c 'import json, sys; d = json.load(open(sys.argv[1])); d["arity"] = 4; json.dump(d, open(sys.argv[2], "w"))' \
    "$T/toy/toy-claim.json" "$T/badclaim/claim.json"
  if scripts/harness.sh --org "$ORG" --work "$T/h-claim" "${TOY[@]}" --bench "$T/toy-bench.json" --secrets "$T/toy-secrets.txt" \
      --claim "$T/badclaim/claim.json" --stub RecursionFast/Challenge/L.lean.in \
      audit/ToyChallenge.lean "$T/toysol" audit/comparator.json > "$LOG/harness-claim-mismatch.log" 2>&1; then
    echo "harness ACCEPTED a claim that does not render the challenge"; exit 1; fi
  grep -q "HARNESS: REJECT (the challenge is not the rendering of the stub with the claim)" "$LOG/harness-claim-mismatch.log" \
    || { tail -10 "$LOG/harness-claim-mismatch.log"; exit 1; }
  echo "harness rejects a claim that does not render the challenge (S6b-M2): $(grep -h 'HARNESS:' "$LOG/harness-claim-mismatch.log")"
  # S6b-M3: ForgeRaw (the raw forgery, which the gate passes) is rejected by the source rule before any build
  mkdir -p "$T/forgeraw"; cp probes/s6b/gate/ForgeRaw.lean "$T/forgeraw/"
  python3 -I -c 'import json, sys; d = json.load(open(sys.argv[1])); d["solution_module"] = "ForgeRaw"; json.dump(d, open(sys.argv[2], "w"))' \
    audit/comparator.json "$T/forgeraw.json"
  if scripts/harness.sh --org "$ORG" --work "$T/h-raw" "${TOY[@]}" audit/ToyChallenge.lean "$T/forgeraw" "$T/forgeraw.json" \
      > "$LOG/harness-forgeraw.log" 2>&1; then echo "harness ACCEPTED ForgeRaw"; exit 1; fi
  grep -q "HARNESS: REJECT (source rule: 1 files, [0-9]* finding(s))" "$LOG/harness-forgeraw.log" \
    || { tail -12 "$LOG/harness-forgeraw.log"; echo "ForgeRaw: not rejected by the source rule"; exit 1; }
  ! grep -q "^TIME \|Exporting\|Building" "$LOG/harness-forgeraw.log" || { echo "ForgeRaw: something was built before the source rule"; exit 1; }
  echo "harness rejects ForgeRaw by the source rule before any build (S6b-M3): $(grep -h 'source-rule: ForgeRaw' "$LOG/harness-forgeraw.log" | sed 's/source-rule: ForgeRaw.lean://' | tr '\n' ' ')"
}
toy_bad() {
  if scripts/harness.sh --org "$ORG" --work "$T/h-bad" audit/ToyChallenge.lean "$T/toybad" audit/comparator-bad.json \
      > "$LOG/harness-toy-negative.log" 2>&1; then echo "negative toy ACCEPTED"; exit 1; fi
  grep -q "Const does not match" "$LOG/harness-toy-negative.log"
  echo "negative toy rejected: $(grep -h "Const does not match\|HARNESS:" "$LOG/harness-toy-negative.log" | tr '\n' ' ')"
}

# step 8: probes compiled into the scratch directory $A4 (LEAN_PATH), the gate run on them
A4=$T/a4; SP=$T/spoofroot; G=$HERE/probes/s6b/gate; P4=$G/a4; mkdir -p "$A4/GClean" "$SP/RecursionFast"
GA=(--manifest "$MAN" --allowed-imports "$AL" --frontend-imports "$FR")
gp() { (cd "$ORG" && lake env bash -c "LEAN_PATH=$A4:\$LEAN_PATH $*"); }
gps() { (cd "$ORG" && lake env bash -c "LEAN_PATH=$SP:$A4:\$LEAN_PATH $*"); }   # spoof root first
olean() { ${GP:-gp} lean --root="$1" -o "$2" "${@:3}" 2>&1 | grep -v "manifest out of date\|declaration uses .sorry." || true; }
# gate_rejects LOG PATTERN ARGS...: the gate (run by ${GP:-gp}) rejects ARGS, with a line `REJECT PATTERN`
gate_rejects() {
  local log=$1 pat=$2; shift 2
  if ${GP:-gp} .lake/build/bin/gate "$@" > "$log" 2>&1; then cat "$log"; echo "gate ACCEPTED $*"; exit 1; fi
  grep -q -- "REJECT $pat" "$log" || { cat "$log"; echo "gate on $*: not rejected for: $pat"; exit 1; }
}
gate_a4() {
  # the spoof root: byte copies of the contract and vendored .oleans (trusted by hash wherever they
  # lie) plus a solution module named RecursionFast.Contract.Spoof (not in the manifest: untrusted)
  cp -r "$ORG/.lake/build/lib/lean/RecursionFast/Contract" "$ORG/.lake/build/lib/lean/RecursionFast/Contract.olean" "$SP/RecursionFast/"
  cp -r "$ORG/.lake/build/lib/lean/RiscvZkvm" "$SP/"
  for p in GateBypass UnboundImage HygieneBypass SkipKernel; do  # (they elaborate with warnings)
    gp lean --root="$P4" -o "$A4/$p.olean" "$P4/$p.lean" > /dev/null 2>&1 || true
    [[ -f "$A4/$p.olean" ]] || { echo "probe $p did not compile"; exit 1; }
  done
  GP=gps olean "$P4/spoof" "$SP/RecursionFast/Contract/Spoof.olean" "$P4/spoof/RecursionFast/Contract/Spoof.lean"
  GP=gps olean "$P4" "$A4/SpoofCert.olean" "$P4/SpoofCert.lean"
  for p in SpoofCert GateBypass UnboundImage HygieneBypass; do
    GP=gp; [[ $p != SpoofCert ]] || GP=gps
    gate_rejects "$T/gate-$p.log" "" $p cert --manifest "$MAN"
    echo "probe $p: $(grep REJECT "$T/gate-$p.log" | head -2 | tr '\n' ' ')"
  done | tee "$LOG/gate-a4.log"
  if gp leanchecker SkipKernel > /dev/null 2>&1; then echo "leanchecker ACCEPTED SkipKernel"; exit 1; fi
  echo "A4 probes: all rejected (SkipKernel by leanchecker)" | tee -a "$LOG/gate-a4.log"
}
# v2 rule 4 (S5-A9): only the badge-path fields must have compiled code
gate_v2() {
  olean "$G" "$A4/GateV2.olean" "$G/GateV2.lean"
  local V=(GateV2 GateV2.cert "${GA[@]}") pos=GateV2.submission,GateV2.submissionNcProver,GateV2.submissionNcFuel,GateV2.submissionR
  {
    gp .lake/build/bin/gate "${V[@]}" --computable $pos > "$T/v2-pos.log" 2>&1 \
      || { cat "$T/v2-pos.log"; echo "gate REJECTED the v2 positives (errorCap, noncomputable prover / fuel, board R)"; exit 1; }
    grep -q "gate: PASS" "$T/v2-pos.log"
    echo "v2 rule 4 positive ($pos): PASS, $(grep -c ': compiled code$' "$T/v2-pos.log") badge-path fields compiled"
    for n in submissionBadIdx:'GateV2.submissionBadIdx.P.IDX' submissionBadVK:'GateV2.submissionBadVK.P.VK' \
             submissionBadVerify:'GateV2.submissionBadVerify.P.verify' submissionBadImg:'GateV2.submissionBadImg.P.extractor.img' \
             submissionRBadDecode:'GateV2.submissionRBadDecode.entry.decode' submissionRBadC:'GateV2.submissionRBadC.entry.C'; do
      local c=${n%%:*} pat=${n#*:}
      gate_rejects "$T/v2-$c.log" "$pat" "${V[@]}" --computable GateV2.$c
      grep REJECT "$T/v2-$c.log" | grep -qv -- "$pat" && { cat "$T/v2-$c.log"; echo "GateV2.$c: unexpected rejection"; exit 1; }
      echo "v2 rule 4 negative $c: $(grep REJECT "$T/v2-$c.log" | head -1)"
    done
  } | tee "$LOG/gate-v2.log"
}
# S7-M1: an elaboration-time metaprogram overwrites a definition's emitted code (no attribute), and
# a compiler-pass installer; both rejected (rules 6 and 3, 6, 7); within the allowed imports the
# forgery does not elaborate
gate_s7() {
  for p in Forge Cpass; do olean "$G" "$A4/$p.olean" "$G/$p.lean"; done
  {
    for c in "Forge|S7Forge.certified|S7Forge.submission|module Forge imports Lean" \
             "Cpass|cert||module Cpass: @\[cpass\] on noopInstaller" "Cpass|cert||module Cpass imports Lean" \
             "Cpass|cert||module Cpass: noopInstaller refers to the compiler/environment API"; do
      IFS='|' read -r mod thm comp pat <<< "$c"
      gate_rejects "$T/s7-$mod.log" "$pat" "$mod" "$thm" "${GA[@]}" ${comp:+--computable "$comp"}
      echo "S7-M1 $mod: $(grep -- "REJECT $pat" "$T/s7-$mod.log" | head -1)"
    done
    if gp lean "$G/ForgeNoLean.lean" > "$T/forge-nolean.log" 2>&1; then echo "ForgeNoLean ELABORATED (rule 6 does not keep the compiler out)"; exit 1; fi
    grep -q "Unknown identifier .impureExt.getState." "$T/forge-nolean.log" || { cat "$T/forge-nolean.log"; exit 1; }
    echo "S7-M1 ForgeNoLean: with Mathlib, the contract, the library and the controls only, impureExt is out of reach (Unknown identifier)"
    # S6b-M3: the raw route (persistentEnvExtensionsRef + unsafeCast, Mathlib-only imports) forges what
    # importers compile, and NO gate rule sees it (the gate PASSES it, as a badge root too); the
    # source rule rejects it (step 7, ForgeRaw through the harness)
    olean "$G" "$A4/ForgeRaw.olean" "$G/ForgeRaw.lean"
    olean "$G" "$A4/UseRaw.olean" -c "$T/UseRaw.c" "$G/UseRaw.lean"
    grep -A5 "^LEAN_EXPORT uint8_t l_useDec(lean_object\* v" "$T/UseRaw.c" | grep -q "l_List_beq.*(v_msg_[0-9]*_, v_msg_[0-9]*_)" \
      || { grep -A6 "^LEAN_EXPORT uint8_t l_useDec(" "$T/UseRaw.c"; echo "ForgeRaw: expected the importer to run acceptAll"; exit 1; }
    gp .lake/build/bin/gate ForgeRaw S7Raw.certified "${GA[@]}" --computable S7Raw.submission --badge-root S7Raw.submission \
      > "$T/forgeraw-gate.log" 2>&1 && grep -q "gate: PASS" "$T/forgeraw-gate.log" \
      || { cat "$T/forgeraw-gate.log"; echo "ForgeRaw: the gate was expected to PASS it (the residual it cannot see)"; exit 1; }
    echo "S6b-M3 ForgeRaw: forges its importer's code (useDec = msg == msg); the gate PASSES it (rules 1-9 cannot see a run_meta); only the source rule rejects it"
  } | tee "$LOG/gate-s7.log"
}
# S6b-A11: the Clean frontend for circuit proofs, never on the badge path (rules 6, 8, 9); after
# gate_v2, in its job (GClean.Core imports GateV2)
gate_clean() {
  local GC=$G/clean m C=(GClean GClean.cert "${GA[@]}")
  for m in GClean/Core GClean/Circuit GClean; do olean "$GC" "$A4/$m.olean" "$GC/$m.lean"; done
  {
    gp .lake/build/bin/gate "${C[@]}" --computable GClean.submissionR --badge-root GClean.leaf > "$T/gclean-pos.log" 2>&1 \
      || { cat "$T/gclean-pos.log"; echo "gate REJECTED the Clean positive"; exit 1; }
    grep -q "gate: badge-root-module GClean.Core" "$T/gclean-pos.log"; grep -q "gate: PASS" "$T/gclean-pos.log"
    echo "S6b-A11 positive (circuit proofs import Clean, leaf in a Clean-free module): PASS, badge root module GClean.Core"
    for c in "submissionBadDecode|GClean.leaf|GClean.submissionBadDecode.entry.decode: refers to frontend (Clean) code" \
             "submissionR|GClean.leafBad|badge root GClean.leafBad is declared in module GClean.Circuit"; do
      IFS='|' read -r sub root pat <<< "$c"
      gate_rejects "$T/gclean-$sub.log" "$pat" "${C[@]}" --computable "GClean.$sub" --badge-root "$root"
      echo "S6b-A11 negative: $(grep -- "REJECT $pat" "$T/gclean-$sub.log" | head -1 | cut -c1-160)"
    done
    # the forgery through Clean elaborates (Clean imports Lean) and its emitted code is forged; rule 8
    # rejects it as a badge root, so it is never linked into the badge executables
    olean "$G" "$A4/ForgeClean.olean" -c "$T/ForgeClean.c" "$G/ForgeClean.lean"
    grep -A4 "^LEAN_EXPORT uint8_t l_S7FC_dec(lean_object\* v" "$T/ForgeClean.c" | grep -q acceptAll \
      || { echo "ForgeClean: expected the forged C (dec calls acceptAll)"; exit 1; }
    gate_rejects "$T/forgeclean.log" "badge root S7FC.submission is declared in module ForgeClean" \
      ForgeClean S7FC.certified "${GA[@]}" --computable S7FC.submission --badge-root S7FC.submission
    echo "S6b-A11 ForgeClean: the forgery through Clean elaborates (C of dec calls acceptAll); rule 8 rejects it as a badge root"
  } | tee "$LOG/gate-clean.log"
}

# step 9: NAME [GATE]: one pipeline regression
regress() {
  tests/pipeline/$1.sh "${@:2}" > "$LOG/regress-$1.log" 2>&1 || { cat "$LOG/regress-$1.log"; exit 1; }
  tail -1 "$LOG/regress-$1.log"
}

# step 10, untimed part: the smoke executables (sandboxed builds)
B=$T/badge; BIN=$B/submission/tree/.lake/build/bin; KBIN=$B/keyed/tree/.lake/build/bin
smoke_build() {
  for e in verify index; do
    python3 -I harness/badge-main.py "$T/Smoke-$e.lean" RecursionFastSmoke RecursionFastSmoke.submission $e
    cmp -s "$T/Smoke-$e.lean" "harness/smoke/Smoke${e^}.lean" || { echo "harness/smoke/Smoke${e^}.lean is stale (harness/badge-main.py)"; exit 1; }
  done
  for v in submission keyed; do
    harness/badge-build.sh --org "$ORG" --work "$B/$v" harness/smoke RecursionFastSmoke RecursionFastSmoke.$v > /dev/null \
      || { tail -20 "$B/$v/badge-build.log"; exit 1; }
  done
  echo "smoke executables built (sandboxed, organiser package read-only): $BIN, $KBIN"
}

job 7-toy toy; job 7-bench toy_bench; job 7-bad toy_bad
job 8-a4 titled "8 gate probes (scratch directory; trust by content hash): v2 rule 4, A4 ports" gate_a4
job 8-v2 eval 'gate_v2; gate_clean'; job 8-s7 gate_s7
job 9-cmpproj titled "9 pipeline regressions (A6-G0 cmpproj, A6-G1/G2 gateproj, A7-M3 bindproj)" regress cmpproj
job 9-gateproj regress gateproj "$ORG/.lake/build/bin/gate"; job 9-bindproj regress bindproj "$ORG/.lake/build/bin/gate"
job 10-build titled "10 badge path smoke test (NOT SECURE cmpToy, O-10): executables, benchmark runner, rejections" smoke_build
join 7-toy 7-bench 7-bad 8-a4 8-v2 8-s7 9-cmpproj 9-gateproj 9-bindproj 10-build

# ---- step 10, timed: the benchmark run alone, then the runner's rejections ----------------------
step "10 (continued) the benchmark run (timed, alone) and the runner's rejections"
python3 -I harness/run-benchmark.py secrets 96 "$T/secrets.txt"
python3 -I harness/gen-chain-layout.py layout --n 1024 "$T/L1024.json" > /dev/null
D=$("$BIN/harness-index" harness/examples/chain-n16.layout.json "$T/vk-plain")
DK16=$("$KBIN/harness-index" harness/examples/chain-n16.layout.json "$T/vk-k16")
DK1024=$("$KBIN/harness-index" "$T/L1024.json" "$T/vk-k1024")
[[ "$DK16" != "$DK1024" ]] || { echo "keyed smoke protocol: L_chain(16) and L_chain(1024) have the same key"; exit 1; }
mkcfg() {  # out, verify-bin-dir, digestC, digestL, extra JSON (merged)
  python3 -I -c 'import json, sys
here, b, dc, dl, extra = sys.argv[2:7]
cfg = {"k": 26, "boards": ["L", "R"], "verify": [b + "/harness-verify"], "index": [b + "/harness-index"],
       "prover": ["python3", "-I", here + "/harness/smoke/toy_prover.py"], "gen": here + "/harness/gen-chain-layout.py",
       "layouts": {"C": here + "/harness/examples/chain-n16.layout.json"}, "claim": {"digestC": dc, "digestL": dl},
       "sandbox": here + "/scripts/bwrap-landrun.sh", "sandbox_ro": [here + "/harness/smoke"],
       "dos": {"tapes": 100, "max_len": 1048576}}
cfg.update(json.loads(extra))
json.dump(cfg, open(sys.argv[1], "w"), indent=1)' "$@"
}
mkcfg "$T/bench.json" "$HERE" "$BIN" "$D" "$D" '{}'
python3 -I harness/run-benchmark.py run --config "$T/bench.json" --secrets "$T/secrets.txt" --out "$LOG/bench-smoke.json" \
  --workdir "$T/bench" | tee "$LOG/bench-smoke.log"
SMALL='"tree": {"n": 16, "leaves": 2}, "leafboard": {}, "repeats": 1, "dos": {"tapes": 0}, "classes": {"8": 20, "16": 20, "32": 21, "1024": 24}'
python3 -I harness/run-benchmark.py secrets 2 "$T/secrets2.txt"
expect_reject() {  # name, pattern, config
  if python3 -I harness/run-benchmark.py run --config "$3" --secrets "$T/secrets2.txt" --out "$T/$1.json" --workdir "$T/bench" \
      > "$T/$1.log" 2>&1; then cat "$T/$1.log"; echo "runner ACCEPTED $1"; exit 1; fi
  grep -q -- "$2" "$T/$1.json" || { cat "$T/$1.log"; echo "runner $1: rejected, but not for: $2"; exit 1; }
  echo "runner rejects $1: $(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["reason"])' "$T/$1.json")"
}
{
  FLIP=$(python3 -I -c 'import sys; d = bytearray(bytes.fromhex(sys.argv[1])); d[0] ^= 1; print(d.hex())' "$D")
  mkcfg "$T/c1.json" "$HERE" "$BIN" "$FLIP" "$D" "{$SMALL, \"boards\": [\"R\"]}"
  expect_reject digestC-flipped "declared digestC" "$T/c1.json"
  # keyed: the claim's digestL is the key digest of L_chain(16), not of L_chain(2^10) (S5-A13)
  DKC=$("$KBIN/harness-index" harness/examples/chain-n16.layout.json "$T/vk-kc")
  mkcfg "$T/c2.json" "$HERE" "$KBIN" "$DKC" "$DK16" "{$SMALL, \"tree\": {\"n\": 1024, \"leaves\": 2}, \"boards\": [\"R\"]}"
  expect_reject digestL-of-Lchain16 "declared digestL" "$T/c2.json"
  mkcfg "$T/c2ok.json" "$HERE" "$KBIN" "$DKC" "$DK1024" "{$SMALL, \"tree\": {\"n\": 1024, \"leaves\": 2}, \"boards\": [\"R\"]}"
  python3 -I harness/run-benchmark.py run --config "$T/c2ok.json" --secrets "$T/secrets2.txt" --out "$T/c2ok.out.json" \
    --workdir "$T/bench" > "$T/c2ok.log" 2>&1 || { cat "$T/c2ok.log"; echo "keyed smoke with the right digests REJECTED"; exit 1; }
  echo "runner accepts the keyed smoke protocol with the indexer's digests of C_V and L_chain(2^10)"
  P='"prover": ["bash", "-c", "python3 -I '$HERE'/harness/smoke/toy_prover.py $0 && printf x >> proof.bin"]'
  mkcfg "$T/c3.json" "$HERE" "$BIN" "$D" "$D" "{$SMALL, $P}"
  expect_reject bad-proof "does not verify" "$T/c3.json"
  P='"prover": ["python3", "-I", "'$HERE'/harness/smoke/toy_prover.py", "--spin", "3"], "budgets": {"leaf_s": 1}'
  mkcfg "$T/c4.json" "$HERE" "$BIN" "$D" "$D" "{$SMALL, $P}"
  expect_reject timeout "timeout" "$T/c4.json"
  mkcfg "$T/c5.json" "$HERE" "$BIN" "$D" "$D" "{$SMALL, \"prover\": [\"true\"]}"
  expect_reject no-proof "wrote no proof.bin" "$T/c5.json"
  P='"prover": ["bash", "-c", "head -c 140000 /dev/zero > proof.bin"]'
  mkcfg "$T/c6.json" "$HERE" "$BIN" "$D" "$D" "{$SMALL, \"boards\": [\"L\"], $P}"
  expect_reject board-L-cap "above the board-L cap 131072" "$T/c6.json"
  # classes (S7-M2): a declared class below the benchmark layout's is rejected up front; a leaf-board
  # size above the declared class is skipped, not failed; a board-L failure leaves board R standing
  mkcfg "$T/c7.json" "$HERE" "$BIN" "$D" "$D" "{$SMALL, \"k\": 19}"
  expect_reject class-below "below the class 20" "$T/c7.json"
  cat > "$T/failsmall.py" <<PY
import subprocess, sys
x = open("stmt.bin", "rb").read(); n = int.from_bytes(x[32:40], "little")
if sys.argv[-1] == "leaf" and n == 8: sys.exit(3)
sys.exit(subprocess.run([sys.executable, "-I", "$HERE/harness/smoke/toy_prover.py", sys.argv[-1]]).returncode)
PY
  mkcfg "$T/c8.json" "$HERE" "$BIN" "$D" "$D" "{$SMALL, \"k\": 20, \"leafboard\": {\"8\": 2, \"32\": 2}, \"prover\": [\"python3\", \"-I\", \"$T/failsmall.py\"]}"
  python3 -I harness/run-benchmark.py run --config "$T/c8.json" --secrets "$T/secrets.txt" --out "$T/c8.out.json" \
    --workdir "$T/bench" > "$T/c8.log" 2>&1 || { cat "$T/c8.log"; echo "board separation: the run was rejected as a whole"; exit 1; }
  python3 -I -c 'import json, sys
r = json.load(open(sys.argv[1]))["scores"]
assert r["L"]["verdict"] == "REJECT" and r["R"]["verdict"] == "ACCEPT" and r["W"]["verdict"] == "ACCEPT", r
assert "32" in r["L"]["skipped"], r["L"]
print("runner: board L REJECT (" + r["L"]["reason"] + "), boards R and W ACCEPT; n = 32 skipped: " + r["L"]["skipped"]["32"])' "$T/c8.out.json"
  # fix pass. S6b-M1: no sandbox, no run
  mkcfg "$T/c9.json" "$HERE" "$BIN" "$D" "$D" "{$SMALL}"
  python3 -I -c 'import json, sys; d = json.load(open(sys.argv[1])); del d["sandbox"]; json.dump(d, open(sys.argv[1], "w"))' "$T/c9.json"
  expect_reject no-sandbox "no sandbox" "$T/c9.json"
  # S6b-M2: a layout file that is not the one the claim's digestC names (keyed: the key depends on it)
  mkcfg "$T/c10.json" "$HERE" "$KBIN" "$DKC" "$DK1024" "{$SMALL, \"tree\": {\"n\": 1024, \"leaves\": 2}, \"boards\": [\"R\"], \"layouts\": {\"C\": \"$HERE/harness/examples/chain-n1.layout.json\"}}"
  expect_reject layout-mismatch "declared digestC" "$T/c10.json"
  # S6b-m1: the step's cgroup caps the whole process tree (a 300 MB prover under a 150 MB cap)
  P='"prover": ["python3", "-c", "x = bytearray(300 * 2**20); x[::4096] = b\"1\" * len(x[::4096])"], "budgets": {"mem_kb": 150000}'
  mkcfg "$T/c11.json" "$HERE" "$BIN" "$D" "$D" "{$SMALL, $P}"
  expect_reject memory-cap "killed at the memory cap" "$T/c11.json"
  # S6b-m3: a step cannot read the repository (only /usr, /etc, its directory and the declared paths)
  P='"prover": ["bash", "-c", "test -r '$HERE'/CLAUDE.md && exit 7; python3 -I '$HERE'/harness/smoke/toy_prover.py $0"]'
  mkcfg "$T/c12.json" "$HERE" "$BIN" "$D" "$D" "{$SMALL, $P}"
  python3 -I harness/run-benchmark.py run --config "$T/c12.json" --secrets "$T/secrets2.txt" --out "$T/c12.out.json" \
    --workdir "$T/bench" > "$T/c12.log" 2>&1 || { cat "$T/c12.log"; echo "minimal root: a step could read the repository (or failed)"; exit 1; }
  echo "runner: a step cannot read the repository (minimal sandbox root, S6b-m3); the run is accepted"
} | tee "$LOG/bench-negatives.log"

step "11 Clean frontend (S8-A12; repository tree, never the organiser package)"
scripts/setup-clean.sh > "$LOG/clean-setup.log" 2>&1 || { cat "$LOG/clean-setup.log"; exit 1; }
lake build RecursionFastClean > "$LOG/clean-build.log" 2>&1 || { tail -20 "$LOG/clean-build.log"; exit 1; }
grep "Build completed successfully" "$LOG/clean-build.log"
lake env lean probes/s6b/AxiomAuditClean.lean 2>&1 | tee "$LOG/clean-axioms.log" | grep "axiom audit (Clean)"
if grep -q "error" "$LOG/clean-axioms.log"; then echo "Clean axiom audit FAILED"; exit 1; fi

step "12 organiser .olean manifest re-check"
python3 -I scripts/olean-manifest.py check --org "$ORG" "$MAN"
step "CI OK"

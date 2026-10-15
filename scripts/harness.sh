#!/usr/bin/env bash
# Production harness, in the required order (A6-G0; RESULT.md "Round-3 fixes", R3.1):
#
#   scripts/harness.sh [options] CHALLENGE.lean SOLUTION_DIR CONFIG.json
#
#   0. organiser build integrity: every trusted/pinned .olean (toolchain, Mathlib deps, pinned
#      packages, contract + vendored Rv64) matches the hash manifest (scripts/olean-manifest.py check).
#   1. COMPARATOR FIRST, in a FRESH tree WORK/tree in which no solution code has ever run: the rendered
#      challenge, the solution sources and a harness lakefile that `require`s the organiser package
#      by path. The organiser package, the toolchain and the shared packages live OUTSIDE the tree's
#      writable `.lake` and are read-only to every sandboxed step (--landrun, default
#      scripts/bwrap-landrun.sh). The comparator builds and exports the challenge before it builds
#      the solution. Manifest re-checked afterwards; the solution must not shadow an organiser module.
#      Then the harness records the content hashes of the compiled artifacts the comparator verified
#      (WORK/cmp-build.sha256: every .olean/.olean.server/.olean.private/.ir under .lake/build/lib/lean
#      and every .c under .lake/build/ir; A7-M3) and moves the tree to WORK/cmp (kept as evidence).
#   2. (--gate THM) GATE in a second fresh tree at the SAME path WORK/tree (an .olean records the
#      absolute source path, e.g. in linter messages, so only a same-path rebuild is byte-reproducible):
#      sandboxed `lake build` of the solution, manifest check, shadow check, BUILD BINDING (A7-M3:
#      every artifact of this build must be byte-identical to the comparator-verified one in
#      WORK/cmp-build.sha256; Lean builds are deterministic, so an honest solution reproduces them,
#      and a solution whose elaboration differs between the two builds is rejected), then the
#      environment gate (trust by content hash, --manifest).
#   3. The badge path (DESIGN §7.4 step 3), after the gate, in WORK/tree, on the comparator-verified
#      code (the bound .olean IR and .c files); never inside the gate or an emulator process:
#      3a (--badge-build SUBMISSION, v2) builds the badge executables `harness-verify` and
#         `harness-index` (harness/lean/Main.lean.in, generated into WORK/tree/badge at stage 1 so
#         that both trees have the same lakefile) against the constant SUBMISSION (board L
#         `RecursionFast.Challenge.submission`, board R `RecursionFast.Challenge.leaf`), importing only
#         the module that declares it (gate rule 8 checks that it reaches neither Clean nor the
#         compiler and prints it; S6b-A17),
#         sandboxed (only the tree's .lake writable: every organiser/package object file must be
#         prebuilt by scripts/org-build.sh); the bound artifacts must be unchanged afterwards;
#      3b (--bench CONFIG --secrets FILE --claim CLAIM --stub STUB, v2) runs the benchmark
#         (harness/run-benchmark.py, an organiser process that sandboxes every step itself) with
#         CONFIG plus, forced by the harness: the two executables, the sandbox (--landrun, S6b-M1),
#         and from the claim that rendered the challenge (S6b-M2): the class `k` (= Declared.k,
#         S6b-m2), the hash, the declared digests and the recursion layout C, i.e. the very file
#         rendered into the certified `C`; its result is WORK/bench.json and some board must ACCEPT.
#   Fix pass (S6b-M3, S6b-M2): in each fresh tree, before anything of the submission is built in
#   it, the SOURCE RULE (scripts/source-rule.py) on the submission's .lean files (--source-rule off
#   only for the layer regressions in tests/pipeline, each of which tests one other layer alone);
#   and before stage 0, with --claim/--stub, CHALLENGE must be the rendering of STUB with CLAIM.
# Exit 0 and "HARNESS: ACCEPT" iff every stage passes; otherwise "HARNESS: REJECT (<stage>)", exit 1.
#
# Options: --org DIR (organiser package, REQUIRED: scripts/org-build.sh DIR; this repository's root
#          is not one, it requires Clean and holds submissions)  --manifest FILE  --work DIR
#          --allowed-imports FILE (gate rule 6, S7-M1; default scripts/import-allowlist.txt, '' = off)
#          --frontend-imports FILE (gate rule 6, S6b-A11; default scripts/import-frontend.txt)
#          --prefix MOD (trusted project prefixes, repeatable; default RecursionFast.Contract, RiscvZkvm)
#          --packages DIR ('' = none)  --landrun PATH  --gate THEOREM  --computable N1,N2
#          --badge-build SUBMISSION  --bench CONFIG  --secrets FILE  --claim CLAIM.json  --stub STUB.lean.in
#          --source-rule on|off
# Environment: COMPARATOR_HOME (the comparator checkout; default ./tools/comparator),
#          COMPARATOR_NANODA (nanoda_bin; default ./tools/ext/nanoda_lib/target/release/nanoda_bin),
#          COMPARATOR_LEAN4EXPORT (default under COMPARATOR_HOME). Binaries are never in git.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
ORG=""; MANIFEST=$HERE/scripts/olean-manifest.sha256; WORK=""; LANDRUN=$HERE/scripts/bwrap-landrun.sh
ALLOW=$HERE/scripts/import-allowlist.txt; FRONT=$HERE/scripts/import-frontend.txt
GATE_THM=""; COMPUTABLE=""; BADGE_SUB=""; BENCH=""; SECRETS=""; CLAIM=""; STUB=""; SRCRULE=on; MARGS=()
while [[ $# -gt 0 && "$1" == --* ]]; do
  case "$1" in
    --org) ORG=$(cd "$2" && pwd); shift 2 ;;
    --manifest) MANIFEST=$(realpath "$2"); shift 2 ;;
    --allowed-imports) ALLOW=${2:+$(realpath "$2")}; shift 2 ;;
    --frontend-imports) FRONT=${2:+$(realpath "$2")}; shift 2 ;;
    --work) WORK=$2; shift 2 ;;
    --prefix) MARGS+=(--prefix "$2"); shift 2 ;;
    --packages) MARGS+=(--packages "$2"); shift 2 ;;
    --landrun) LANDRUN=$(realpath "$2"); shift 2 ;;
    --gate) GATE_THM=$2; shift 2 ;;
    --computable) COMPUTABLE=$2; shift 2 ;;
    --badge-build) BADGE_SUB=$2; shift 2 ;;
    --bench) BENCH=$(realpath "$2"); shift 2 ;;
    --secrets) SECRETS=$(realpath "$2"); shift 2 ;;
    --claim) CLAIM=$(realpath "$2"); shift 2 ;;
    --stub) STUB=$(realpath "$2"); shift 2 ;;
    --source-rule) SRCRULE=$2; shift 2 ;;
    *) echo "harness: unknown option $1" >&2; exit 2 ;;
  esac
done
[[ $# -eq 3 ]] || { sed -n "2,$(grep -n '^set -euo' "$0" | head -1 | cut -d: -f1)p" "$0"; exit 2; }
[[ -n "$ORG" ]] || { echo "harness: --org DIR is required (an organiser package built by scripts/org-build.sh DIR)" >&2; exit 2; }
[[ -z "$BENCH" || ( -n "$BADGE_SUB" && -n "$SECRETS" && -n "$CLAIM" && -n "$STUB" ) ]] \
  || { echo "harness: --bench needs --badge-build, --secrets, --claim and --stub (S6b-M2)" >&2; exit 2; }
[[ ( -z "$CLAIM" && -z "$STUB" ) || ( -n "$CLAIM" && -n "$STUB" ) ]] || { echo "harness: --claim and --stub go together" >&2; exit 2; }
[[ "$SRCRULE" == on || "$SRCRULE" == off ]] || { echo "harness: --source-rule on|off" >&2; exit 2; }
CHALLENGE=$(realpath "$1"); SOLDIR=$(realpath "$2"); CONFIG=$(realpath "$3")
CMP=${COMPARATOR_HOME:-$HERE/tools/comparator}
NANODA=${COMPARATOR_NANODA:-$HERE/tools/ext/nanoda_lib/target/release/nanoda_bin}
[[ -x "$CMP/.lake/build/bin/comparator" ]] || { echo "harness: no comparator at $CMP (set COMPARATOR_HOME)" >&2; exit 2; }
[[ -n "$WORK" ]] || { WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT; }
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd); TREE=$WORK/tree
[[ ! -e "$TREE" && ! -e "$WORK/cmp" ]] || { echo "harness: $WORK already holds a tree; use a fresh --work" >&2; exit 2; }
reject() { echo "HARNESS: REJECT ($*)"; exit 1; }
mcheck() { python3 -I "$HERE/scripts/olean-manifest.py" check --org "$ORG" "${MARGS[@]}" "$MANIFEST"; }
jget() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' "$1" "$2"; }
CH_MOD=$(jget "$CONFIG" challenge_module); SOL_MOD=$(jget "$CONFIG" solution_module)
# The badge executables' main modules in DIR, importing MODULE (harness/badge-main.py).
badge_mains() {
  mkdir -p "$1"; local e
  for e in verify index; do python3 -I "$HERE/harness/badge-main.py" "$1/Harness${e^}.lean" "$2" "$BADGE_SUB" $e; done
}

# A fresh tree: challenge + solution sources (+ the badge mains, which stage 3a builds) + the
# lakefile and manifest of harness/mk-tree.py (module roots checked fresh); the organiser package by path.
mkfresh() {
  local t=$1
  mkdir -p "$t/challenge" "$t/submission" "$t/.lake"
  cp "$ORG/lean-toolchain" "$t/"; cp "$CONFIG" "$t/config.json"
  local chpath; chpath="$t/challenge/$(echo "$CH_MOD" | tr . /).lean"
  mkdir -p "$(dirname "$chpath")"; cp "$CHALLENGE" "$chpath"
  (cd "$SOLDIR" && find . -name '*.lean' -not -path '*/.lake/*' -exec cp --parents {} "$t/submission/" \;)
  [[ -z "$BADGE_SUB" ]] || badge_mains "$t/badge" "$SOL_MOD"
  python3 -I "$HERE/harness/mk-tree.py" "$ORG" "$t" harness "$CH_MOD"
}
# The solution must not place an organiser module (by manifest path) anywhere in its build output.
shadow() {
  python3 -I - "$MANIFEST" "$1/.lake/build/lib/lean" <<'EOF'
import os, sys
keys = set()
for line in open(sys.argv[1]):
    if line.strip() and not line.startswith("#"):
        k = line.split(None, 1)[1].strip().split("/")
        keys.add("/".join(k[2:] if k[0] == "packages" else k[1:]))
root = sys.argv[2]
bad = [os.path.relpath(os.path.join(d, f), root) for d, _, fs in os.walk(root) for f in fs
       if os.path.relpath(os.path.join(d, f), root) in keys]
for b in bad: print(f"harness: solution build output shadows organiser module file {b}")
sys.exit(1 if bad else 0)
EOF
}

# Content hashes of a tree's compiled solution/challenge artifacts (A7-M3); paths relative to .lake/build.
# Anything but regular files and directories (e.g. a symlink planted by the build) is an error.
arts() {
  local b=$1/.lake/build d; local ds=()
  for d in lib/lean ir; do [[ -d "$b/$d" ]] && ds+=("$d"); done
  [[ ${#ds[@]} -gt 0 ]] || return 0
  if [[ -n $(cd "$b" && find "${ds[@]}" ! -type f ! -type d -print -quit) ]]; then
    echo "harness: non-regular file in $b: $(cd "$b" && find "${ds[@]}" ! -type f ! -type d | head -3 | tr '\n' ' ')" >&2; return 1
  fi
  (cd "$b" && find "${ds[@]}" -type f \( -name '*.olean' -o -name '*.olean.server' -o -name '*.olean.private' \
     -o -name '*.ir' -o -name '*.c' \) -print0 | LC_ALL=C sort -z | xargs -0 -r sha256sum)
}

if [[ -n "$CLAIM" ]]; then
  echo "== claim: the challenge is the rendering of the stub with the claim (S6b-M2)"
  # copy the claim and the files it names (images, layouts) into WORK/claim: the challenge and the
  # benchmark read these copies, never the submitter's directory again
  python3 -I - "$STUB" "$CLAIM" "$WORK/claim" <<'EOF' || reject "claim files"
import json, os, re, shutil, sys
stub, claim, dst = sys.argv[1:]
src = os.path.dirname(claim); os.makedirs(dst)
kinds = dict((k, t) for t, k in re.findall(r"\{\{(nat|rat|hash|digest|image|layout):([A-Za-z0-9_.]+)\}\}", open(stub).read()))
d = json.load(open(claim))
paths = [d[k] for k, t in kinds.items() if t == "layout" and k in d] + \
        [v for k, t in kinds.items() if t == "image" and isinstance(d.get(k), dict) for v in d[k].values()]
for rel in paths:
    if not isinstance(rel, str) or os.path.isabs(rel) or ".." in rel.split("/"):
        sys.exit(f"harness: claim path {rel!r} is not a plain relative path")
    os.makedirs(os.path.dirname(os.path.join(dst, rel)) or dst, exist_ok=True)
    shutil.copyfile(os.path.join(src, rel), os.path.join(dst, rel))
shutil.copyfile(claim, os.path.join(dst, "claim.json"))
EOF
  python3 -I "$HERE/scripts/render-challenge.py" "$STUB" "$WORK/claim/claim.json" "$WORK/claim/challenge.lean" \
    || reject "claim does not render"
  cmp -s "$WORK/claim/challenge.lean" "$CHALLENGE" || reject "the challenge is not the rendering of the stub with the claim"
  echo "harness: the challenge is the stub rendered with the claim"
fi
# The source rule (S6b-M3) on the submission's .lean files as copied into a fresh tree, before
# anything of the submission is built in it.
srcrule() {
  [[ "$SRCRULE" == on ]] || return 0
  python3 -I "$HERE/scripts/source-rule.py" "$1/submission" > "$WORK/source-rule.log" 2>&1 \
    || { tail -12 "$WORK/source-rule.log"; reject "source rule: $(tail -1 "$WORK/source-rule.log" | sed 's/^source-rule: //')"; }
  echo "harness: $(tail -1 "$WORK/source-rule.log")"
}
echo "== stage 0: organiser build integrity"
mcheck || reject "organiser build does not match the olean manifest"

echo "== stage 1: comparator, fresh tree $TREE (no solution code has run on it)"
mkfresh "$TREE" || reject "fresh tree (module names)"
srcrule "$TREE"
set +e
(cd "$TREE" && COMPARATOR_LANDRUN=$LANDRUN \
  COMPARATOR_LEAN4EXPORT=${COMPARATOR_LEAN4EXPORT:-$CMP/.lake/packages/lean4export/.lake/build/bin/lean4export} \
  COMPARATOR_NANODA=$NANODA \
  /usr/bin/time -f "TIME %e s wall, %U s user, %M KB max" lake env "$CMP/.lake/build/bin/comparator" config.json) \
  > "$WORK/comparator.log" 2>&1
rc=$?
set -e
grep -v "^WARNING: THIS IS NOT REAL" "$WORK/comparator.log" | tail -12
echo "== stage 1: post-checks"
mcheck || reject "organiser .olean changed during the comparator run"
shadow "$TREE" || reject "solution shadows an organiser module"
[[ $rc -eq 0 ]] && grep -q "Your solution is okay" "$WORK/comparator.log" || reject "comparator, exit $rc"
arts "$TREE" > "$WORK/cmp-build.sha256" || reject "comparator tree artifacts"
echo "harness: recorded $(wc -l < "$WORK/cmp-build.sha256") comparator-verified build artifacts (cmp-build.sha256)"
mv "$TREE" "$WORK/cmp"

if [[ -n "$GATE_THM" ]]; then
  echo "== stage 2: gate, fresh tree $TREE (same path; the comparator's tree is now $WORK/cmp)"
  mkfresh "$TREE" || reject "fresh tree (module names)"
  srcrule "$TREE"
  (cd "$TREE" && "$LANDRUN" --env PATH --env HOME --rwx "$TREE/.lake" -- lake build "$SOL_MOD") \
    > "$WORK/gate-build.log" 2>&1 || { tail -5 "$WORK/gate-build.log"; reject "solution build in the gate tree"; }
  mcheck || reject "organiser .olean changed during the solution build"
  shadow "$TREE" || reject "solution shadows an organiser module"
  # A7-M3: the gate (and the badge) must see exactly the build the comparator verified.
  arts "$TREE" > "$WORK/gate-build.sha256" || reject "gate tree artifacts"
  sol_olean="$(echo "$SOL_MOD" | tr . /).olean"
  grep -q "  lib/lean/$sol_olean\$" "$WORK/gate-build.sha256" || reject "gate tree build has no $sol_olean"
  nb=$(LC_ALL=C comm -23 <(LC_ALL=C sort "$WORK/gate-build.sha256") <(LC_ALL=C sort "$WORK/cmp-build.sha256") | tee "$WORK/build-diff.txt" | wc -l)
  if [[ $nb -ne 0 ]]; then
    sed 's/^[0-9a-f]*  /harness: differs from the comparator-verified build: /' "$WORK/build-diff.txt" | head -5
    reject "gate tree build differs from the comparator-verified build ($nb artifacts)"
  fi
  echo "harness: gate tree build = comparator-verified build ($(wc -l < "$WORK/gate-build.sha256") artifacts byte-identical)"
  LP=$(cd "$TREE" && lake env printenv LEAN_PATH)
  gargs=("$SOL_MOD" "$GATE_THM" --manifest "$MANIFEST"); [[ -n "$COMPUTABLE" ]] && gargs+=(--computable "$COMPUTABLE")
  [[ -n "$ALLOW" ]] && gargs+=(--allowed-imports "$ALLOW")
  [[ -n "$FRONT" ]] && gargs+=(--frontend-imports "$FRONT")
  # rule 8 (S6b-A11): the badge executables are built from the module that declares BADGE_SUB, which
  # must reach neither Clean nor the compiler; the gate prints it
  [[ -n "$BADGE_SUB" && -n "$ALLOW" ]] && gargs+=(--badge-root "$BADGE_SUB")
  (cd "$TREE" && LEAN_PATH=$LP "$LANDRUN" --env PATH --env HOME --env LEAN_PATH -- \
    "$ORG/.lake/build/bin/gate" "${gargs[@]}") | tee "$WORK/gate.log" || reject "gate"
  if [[ -n "$BADGE_SUB" ]]; then
    echo "== stage 3a: badge executables (sandboxed build in the gate tree, after the gate)"
    # the mains import only the badge root's module (rule 8; the gate prints it), else the solution's
    BMOD=$(sed -n 's/^gate: badge-root-module //p' "$WORK/gate.log")
    badge_mains "$TREE/badge" "${BMOD:-$SOL_MOD}"
    [[ -z "$BMOD" || "$BMOD" == "$SOL_MOD" ]] || echo "harness: the badge executables import $BMOD (the module of $BADGE_SUB), not $SOL_MOD"
    mkdir -p "$TREE/.lake/tmp"   # the linker's temporary files
    (cd "$TREE" && TMPDIR=$TREE/.lake/tmp "$LANDRUN" --env PATH --env HOME --env TMPDIR --rwx "$TREE/.lake" -- \
      lake build harness-verify harness-index) > "$WORK/badge-build.log" 2>&1 \
      || { grep -v "^✔\|^⣿\|^ℹ" "$WORK/badge-build.log" | tail -8; reject "badge executables build"; }
    mcheck || reject "organiser .olean changed during the badge build"
    # the bound artifacts (A7-M3) are unchanged; the badge mains' own artifacts are new
    arts "$TREE" > "$WORK/badge-build.sha256" || reject "badge tree artifacts"
    nb=$(LC_ALL=C comm -23 <(LC_ALL=C sort "$WORK/gate-build.sha256") <(LC_ALL=C sort "$WORK/badge-build.sha256") | wc -l)
    [[ $nb -eq 0 ]] || reject "the badge build changed $nb comparator-verified artifacts"
    echo "harness: badge executables built: $TREE/.lake/build/bin/harness-{verify,index} ($(wc -l < "$WORK/gate-build.sha256") bound artifacts unchanged)"
  fi
  if [[ -n "$BENCH" ]]; then
    echo "== stage 3b: benchmark run (harness/run-benchmark.py; every step sandboxed)"
    # forced by the harness (S6b-M1, S6b-M2, S6b-m2, S6b-m5): the executables, the sandbox, and from
    # the claim that rendered the challenge the class, the hash, the digests and the layout C
    python3 -I -c 'import json, os, sys
cfg = json.load(open(sys.argv[1])); b, landrun, cdir = sys.argv[2:5]
claim = json.load(open(os.path.join(cdir, "claim.json")))
cfg["verify"] = [os.path.join(b, "harness-verify")]; cfg["index"] = [os.path.join(b, "harness-index")]
cfg["sandbox"] = landrun
cfg["k"] = claim["k"]
cfg["cfg"] = {"hash": claim["hash"]}
if "C" in claim:
    cfg.setdefault("layouts", {})["C"] = os.path.join(cdir, claim["C"])
    cfg["claim"] = {"digestC": claim["digestC"], "digestL": claim["digestL"]}
elif "R" in cfg.get("boards", []):
    sys.exit("harness: board R needs a board-R claim (C, digestC, digestL)")
else:
    cfg.pop("claim", None); cfg.get("layouts", {}).pop("C", None)
json.dump(cfg, open(sys.argv[5], "w"), indent=1)' "$BENCH" "$TREE/.lake/build/bin" "$LANDRUN" "$WORK/claim" \
      "$WORK/bench-config.json" || reject "benchmark configuration"
    python3 -I "$HERE/harness/run-benchmark.py" run --config "$WORK/bench-config.json" --secrets "$SECRETS" \
      --out "$WORK/bench.json" --workdir "$WORK/bench" \
      || reject "benchmark: $(jget "$WORK/bench.json" reason)"
    python3 -I -c 'import json, sys
for b, v in json.load(open(sys.argv[1]))["scores"].items():
    r = v.get("reason")
    print("harness: board " + b + ": " + str(v.get("verdict", "unranked")) + (" (" + str(r) + ")" if r else "") + " " + str(v))' "$WORK/bench.json"
  fi
fi
echo "HARNESS: ACCEPT"

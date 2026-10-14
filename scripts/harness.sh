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
#   3. (--badge "CMD ...") the badge path (compiled prover/indexer) runs as its OWN sandboxed process
#      in WORK/tree after the gate; never inside the gate or an emulator process. It therefore runs
#      the comparator-verified code (the bound .olean IR and .c files).
# Exit 0 and "HARNESS: ACCEPT" iff every stage passes; otherwise "HARNESS: REJECT (<stage>)", exit 1.
#
# Options: --org DIR (organiser package, default this tree)  --manifest FILE  --work DIR
#          --prefix MOD (trusted project prefixes, repeatable; default RecursionFast.Contract, RiscvZkvm)
#          --packages DIR ('' = none)  --landrun PATH  --gate THEOREM  --computable N1,N2  --badge CMD
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
ORG=$HERE; MANIFEST=$HERE/scripts/olean-manifest.sha256; WORK=""; LANDRUN=$HERE/scripts/bwrap-landrun.sh
GATE_THM=""; COMPUTABLE=""; BADGE=""; MARGS=()
while [[ $# -gt 0 && "$1" == --* ]]; do
  case "$1" in
    --org) ORG=$(cd "$2" && pwd); shift 2 ;;
    --manifest) MANIFEST=$(realpath "$2"); shift 2 ;;
    --work) WORK=$2; shift 2 ;;
    --prefix) MARGS+=(--prefix "$2"); shift 2 ;;
    --packages) MARGS+=(--packages "$2"); shift 2 ;;
    --landrun) LANDRUN=$(realpath "$2"); shift 2 ;;
    --gate) GATE_THM=$2; shift 2 ;;
    --computable) COMPUTABLE=$2; shift 2 ;;
    --badge) BADGE=$2; shift 2 ;;
    *) echo "harness: unknown option $1" >&2; exit 2 ;;
  esac
done
[[ $# -eq 3 ]] || { sed -n '2,31p' "$0"; exit 2; }
CHALLENGE=$(realpath "$1"); SOLDIR=$(realpath "$2"); CONFIG=$(realpath "$3")
CMP=${COMPARATOR_HOME:-$HERE/../contract/tools/comparator}
[[ -n "$WORK" ]] || { WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT; }
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd); TREE=$WORK/tree
[[ ! -e "$TREE" && ! -e "$WORK/cmp" ]] || { echo "harness: $WORK already holds a tree; use a fresh --work" >&2; exit 2; }
reject() { echo "HARNESS: REJECT ($*)"; exit 1; }
mcheck() { python3 -I "$HERE/scripts/olean-manifest.py" check --org "$ORG" "${MARGS[@]}" "$MANIFEST"; }
cfg() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' "$CONFIG" "$1"; }
CH_MOD=$(cfg challenge_module); SOL_MOD=$(cfg solution_module)

# A fresh tree: challenge + solution sources + harness lakefile; the organiser package by path.
mkfresh() {
  local t=$1
  mkdir -p "$t/challenge" "$t/submission" "$t/.lake"
  cp "$ORG/lean-toolchain" "$t/"
  local chpath; chpath="$t/challenge/$(echo "$CH_MOD" | tr . /).lean"
  mkdir -p "$(dirname "$chpath")"; cp "$CHALLENGE" "$chpath"
  (cd "$SOLDIR" && find . -name '*.lean' -not -path '*/.lake/*' -exec cp --parents {} "$t/submission/" \;)
  python3 -I - "$ORG" "$t" "$CH_MOD" <<'EOF'
import json, os, sys, tomllib
org, t, ch = sys.argv[1:]
name = tomllib.load(open(os.path.join(org, "lakefile.toml"), "rb"))["name"]
m = json.load(open(os.path.join(org, "lake-manifest.json")))
pk = os.path.normpath(os.path.join(org, m.get("packagesDir") or ".lake/packages"))
mods = sorted(os.path.relpath(os.path.join(d, f), os.path.join(t, "submission"))[:-5].replace(os.sep, ".")
              for d, _, fs in os.walk(os.path.join(t, "submission")) for f in fs if f.endswith(".lean"))
# Module roots must be fresh: Lean resolves a module through the FIRST search-path root that has
# its top-level name, and the organiser package and packages precede the tree's own build output.
import glob, subprocess
dirs = [os.path.join(org, ".lake/build/lib/lean")] + glob.glob(os.path.join(pk, "*/.lake/build/lib/lean"))
dirs.append(os.path.join(subprocess.run(["lean", "--print-prefix"], cwd=t, capture_output=True, text=True,
                                        check=True).stdout.strip(), "lib/lean"))
for r in sorted({x.split(".")[0] for x in mods + [ch]}):
    for d in dirs:
        if os.path.isdir(os.path.join(d, r)) or os.path.exists(os.path.join(d, r + ".olean")):
            sys.exit(f"harness: module root {r} of the challenge/solution exists in {d}")
q = lambda xs: "[" + ", ".join(json.dumps(x) for x in xs) + "]"
open(os.path.join(t, "lakefile.toml"), "w").write(f"""name = "harness"
packagesDir = {json.dumps(pk)}
[[require]]
name = {json.dumps(name)}
path = {json.dumps(org)}
[[lean_lib]]
name = "HarnessChallenge"
srcDir = "challenge"
roots = {q([ch])}
[[lean_lib]]
name = "HarnessSubmission"
srcDir = "submission"
roots = {q(mods)}
""")
for p in m["packages"]:
    p["inherited"] = True
m["packages"].insert(0, {"type": "path", "scope": "", "name": name, "manifestFile": "lake-manifest.json",
                         "inherited": False, "dir": org, "configFile": "lakefile.toml"})
m["name"] = "harness"; m["packagesDir"] = pk
json.dump(m, open(os.path.join(t, "lake-manifest.json"), "w"), indent=1)
EOF
  cp "$CONFIG" "$t/config.json"
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

echo "== stage 0: organiser build integrity"
mcheck || reject "organiser build does not match the olean manifest"

echo "== stage 1: comparator, fresh tree $TREE (no solution code has run on it)"
mkfresh "$TREE" || reject "fresh tree (module names)"
set +e
(cd "$TREE" && COMPARATOR_LANDRUN=$LANDRUN \
  COMPARATOR_LEAN4EXPORT=${COMPARATOR_LEAN4EXPORT:-$CMP/.lake/packages/lean4export/.lake/build/bin/lean4export} \
  COMPARATOR_NANODA=${COMPARATOR_NANODA:-$HERE/tools/ext/nanoda_lib/target/release/nanoda_bin} \
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
  (cd "$TREE" && LEAN_PATH=$LP "$LANDRUN" --env PATH --env HOME --env LEAN_PATH -- \
    "$ORG/.lake/build/bin/gate" "${gargs[@]}") || reject "gate"
  if [[ -n "$BADGE" ]]; then
    echo "== stage 3: badge path (own sandboxed process)"
    (cd "$TREE" && "$LANDRUN" --env PATH --env HOME -- bash -c "$BADGE") || reject "badge"
  fi
fi
echo "HARNESS: ACCEPT"

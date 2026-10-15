#!/usr/bin/env bash
# A6-G0 regression (probes/s6b/pipeline/cmpproj, Lean core only; v0.3 probes/a6/cmpproj): a solution whose elaboration rewrites the
# contract `.olean` (`Good := True` for an unsatisfiable `Good`) must be REJECTED by the production
# pipeline (scripts/harness.sh), in every variant:
#   B-old  A6's scenario B (solution built first in the shared tree): the old order still accepts
#          (shown for reference), and the manifest check that now precedes the comparator rejects it.
#   B-rel  A6's Tamper.lean (rewrites the tree's own .lake/build) under the harness: rejected.
#   B-lp   TamperLP.lean (rewrites the organiser package found through LEAN_PATH) under the harness
#          sandbox: rejected (read-only organiser package, the solution does not build).
#   B-lp-nosandbox  the same with the insecure fake landrun: still rejected (the comparator exported
#          the challenge before the solution ran: "Const does not match"; the post-stage manifest
#          check also reports the changed file).
# (S6b fix pass) `--source-rule off`: this regression tests one layer alone; its probes use `#eval`
# and `import Lean` on purpose, which the source rule (scripts/source-rule.py) would reject first.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/../.." && pwd)
P=$HERE/probes/s6b/pipeline/cmpproj
C=${COMPARATOR_HOME:?set COMPARATOR_HOME}
FAKE=$C/scripts/fake-landrun.sh
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
manifest() { python3 -I "$HERE/scripts/olean-manifest.py" "$1" --org "$2" --packages '' --prefix RecursionFast.Contract "$3"; }
# organiser package: the stand-in contract only, built before any solution code exists
mkorg() {
  mkdir -p "$1/RecursionFast"
  cp "$P/RecursionFast/Contract.lean" "$1/RecursionFast/"; cp "$P/lean-toolchain" "$P/lake-manifest.json" "$1/"
  printf 'name = "cmpproj"\n[[lean_lib]]\nname = "Contract"\nroots = ["RecursionFast.Contract"]\n' > "$1/lakefile.toml"
  (cd "$1" && lake build Contract > /dev/null)
  manifest gen "$1" "$1.manifest" > /dev/null
}
harness() {  # org work soldir [extra harness options]
  "$HERE/scripts/harness.sh" --source-rule off --org "$1" --manifest "$1.manifest" --packages '' --prefix RecursionFast.Contract \
    --work "$2" "${@:4}" "$P/Challenge.lean" "$3" "$P/config.json"
}
expect_reject() {  # name, command...
  local n=$1; shift
  if "$@" > "$T/$n.log" 2>&1; then echo "cmpproj $n: ACCEPTED (regression)"; tail -20 "$T/$n.log"; exit 1; fi
  echo "cmpproj $n: rejected: $(grep -hi "HARNESS:\|olean-manifest: FAIL\|Const does not match\|read-only file system" "$T/$n.log" | head -3 | tr '\n' ' ')"
}
mkdir -p "$T/solA" "$T/solB"
cp "$P/Solution.lean" "$P/Tamper.lean" "$T/solA/"
sed 's/^import Tamper$/import TamperLP/' "$P/Solution.lean" > "$T/solB/Solution.lean"; cp "$P/TamperLP.lean" "$T/solB/"

# B-old: A6's scenario B in a shared tree
mkdir -p "$T/shared"; cp -r "$P"/. "$T/shared/"
(cd "$T/shared" && lake build Contract > /dev/null)
manifest gen "$T/shared" "$T/shared.manifest" > /dev/null
(cd "$T/shared" && lake build Contract Solution > /dev/null 2>&1)
if (cd "$T/shared" && COMPARATOR_LANDRUN=$FAKE COMPARATOR_LEAN4EXPORT=$C/.lake/packages/lean4export/.lake/build/bin/lean4export \
    lake env "$C/.lake/build/bin/comparator" config.json 2>&1 | grep -q "Your solution is okay"); then
  echo "cmpproj B-old: the v0.3 order (solution built first, comparator last) ACCEPTS the false statement (A6-G0, reference)"
else echo "cmpproj B-old: note: the old order no longer reproduces the acceptance"; fi
expect_reject B-old-manifest manifest check "$T/shared" "$T/shared.manifest"
expect_reject B-old-harness harness "$T/shared" "$T/w0" "$T/solA"
# B-rel, B-lp: the production pipeline (fresh trees, read-only organiser package)
mkorg "$T/org1"
expect_reject B-rel harness "$T/org1" "$T/w1" "$T/solA"
expect_reject B-lp harness "$T/org1" "$T/w2" "$T/solB"
for n in B-rel B-lp; do
  grep -qi "read-only file system" "$T/$n.log" || { echo "cmpproj $n: expected the sandbox to block the write"; exit 1; }
done
manifest check "$T/org1" "$T/org1.manifest" > /dev/null || { echo "cmpproj: organiser package changed under the sandbox"; exit 1; }
# B-lp without a sandbox: the order alone still rejects
mkorg "$T/org2"
expect_reject B-lp-nosandbox harness "$T/org2" "$T/w3" "$T/solB" --landrun "$FAKE"
grep -q "Const does not match" "$T/B-lp-nosandbox.log" || { echo "cmpproj: expected a comparator mismatch"; exit 1; }
grep -q "olean-manifest: FAIL" "$T/B-lp-nosandbox.log" || { echo "cmpproj: expected the post-stage manifest check to fail"; exit 1; }
echo "cmpproj regression OK"

#!/usr/bin/env bash
# Cross-check the indexer's layout JSON reader against the challenge renderer (Stage 6b), on every
# layout of harness/examples/ (the full add8 table, trimmed explicit tables, L_chain(n)) and the
# dummy one-chip layout. Run from the organiser package or the repository (lake env).
#   probes/s6b/layout/check.sh LAKE_DIR
set -euo pipefail
HERE=$(cd "$(dirname "$0")/../../.." && pwd)
LAKE_DIR=$(cd "${1:-$HERE}" && pwd)
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
python3 -I "$HERE/scripts/dummy-claim.py" "$HERE/RecursionFast/Challenge/R.lean.in" "$T/dummy.json" > /dev/null
n=0
for L in "$HERE"/harness/examples/*.layout.json "$T/dummy-C.layout.json"; do
  n=$((n + 1)); d=$T/c$n; mkdir -p "$d"; cp "$L" "$d/C.json"
  printf '{"C": "C.json"}' > "$d/claim.json"
  python3 -I "$HERE/scripts/render-challenge.py" "$HERE/probes/s6b/layout/Check.lean.in" "$d/claim.json" "$d/Check.lean"
  cat >> "$d/Check.lean" <<LEAN

/-- The reader's layout equals the rendered one, word for word. -/
def check : IO Unit := do
  match RecursionFastHarness.LayoutJson.parse (← IO.FS.readFile "$d/C.json") with
  | .error e => throw (IO.userError s!"reader: {e}")
  | .ok L =>
    let (a, b) := (L.words, ParseCheck.C.words)
    unless a == b do throw (IO.userError s!"MISMATCH: {a.length} vs {b.length} words")
    IO.println s!"layout check: $(basename "$L"): reader = renderer ({a.length} words)"

#eval check
LEAN
  (cd "$LAKE_DIR" && lake env lean "$d/Check.lean") 2>&1 | grep -v "manifest out of date"
done
# negative control: one matrix value of the rendered literal changed (`kx 1` -> `kx 3`) must mismatch
sed '0,/(\([0-9]*\), \([0-9]*\), kx 1)/s//(\1, \2, kx 3)/' "$T/c1/Check.lean" > "$T/c1/Bad.lean"
! cmp -s "$T/c1/Check.lean" "$T/c1/Bad.lean" || { echo "layout check: the negative control did not change the file"; exit 1; }
if (cd "$LAKE_DIR" && lake env lean "$T/c1/Bad.lean") > "$T/bad.log" 2>&1; then
  echo "layout check: a changed literal was NOT detected (bug)"; exit 1; fi
grep -q MISMATCH "$T/bad.log" && echo "layout check: negative control (one matrix value changed): MISMATCH detected"

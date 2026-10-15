#!/usr/bin/env bash
# Organiser package build (A6-G0): a separate directory that holds ONLY organiser sources and
# organiser build outputs (contract, vendored Rv64, Library, Controls, Bridge, `gate`, `axiomaudit`,
# the harness driver `RecursionFastHarness` and `harness-linkcheck`, Stage 6b),
# never a solution, a rendered challenge or a probe. The harness `require`s it by path, read-only
# (scripts/harness.sh), and its trusted `.olean`s are checked against scripts/olean-manifest.sha256.
#
#   scripts/org-build.sh DEST
#
# Sources are synchronised from this tree (rsync --delete; Lake traces are content hashes, so an
# unchanged source is not rebuilt). The lakefile is this tree's minus every non-organiser library
# (RecursionFastAudit*, RecursionFastCandidate, RecursionFastBaselineAudit) and minus the NOT SECURE
# smoke-test protocol and its executables (Stage 6b); packagesDir and Clean's path are made absolute.
# Stage 6b decision (S6b-A11): the Clean frontend is in the organiser package (the `Clean` require at
# the pinned rev, built from ext/Clean, hash-pinned by the olean manifest like the other pinned
# packages, and the untrusted bridge `RecursionFastClean`), so that a board-R submission's circuit
# proofs can import it; gate rule 8 keeps it out of the badge executables.
# Stage 6b: `harness-linkcheck` (harness/lean/LinkCheck.lean) imports every organiser library, so
# building it prebuilds every object file a badge executable links (the gate tree sees this package
# read-only), and running it checks that no organiser module is expensive to initialise.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
DEST=${1:?usage: org-build.sh DEST}
mkdir -p "$DEST/RecursionFast" "$DEST/scripts"
for d in Contract Vendor Library Controls Bridge Clean; do
  # S9F-M1: a directory git does not hold (an empty one, absent from every clone) is an empty
  # directory here (a library's `globs` need the directory to exist)
  if [[ -d "$HERE/RecursionFast/$d" ]]; then
    rsync -a --delete "$HERE/RecursionFast/$d/" "$DEST/RecursionFast/$d/"
  else
    rm -rf "${DEST:?}/RecursionFast/${d:?}"; mkdir -p "$DEST/RecursionFast/$d"
  fi
  [[ -f "$HERE/RecursionFast/$d.lean" ]] && cp -p "$HERE/RecursionFast/$d.lean" "$DEST/RecursionFast/"
done
mkdir -p "$DEST/harness/lean"
rsync -a --delete "$HERE/harness/lean/" "$DEST/harness/lean/"
cp -p "$HERE/scripts/Gate.lean" "$HERE/scripts/AxiomAudit.lean" "$DEST/scripts/"
cp -p "$HERE/lean-toolchain" "$DEST/"
python3 -I - "$HERE" "$DEST" <<'EOF'
import json, os, re, sys
here, dest = sys.argv[1:]
drop = {"RecursionFastAudit", "RecursionFastAuditNegative", "RecursionFastCandidate", "RecursionFastBaselineAudit",
        "RecursionFastSmoke", "smoke-verify", "smoke-index"}   # Stage 6b: the NOT SECURE smoke protocol
m = json.load(open(os.path.join(here, "lake-manifest.json")))
m["packages"] = [p for p in m["packages"] if p["name"] not in drop]
for p in m["packages"]:            # path packages (Clean at ext/Clean) by absolute path
    if p.get("type") == "path":
        p["dir"] = os.path.normpath(os.path.join(here, p["dir"]))
pk = os.path.normpath(os.path.join(here, m.get("packagesDir") or ".lake/packages"))
text = open(os.path.join(here, "lakefile.toml")).read()
blocks = re.split(r"(?m)^(?=\[\[)", text)
keep = [b for b in blocks if not (b.startswith("[[") and
        (n := re.search(r'(?m)^name\s*=\s*"([^"]+)"', b)) and n.group(1) in drop)]
out = re.sub(r'(?m)^packagesDir\s*=.*$', f"packagesDir = {json.dumps(pk)}", "".join(keep))
out = re.sub(r'(?m)^path\s*=\s*"ext/Clean"$', f"path = {json.dumps(os.path.join(here, 'ext/Clean'))}", out)
new = os.path.join(dest, "lakefile.toml")
if not os.path.exists(new) or open(new).read() != out:
    open(new, "w").write(out)
m["packagesDir"] = pk
open(os.path.join(dest, "lake-manifest.json"), "w").write(json.dumps(m, indent=1) + "\n")
EOF
cd "$DEST"
T="RecursionFastContract RecursionFastLibrary RecursionFastControls RecursionFastBridge gate axiomaudit"
T="$T RecursionFastHarness harness-linkcheck RecursionFastClean"
out=$(lake build $T 2>&1) && rc=0 || rc=$?
grep -v "^✔\|^⣿\|^ℹ\|^info: \|native backend disabled\|sqlite3\|^ *[0-9]* |\|^ *|\|Wdiscarded" <<< "$out" || true
[[ $rc -eq 0 ]] || { echo "org-build: lake build failed (exit $rc)"; exit 1; }
(ulimit -v 16000000; timeout 60 .lake/build/bin/harness-linkcheck) \
  || { echo "org-build: harness-linkcheck failed (an organiser module is expensive to initialise?)"; exit 1; }
# Gate rule 6 (S7-M1): the modules a submission may import, the import closure of the organiser's
# roots; compared with the committed scripts/import-allowlist.txt by scripts/ci.sh.
lake env .lake/build/bin/gate --closure Mathlib,RecursionFast.Contract,RecursionFast.Library,RecursionFast.Controls \
  import-allowlist.txt 2>&1 | grep -v "manifest out of date"
# Rule 6's frontend list (S6b-A11): Clean's own modules and the bridge, importable by a submission's
# circuit proofs but not by the module of its badge root (rule 8); compared with
# scripts/import-frontend.txt by scripts/ci.sh. (Clean's closure contains `Lean` itself, so only
# Clean's own modules are listed, not the Lean modules they import.)
# frontend-closure.txt (the whole closure, Lean and Mathlib modules included) is kept: with
# import-allowlist.txt it is the trusted closure the olean manifest covers (S9F-M2,
# scripts/olean-manifest.py gen --closure).
lake env .lake/build/bin/gate --closure RecursionFast.Clean frontend-closure.txt 2>&1 | grep -v "manifest out of date"
grep -E '^(Clean|RecursionFast\.Clean)(\.|$)' frontend-closure.txt > import-frontend.txt
echo "org-build: organiser package built in $DEST"

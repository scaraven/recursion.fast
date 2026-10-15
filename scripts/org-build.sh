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
# (RecursionFastAudit*, RecursionFastCandidate, RecursionFastBaselineAudit) and minus the Clean frontend
# (the `Clean` require and `RecursionFastClean`, with Clean's manifest entry) and minus the NOT SECURE
# smoke-test protocol and its executables (Stage 6b); packagesDir is made absolute.
# Stage 6b: `harness-linkcheck` (harness/lean/LinkCheck.lean) imports every organiser library, so
# building it prebuilds every object file a badge executable links (the gate tree sees this package
# read-only), and running it checks that no organiser module is expensive to initialise.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
DEST=${1:?usage: org-build.sh DEST}
mkdir -p "$DEST/RecursionFast" "$DEST/scripts"
for d in Contract Vendor Library Controls Bridge; do
  rsync -a --delete "$HERE/RecursionFast/$d/" "$DEST/RecursionFast/$d/"
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
        "Clean", "RecursionFastClean",   # Stage 8: the untrusted Clean frontend never enters the organiser package
        "RecursionFastSmoke", "smoke-verify", "smoke-index"}   # Stage 6b: the NOT SECURE smoke protocol
m = json.load(open(os.path.join(here, "lake-manifest.json")))
m["packages"] = [p for p in m["packages"] if p["name"] not in drop]
pk = os.path.normpath(os.path.join(here, m.get("packagesDir") or ".lake/packages"))
text = open(os.path.join(here, "lakefile.toml")).read()
blocks = re.split(r"(?m)^(?=\[\[)", text)
keep = [b for b in blocks if not (b.startswith("[[") and
        (n := re.search(r'(?m)^name\s*=\s*"([^"]+)"', b)) and n.group(1) in drop)]
out = re.sub(r'(?m)^packagesDir\s*=.*$', f"packagesDir = {json.dumps(pk)}", "".join(keep))
new = os.path.join(dest, "lakefile.toml")
if not os.path.exists(new) or open(new).read() != out:
    open(new, "w").write(out)
m["packagesDir"] = pk
open(os.path.join(dest, "lake-manifest.json"), "w").write(json.dumps(m, indent=1) + "\n")
EOF
cd "$DEST"
T="RecursionFastContract RecursionFastLibrary RecursionFastControls RecursionFastBridge gate axiomaudit"
T="$T RecursionFastHarness harness-linkcheck"
lake build $T 2>&1 \
  | grep -v "^✔\|^⣿\|^ℹ\|^info: \|native backend disabled\|sqlite3\|^ *[0-9]* |\|^ *|\|Wdiscarded" || true
lake build $T > /dev/null
(ulimit -v 16000000; timeout 60 .lake/build/bin/harness-linkcheck) \
  || { echo "org-build: harness-linkcheck failed (an organiser module is expensive to initialise?)"; exit 1; }
# Gate rule 6 (S7-M1): the modules a submission may import, the import closure of the organiser's
# roots; compared with the committed scripts/import-allowlist.txt by scripts/ci.sh.
lake env .lake/build/bin/gate --closure Mathlib,RecursionFast.Contract,RecursionFast.Library,RecursionFast.Controls \
  import-allowlist.txt 2>&1 | grep -v "manifest out of date"
echo "org-build: organiser package built in $DEST"

#!/usr/bin/env bash
# Organiser package build (A6-G0): a separate directory that holds ONLY organiser sources and
# organiser build outputs (contract, vendored Rv64, Library, Controls, Bridge, `gate`, `axiomaudit`),
# never a solution, a rendered challenge or a probe. The harness `require`s it by path, read-only
# (scripts/harness.sh), and its trusted `.olean`s are checked against scripts/olean-manifest.sha256.
#
#   scripts/org-build.sh DEST
#
# Sources are synchronised from this tree (rsync --delete; Lake traces are content hashes, so an
# unchanged source is not rebuilt). The lakefile is this tree's minus every non-organiser library
# (RecursionFastAudit*, RecursionFastCandidate, RecursionFastBaselineAudit); packagesDir is made absolute.
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
DEST=${1:?usage: org-build.sh DEST}
mkdir -p "$DEST/RecursionFast" "$DEST/scripts"
for d in Contract Vendor Library Controls Bridge; do
  rsync -a --delete "$HERE/RecursionFast/$d/" "$DEST/RecursionFast/$d/"
  [[ -f "$HERE/RecursionFast/$d.lean" ]] && cp -p "$HERE/RecursionFast/$d.lean" "$DEST/RecursionFast/"
done
cp -p "$HERE/scripts/Gate.lean" "$HERE/scripts/AxiomAudit.lean" "$DEST/scripts/"
cp -p "$HERE/lean-toolchain" "$DEST/"
python3 -I - "$HERE" "$DEST" <<'EOF'
import json, os, re, sys
here, dest = sys.argv[1:]
drop = {"RecursionFastAudit", "RecursionFastAuditNegative", "RecursionFastCandidate", "RecursionFastBaselineAudit"}
m = json.load(open(os.path.join(here, "lake-manifest.json")))
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
lake build RecursionFastContract RecursionFastLibrary RecursionFastControls RecursionFastBridge gate axiomaudit 2>&1 \
  | grep -v "^✔\|^⣿\|^ℹ\|^info: \|native backend disabled\|sqlite3\|^ *[0-9]* |\|^ *|\|Wdiscarded" || true
lake build RecursionFastContract RecursionFastLibrary RecursionFastControls RecursionFastBridge gate axiomaudit > /dev/null
echo "org-build: organiser package built in $DEST"

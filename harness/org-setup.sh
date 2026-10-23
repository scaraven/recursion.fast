#!/usr/bin/env bash
# The organiser's preparation of a machine (TRUSTED; run before any entry code exists on it):
#   1. build the organiser's Lean targets (contract, library, controls) in ORG (Mathlib from its
#      cache on CI: `lake exe cache get` happens before this script, never on a shared tree);
#   2. build the Lean harness tools (harness/lean-tools: gate, axiomaudit, chaincheck);
#   3. write the import allowlist (gate rule 6: the import closure of the organiser's roots) and the
#      olean manifest over it (`scripts/olean-manifest.py gen`) into ORG/.lake/rf/;
#   4. build, once and outside any sandbox, what Lake links into every badge executable: the
#      compiled objects of every module of the organiser's import closure and the external C
#      libraries of the package tree (a throw-away executable that imports `RecursionFast`), so that
#      a badge build in the sandbox writes the package tree only for modules an entry adds;
#   5. build the service (`cargo build --release`).
#
#   harness/org-setup.sh ORG          (ORG: the organiser checkout, e.g. the repository root)
# Logs: ORG/logs/org-setup/ (gitignored). Every step under `timeout`.
set -euo pipefail
ORG=$(cd "${1:?usage: org-setup.sh ORG}" && pwd)
HERE=$(cd "$(dirname "$0")" && pwd)
LOG=$ORG/logs/org-setup; mkdir -p "$LOG" "$ORG/.lake/rf"
ROOTS=${RF_ORG_ROOTS:-Mathlib,RecursionFast.Contract,RecursionFast.Library,RecursionFast.Controls}
TARGETS=${RF_ORG_TARGETS:-RecursionFast}
t0=$(date +%s); step() { echo "== org-setup: $1 ($(( $(date +%s) - t0 )) s)"; }

step "1 organiser build ($TARGETS)"
(cd "$ORG" && timeout 7200 lake build $TARGETS) > "$LOG/build.log" 2>&1 || { tail -20 "$LOG/build.log"; exit 1; }
step "2 harness tools"
(cd "$HERE/lean-tools" && timeout 1800 lake build gate axiomaudit chaincheck tokensweep) > "$LOG/tools.log" 2>&1 \
  || { tail -20 "$LOG/tools.log"; exit 1; }
step "3 allowlist and olean manifest"
(cd "$ORG" && timeout 1800 lake env "$HERE/lean-tools/.lake/build/bin/gate" --closure "$ROOTS" "$ORG/.lake/rf/allowlist.txt") \
  > "$LOG/allowlist.log" 2>&1 || { cat "$LOG/allowlist.log"; exit 1; }
timeout 1800 python3 -I "$ORG/scripts/olean-manifest.py" gen --org "$ORG" --closure "$ORG/.lake/rf/allowlist.txt" \
  "$ORG/.lake/rf/manifest.sha256" > "$LOG/manifest.log" 2>&1 || { cat "$LOG/manifest.log"; exit 1; }
tail -1 "$LOG/allowlist.log"; tail -1 "$LOG/manifest.log"
step "4 compiled objects and external libraries for the badge executables"
X=$(mktemp -d "$ORG/.lake/rf/extlibs.XXXXXX")
PK=$(python3 -I -c 'import json,os,sys; o=sys.argv[1]; m=json.load(open(os.path.join(o,"lake-manifest.json"))); print(os.path.realpath(os.path.join(o, m.get("packagesDir") or ".lake/packages")))' "$ORG")
cp "$ORG/lean-toolchain" "$X/"
printf 'import RecursionFast\ndef main : IO Unit := pure ()\n' > "$X/Nop.lean"
python3 -I - "$ORG" "$X" "$PK" <<'EOF'
import json, os, sys
org, x, pk = sys.argv[1:]
open(os.path.join(x, "lakefile.toml"), "w").write(
    f'name = "rfextlibs"\npackagesDir = {json.dumps(pk)}\n[[require]]\nname = "RecursionFast"\npath = {json.dumps(org)}\n'
    '[[lean_exe]]\nname = "nop"\nroot = "Nop"\n')
m = json.load(open(os.path.join(org, "lake-manifest.json")))
for p in m["packages"]:
    p["inherited"] = True
m["packages"].insert(0, {"type": "path", "scope": "", "name": "RecursionFast", "manifestFile": "lake-manifest.json",
                         "inherited": False, "dir": org, "configFile": "lakefile.toml"})
m["name"], m["packagesDir"] = "rfextlibs", pk
json.dump(m, open(os.path.join(x, "lake-manifest.json"), "w"), indent=1)
EOF
(cd "$X" && timeout 7200 lake build nop) > "$LOG/extlibs.log" 2>&1 || { tail -20 "$LOG/extlibs.log"; exit 1; }
rm -rf "$X"
step "5 service"
(cd "$ORG/service" && timeout 1800 cargo build --release) > "$LOG/service.log" 2>&1 || { tail -20 "$LOG/service.log"; exit 1; }
step "done"

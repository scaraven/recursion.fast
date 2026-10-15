#!/usr/bin/env python3
"""Write the lakefile.toml and lake-manifest.json of a fresh tree that `require`s the organiser
package by path (scripts/harness.sh `mkfresh`: the comparator's and the gate's trees;
harness/badge-build.sh). Stage 6b.

  python3 -I harness/mk-tree.py ORG TREE NAME [CHALLENGE_MODULE]

Libraries: `HarnessChallenge` (TREE/challenge, root CHALLENGE_MODULE, if given) and
`HarnessSubmission` (every module under TREE/submission); one executable `harness-<x>` per badge
main module TREE/badge/Harness<X>.lean. With a challenge (the production harness), every module
root of the challenge, the solution and the badge mains must be fresh: Lean resolves a module
through the FIRST search-path root that has its top-level name, and the organiser package and
packages precede the tree's own build output."""
import glob, json, os, subprocess, sys, tomllib

org, t, pkg = sys.argv[1:4]
ch = sys.argv[4] if len(sys.argv) > 4 else None
name = tomllib.load(open(os.path.join(org, "lakefile.toml"), "rb"))["name"]
m = json.load(open(os.path.join(org, "lake-manifest.json")))
pk = os.path.normpath(os.path.join(org, m.get("packagesDir") or ".lake/packages"))
mods = sorted(os.path.relpath(os.path.join(d, f), os.path.join(t, "submission"))[:-5].replace(os.sep, ".")
              for d, _, fs in os.walk(os.path.join(t, "submission")) for f in fs if f.endswith(".lean"))
badge = sorted(f[:-5] for f in os.listdir(os.path.join(t, "badge"))) if os.path.isdir(os.path.join(t, "badge")) else []
if ch:
    dirs = [os.path.join(org, ".lake/build/lib/lean")] + glob.glob(os.path.join(pk, "*/.lake/build/lib/lean"))
    dirs.append(os.path.join(subprocess.run(["lean", "--print-prefix"], cwd=t, capture_output=True, text=True,
                                            check=True).stdout.strip(), "lib/lean"))
    if set(badge) & {x.split(".")[0] for x in mods + [ch]}:
        sys.exit(f"harness: a solution or challenge module uses a badge module root {badge}")
    for r in sorted({x.split(".")[0] for x in mods + [ch] + badge}):
        for d in dirs:
            if os.path.isdir(os.path.join(d, r)) or os.path.exists(os.path.join(d, r + ".olean")):
                sys.exit(f"harness: module root {r} of the challenge/solution exists in {d}")
q = lambda xs: "[" + ", ".join(json.dumps(x) for x in xs) + "]"
lib = lambda n, src, roots: f'[[lean_lib]]\nname = "{n}"\nsrcDir = "{src}"\nroots = {q(roots)}\n'
open(os.path.join(t, "lakefile.toml"), "w").write(
    f'name = "{pkg}"\npackagesDir = {json.dumps(pk)}\n[[require]]\nname = {json.dumps(name)}\npath = {json.dumps(org)}\n'
    + (lib("HarnessChallenge", "challenge", [ch]) if ch else "") + lib("HarnessSubmission", "submission", mods)
    + "".join(f'[[lean_exe]]\nname = "harness-{b[7:].lower()}"\nsrcDir = "badge"\nroot = "{b}"\n' for b in badge))
for p in m["packages"]:
    p["inherited"] = True
m["packages"].insert(0, {"type": "path", "scope": "", "name": name, "manifestFile": "lake-manifest.json",
                         "inherited": False, "dir": org, "configFile": "lakefile.toml"})
m["name"] = pkg; m["packagesDir"] = pk
json.dump(m, open(os.path.join(t, "lake-manifest.json"), "w"), indent=1)

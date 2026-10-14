#!/usr/bin/env python3
"""Hash manifest of the organiser-built `.olean` files (A6-G0/G2).

  scripts/olean-manifest.py gen   [--org DIR] [--packages DIR] [--prefix MOD]... OUT
  scripts/olean-manifest.py check [--org DIR] [--packages DIR] [--prefix MOD]... MANIFEST

Scope (every `*.olean`, `*.olean.server`, `*.olean.private` file of):
  core/<rel>              the toolchain (`lean --print-prefix`/lib/lean): Init, Std, Lean, Lake, ...
  packages/<pkg>/<rel>    the trusted Mathlib dependencies and the pinned packages (DESIGN §13) in the
                          shared packages directory (`<pkg>/.lake/build/lib/lean`)
  project/<rel>           the organiser package's own build (`<org>/.lake/build/lib/lean`), restricted
                          to the trusted modules: `RecursionFast.Contract(.*)`, `RiscvZkvm(.*)`
                          (`--prefix` replaces this list, for the mini projects of the CI regressions)
`<rel>` is the module's path, e.g. `Mathlib/Order/Basic.olean`. Line format: `<sha256>  <tag>/<rel>`.

`gen` is run once on a clean organiser build, before any solution code exists on the machine.
`check` recomputes the same scope and fails (exit 1) on a changed, missing or **extra** file (a new
module dropped into a trusted directory, e.g. `Mathlib/Evil.olean` or `RecursionFast/Contract/Evil.olean`).
The harness runs `check` before and after every stage that runs solution code; the gate trusts a
module iff its files hash to this manifest (`scripts/Gate.lean`, `--manifest`).
"""
import argparse, hashlib, json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

TRUSTED_PKGS = ["mathlib", "batteries", "aesop", "Qq", "plausible", "proofwidgets", "importGraph",
                "LeanSearchClient"]
PINNED_PKGS = ["CompPoly", "Arklib", "VCVio", "PolyFun"]
DEFAULT_PREFIXES = ["RecursionFast.Contract", "RiscvZkvm"]
EXTS = (".olean", ".olean.server", ".olean.private")

def olean_files(root):
    for dp, dns, fns in os.walk(root):
        dns.sort()
        for f in sorted(fns):
            if f.endswith(EXTS):
                p = os.path.join(dp, f)
                yield os.path.relpath(p, root), p

def module_of(rel):
    for e in EXTS[::-1]:
        if rel.endswith(e):
            return rel[: -len(e)].replace(os.sep, ".")
    return None

def under(mod, prefixes):
    return any(mod == p or mod.startswith(p + ".") for p in prefixes)

def scope(org, packages, prefixes):
    out = {}
    prefix = subprocess.run(["lean", "--print-prefix"], cwd=org, capture_output=True, text=True,
                            check=True).stdout.strip()
    for rel, p in olean_files(os.path.join(prefix, "lib", "lean")):
        out[f"core/{rel}"] = p
    if packages:
        for pkg in TRUSTED_PKGS + PINNED_PKGS:
            root = os.path.join(packages, pkg, ".lake", "build", "lib", "lean")
            if os.path.isdir(root):
                for rel, p in olean_files(root):
                    out[f"packages/{pkg}/{rel}"] = p
    for rel, p in olean_files(os.path.join(org, ".lake", "build", "lib", "lean")):
        if under(module_of(rel), prefixes):
            out[f"project/{rel}"] = p
    return out

def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        while chunk := f.read(1 << 22):
            h.update(chunk)
    return h.hexdigest()

def hash_all(files):
    keys = sorted(files)
    with ThreadPoolExecutor(max_workers=min(32, (os.cpu_count() or 4) * 2)) as ex:
        return dict(zip(keys, ex.map(lambda k: sha(files[k]), keys)))

def packages_dir(org):
    m = json.load(open(os.path.join(org, "lake-manifest.json")))
    return os.path.normpath(os.path.join(org, m.get("packagesDir") or ".lake/packages"))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["gen", "check"])
    ap.add_argument("manifest")
    ap.add_argument("--org", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ap.add_argument("--packages", default=None, help="packages dir ('' for none)")
    ap.add_argument("--prefix", action="append", default=None)
    a = ap.parse_args()
    org = os.path.abspath(a.org)
    packages = packages_dir(org) if a.packages is None else a.packages
    hashes = hash_all(scope(org, packages, a.prefix or DEFAULT_PREFIXES))
    if a.mode == "gen":
        with open(a.manifest, "w") as f:
            f.write("# sha256 of the organiser-built .olean files (scripts/olean-manifest.py gen)\n")
            for k in sorted(hashes):
                f.write(f"{hashes[k]}  {k}\n")
        n = {t: sum(k.startswith(t) for k in hashes) for t in ("core/", "packages/", "project/")}
        print(f"olean-manifest: wrote {len(hashes)} entries ({n}) to {a.manifest}")
        return 0
    want = {}
    for line in open(a.manifest):
        if line.strip() and not line.startswith("#"):
            h, k = line.split(None, 1)
            want[k.strip()] = h
    bad = [f"changed {k}" for k in sorted(want) if k in hashes and hashes[k] != want[k]]
    bad += [f"missing {k}" for k in sorted(want) if k not in hashes]
    bad += [f"extra {k}" for k in sorted(hashes) if k not in want]
    if bad:
        for b in bad[:50]:
            print(f"olean-manifest: {b}")
        print(f"olean-manifest: FAIL ({len(bad)} differences in {len(want)} entries)")
        return 1
    print(f"olean-manifest: OK ({len(want)} files match)")
    return 0

if __name__ == "__main__":
    sys.exit(main())

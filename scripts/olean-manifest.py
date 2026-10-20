#!/usr/bin/env python3
"""Hash manifest of the organiser-built `.olean` files (A6-G0/G2).

  scripts/olean-manifest.py gen   [--org DIR] [--packages DIR] [--prefix MOD]... [--closure FILE]... OUT
  scripts/olean-manifest.py check [--org DIR] [--packages DIR] [--prefix MOD]... MANIFEST

Scope (every `*.olean`, `*.olean.server`, `*.olean.private` file of):
  core/<rel>              the toolchain (`lean --print-prefix`/lib/lean): Init, Std, Lean, Lake, ...
  packages/<pkg>/<rel>    the modules of the **trusted closure** (S9F-M2) that live in the shared
                          packages directory (`<pkg>/.lake/build/lib/lean`: Mathlib and its
                          dependencies, DESIGN §13) or in a pinned path package of the organiser's
                          lake-manifest (Clean at ext/Clean, S6b-A11). The closure is the union of the
                          `--closure` files: the organiser's `import-allowlist.txt` (gate rule 6, the
                          import closure of Mathlib, Contract, Library, Controls) and
                          `frontend-closure.txt` (the import closure of `RecursionFast.Clean`), both
                          written by scripts/org-build.sh. Without `--closure` (the mini projects of
                          the CI regressions, `--packages ''`) every package file is in scope.
  project/<rel>           the organiser package's own build (`<org>/.lake/build/lib/lean`), restricted
                          to the trusted modules: `RecursionFast.Contract(.*)`
                          (`--prefix` replaces this list, for the mini projects of the CI regressions)
`<rel>` is the module's path, e.g. `Mathlib/Order/Basic.olean`. Line format: `<sha256>  <tag>/<rel>`.

`gen` is run once on a clean organiser build, before any solution code exists on the machine; it
fails if a closure module has no `.olean` anywhere (core, packages, the organiser build), so every
entry is a module an organiser target or the allowlist needs, and nothing else (no stray module of
another package: before S9F-M2 the manifest held 710 such files, whatever the shared tree had
accumulated). `check` recomputes the scope and fails (exit 1) on a changed or missing file, and on
an **extra** one: in `core/` and `project/` any new file (e.g. `RecursionFast/Contract/Evil.olean`),
in `packages/` a new file of a manifest module (e.g. a new `.olean.private`). A new module dropped
into a package directory is out of scope: it is not in the import allowlist, so gate rule 6 rejects
importing it, and the gate treats it as untrusted (it trusts a module only by its manifest hash).
The harness runs `check` before and after every stage that runs solution code; the gate trusts a
module iff its files hash to this manifest (`scripts/Gate.lean`, `--manifest`).
"""
import argparse, json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

TRUSTED_PKGS = ["mathlib", "batteries", "aesop", "Qq", "plausible", "proofwidgets", "importGraph",
                "LeanSearchClient"]
PINNED_PKGS = ["CompPoly", "Arklib", "VCVio", "PolyFun"]
DEFAULT_PREFIXES = ["RecursionFast.Contract"]
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

def scope(org, packages, prefixes, modules=None):
    """The files in scope; `modules`: the package modules in scope (`None`: all)."""
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
                    if modules is None or module_of(rel) in modules:
                        out[f"packages/{pkg}/{rel}"] = p
        # pinned path packages (a `path` require of the organiser package, e.g. Clean at ext/Clean)
        mf = os.path.join(org, "lake-manifest.json")
        for e in (json.load(open(mf))["packages"] if os.path.exists(mf) else []):
            if e.get("type") == "path" and e["name"] in PINNED_PKGS:
                root = os.path.join(os.path.normpath(os.path.join(org, e["dir"])), ".lake", "build", "lib", "lean")
                for rel, p in (olean_files(root) if os.path.isdir(root) else []):
                    if modules is None or module_of(rel) in modules:
                        out[f"packages/{e['name']}/{rel}"] = p
    for rel, p in olean_files(os.path.join(org, ".lake", "build", "lib", "lean")):
        if under(module_of(rel), prefixes):
            out[f"project/{rel}"] = p
    return out

def hash_all(files):
    """sha256 of every file, by `sha256sum` in parallel batches (as the gate hashes; about 3x faster
    here than hashlib in threads). `-z`: one NUL-terminated record per file, names unescaped."""
    keys = sorted(files)
    def batch(ks):
        out = subprocess.run(["sha256sum", "-z", "--", *(files[k] for k in ks)], capture_output=True,
                             text=True, check=True).stdout
        return [r.split("  ", 1)[0] for r in out.split("\0")[:-1]]
    with ThreadPoolExecutor(max_workers=os.cpu_count() or 4) as ex:
        hs = [h for b in ex.map(batch, [keys[i:i + 256] for i in range(0, len(keys), 256)]) for h in b]
    assert len(hs) == len(keys)
    return dict(zip(keys, hs))

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
    ap.add_argument("--closure", action="append", default=[], help="gen: a module list (one per line)")
    a = ap.parse_args()
    org = os.path.abspath(a.org)
    packages = packages_dir(org) if a.packages is None else a.packages
    prefixes = a.prefix or DEFAULT_PREFIXES
    if a.mode == "gen":
        modules = None
        if a.closure:
            modules = {l.strip() for f in a.closure for l in open(f) if l.strip()}
        files = scope(org, packages, prefixes, modules)
        if modules is not None:       # every closure module is built somewhere
            found = {module_of(k.split("/", 1)[1] if k.startswith("core/") else k.split("/", 2)[2])
                     for k in files if not k.startswith("project/")}
            found |= {module_of(rel) for rel, _ in olean_files(os.path.join(org, ".lake", "build", "lib", "lean"))}
            lost = sorted(modules - found)
            if lost:
                print(f"olean-manifest: {len(lost)} closure module(s) have no .olean (build the organiser "
                      f"package first): {' '.join(lost[:10])}")
                return 1
        hashes = hash_all(files)
    else:
        want = {}
        for line in open(a.manifest):
            if line.strip() and not line.startswith("#"):
                h, k = line.split(None, 1)
                want[k.strip()] = h
        modules = {module_of(k.split("/", 2)[2]) for k in want if k.startswith("packages/")}
        hashes = hash_all(scope(org, packages, prefixes, modules))
    if a.mode == "gen":
        with open(a.manifest, "w") as f:
            f.write("# sha256 of the organiser-built .olean files (scripts/olean-manifest.py gen)\n")
            for k in sorted(hashes):
                f.write(f"{hashes[k]}  {k}\n")
        n = {t: sum(k.startswith(t) for k in hashes) for t in ("core/", "packages/", "project/")}
        print(f"olean-manifest: wrote {len(hashes)} entries ({n}) to {a.manifest}")
        return 0
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

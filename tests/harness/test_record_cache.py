#!/usr/bin/env python3
"""The record build cache (`harness/rfh/buildcache.py`) against a real Lake: the
repository's Lean toolchain, core only (no Mathlib, no package tree).

  python3 -I tests/harness/test_record_cache.py [WORKDIR]

A tree laid out like `evaluate.py`'s (`challenge/Challenge.lean`, `submission/*.lean`, two libs) is
built as "the record" and exported; later trees are seeded from the export and rebuilt. Checks: the
export holds only built entry modules (never `Challenge`, no `.hash`); an unchanged entry rebuilds
only `Challenge`; a changed module is not restored and its importers rebuild; a restored module the
build does not visit is pruned; a file that does not match the manifest, a forged `Challenge`,
another core commit and garbage manifests restore nothing; a seeded build is byte-identical to a
clean one.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WORK = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else tempfile.mkdtemp(prefix="rf-cache-", dir=os.environ.get("RF_TEST_TMP"))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh import buildcache  # noqa: E402

LEAN = os.path.join(subprocess.run(["lean", "--print-prefix"], cwd=ROOT, capture_output=True, text=True,
                                   check=True).stdout.strip(), "bin")
ENV = dict(os.environ, PATH=f"{LEAN}:/usr/bin:/bin", LAKE_NO_CACHE="1")
TOOLCHAIN = open(os.path.join(ROOT, "lean-toolchain")).read()
FAIL = []


def msha(src):
    p = os.path.join(src, "manifest.json")
    return buildcache._sha(p) if os.path.isfile(p) else None


def restore(src, *a, **k):
    """`buildcache.restore` with the manifest's own hash as the attested one (the bot's input)."""
    return buildcache.restore(src, *a, expect=msha(src), **k)


def check(c, what):
    print(("ok   " if c else "FAIL ") + what)
    c or FAIL.append(what)


SRC = {
    "Foo.lean": "def foo : Nat := 41\ntheorem foo_eq : foo = 41 := rfl\n",
    "Bar.lean": "import Foo\ndef bar : Nat := foo + 1\n",
    "Unused.lean": "def unused : Nat := 0\n",
    "Solution.lean": "import Bar\ntheorem sol : bar = 42 := rfl\n",
}
CHALLENGE = "theorem chal : True := trivial\n"


def tree(name, src, challenge=CHALLENGE):
    t = os.path.join(WORK, name)
    shutil.rmtree(t, ignore_errors=True)
    os.makedirs(os.path.join(t, "submission"))
    os.makedirs(os.path.join(t, "challenge"))
    open(os.path.join(t, "lean-toolchain"), "w").write(TOOLCHAIN)
    mods = [f[:-5] for f in sorted(src)]
    open(os.path.join(t, "lakefile.toml"), "w").write(
        'name = "rfentry"\n[[lean_lib]]\nname = "RFChallenge"\nsrcDir = "challenge"\nroots = ["Challenge"]\n'
        '[[lean_lib]]\nname = "RFSubmission"\nsrcDir = "submission"\nroots = ' + json.dumps(mods) + "\n")
    open(os.path.join(t, "challenge", "Challenge.lean"), "w").write(challenge)
    for f, s in src.items():
        open(os.path.join(t, "submission", f), "w").write(s)
    os.makedirs(os.path.join(t, ".lake"))
    return t


def build(t):
    out = subprocess.run(["timeout", "300", "lake", "build", "+Challenge", "+Solution"], cwd=t, env=ENV,
                         capture_output=True, text=True)
    assert out.returncode == 0, out.stdout + out.stderr
    return sorted(l.split("Built ")[1].split()[0] for l in out.stdout.splitlines() if "Built " in l)


def oleans(t):
    d = os.path.join(t, ".lake", "build", "lib", "lean")
    return sorted(f[:-6] for f in os.listdir(d) if f.endswith(".olean"))


os.makedirs(WORK, exist_ok=True)
files = sorted(SRC)
rec = tree("record", SRC)
check(build(rec) == ["Bar", "Challenge", "Foo", "Solution"], "the record builds Solution's closure and Challenge")
exp = os.path.join(WORK, "export")
shutil.rmtree(exp, ignore_errors=True)
summary = buildcache.export(rec, files + ["Challenge.lean"], exp, "c0ffee")
man = json.load(open(os.path.join(exp, "manifest.json")))
check(sorted(man["modules"]) == ["Bar", "Foo", "Solution"], f"export: the built entry modules only, never Challenge or Unused ({sorted(man['modules'])})")
check(not any(r.endswith((".hash", ".setup.json")) for m in man["modules"].values() for r in m["files"]),
      "export: no .hash or .setup.json file")
check(summary["modules"] == 3 and len(summary["manifest_sha256"]) == 64, f"export summary {summary}")

# 1. unchanged entry: nothing but Challenge is built
t = tree("same", SRC)
r = restore(exp, t, files, "c0ffee", key="k")
check(r["restored"] == ["Bar", "Foo", "Solution"] and r["key"] == "k", f"unchanged: restored {r['restored']}")
check(build(t) == ["Challenge"], "unchanged: Lake rebuilds only the fresh Challenge")
check(buildcache.prune(t, r["restored"]) == [], "unchanged: nothing pruned")

# 2. a changed Solution: Foo and Bar reused, Solution rebuilt
s2 = dict(SRC, **{"Solution.lean": "import Bar\ntheorem sol : bar = 42 := by rfl\n"})
t = tree("sol", s2)
r = restore(exp, t, sorted(s2), "c0ffee")
check(r["restored"] == ["Bar", "Foo"], f"changed Solution: restored {r['restored']}")
check(build(t) == ["Challenge", "Solution"], "changed Solution: only Challenge and Solution built")

# 3. a changed Foo: not restored; Bar restored but rebuilt (its import changed); Solution too
s3 = dict(SRC, **{"Foo.lean": "def foo : Nat := 40 + 1\ntheorem foo_eq : foo = 41 := rfl\n"})
t = tree("foo", s3)
r = restore(exp, t, sorted(s3), "c0ffee")
check(r["restored"] == ["Bar", "Solution"], f"changed Foo: restored {r['restored']}")
check(build(t) == ["Bar", "Challenge", "Foo", "Solution"], "changed Foo: Lake rebuilds its importers (trace)")
check(buildcache.prune(t, r["restored"]) == [], "changed Foo: rebuilt modules are not pruned")

# 4. a restored module Solution no longer imports is removed after the build
s4 = dict(SRC, **{"Solution.lean": "import Foo\ntheorem sol : foo = 41 := rfl\n"})
t = tree("q7", s4)
r = restore(exp, t, sorted(s4), "c0ffee")
built = build(t)
unused = buildcache.prune(t, r["restored"])
check(unused == ["Bar"] and oleans(t) == ["Challenge", "Foo", "Solution"],
      f"pruned: built {built}, pruned {unused}, left {oleans(t)}")
check(not any(f.startswith("Bar.") for d in ("lib/lean", "ir") for f in os.listdir(os.path.join(t, ".lake/build", d))),
      "no file of the pruned module is left")

# 5. a cached file that does not match the manifest is not restored
bad = os.path.join(WORK, "export-bad")
shutil.rmtree(bad, ignore_errors=True)
shutil.copytree(exp, bad)
p = os.path.join(bad, "lib/lean/Foo.olean")
os.remove(p)
shutil.copyfile(os.path.join(exp, "lib/lean/Bar.olean"), p)
t = tree("bad", SRC)
r = restore(bad, t, files, "c0ffee")
check(r["restored"] == ["Bar", "Solution"], f"tampered Foo.olean: restored {r['restored']}")
check(build(t) == ["Challenge", "Foo"], "tampered Foo.olean: Foo rebuilt, byte-identical, so its restored "
      "importers stay up to date (Lake keys them on the olean's content hash)")

# 6. a Challenge in the manifest (forged) and an entry file named Challenge.lean: never restored
forged = os.path.join(WORK, "export-forged")
shutil.rmtree(forged, ignore_errors=True)
shutil.copytree(exp, forged)
rec_ch = os.path.join(rec, ".lake/build")
fm = json.load(open(os.path.join(forged, "manifest.json")))
fm["modules"]["Challenge"] = {"source_sha256": buildcache._sha(os.path.join(rec, "challenge/Challenge.lean")),
                              "files": {}}
for rel in buildcache.outputs("Challenge"):
    if os.path.exists(os.path.join(rec_ch, rel)):
        shutil.copyfile(os.path.join(rec_ch, rel), os.path.join(forged, rel))
        fm["modules"]["Challenge"]["files"][rel] = buildcache._sha(os.path.join(rec_ch, rel))
json.dump(fm, open(os.path.join(forged, "manifest.json"), "w"))
t = tree("forged", dict(SRC, **{"Challenge.lean": CHALLENGE}))
r = restore(forged, t, files + ["Challenge.lean"], "c0ffee")
check("Challenge" not in r["restored"] and not os.path.exists(os.path.join(t, ".lake/build/lib/lean/Challenge.olean")),
      f"Challenge is never restored: restored {r['restored']}")

# 6b. the cache must be the attested record's: another manifest hash, or none, restores nothing
t = tree("unbound", SRC)
check(buildcache.restore(exp, t, files, "c0ffee", expect="0" * 64)["restored"] == [], "another attested manifest hash: nothing")
check(buildcache.restore(exp, t, files, "c0ffee")["restored"] == [], "no attested manifest hash: nothing")

# 7. another core commit, no manifest, a garbage manifest: nothing restored, no exception
t = tree("other", SRC)
check(restore(exp, t, files, "deadbeef")["restored"] == [], "another core commit: nothing restored")
check(restore(exp, t, files, None)["restored"] == [], "an unknown core commit: nothing restored")
check(restore(os.path.join(WORK, "nowhere"), t, files, "c0ffee")["restored"] == [], "no cache: nothing")
g = os.path.join(WORK, "export-garbage")
shutil.rmtree(g, ignore_errors=True)
os.makedirs(g)
for body in ("not json", "[]", '{"schema": "recursion.fast/v4/entry-build-1", "core_commit": "c0ffee", "modules": []}',
             '{"schema": "recursion.fast/v4/entry-build-1", "core_commit": "c0ffee", "modules": {"Foo": 1}}'):
    open(os.path.join(g, "manifest.json"), "w").write(body)
    r = restore(g, t, files, "c0ffee")
    check(r["restored"] == [], f"garbage manifest {body[:40]!r}: nothing restored ({r.get('note')})")
check(build(t) == ["Bar", "Challenge", "Foo", "Solution"], "after the failed restores: a clean build")

# 8. the artifacts the comparator binding hashes are byte-identical between a clean and a seeded build
t = tree("seeded", SRC)
restore(exp, t, files, "c0ffee")
build(t)
same = all(open(os.path.join(t, ".lake/build", rel), "rb").read() == open(os.path.join(rec, ".lake/build", rel), "rb").read()
           for m in ("Foo", "Bar", "Solution", "Challenge") for rel in (f"lib/lean/{m}.olean", f"ir/{m}.c"))
check(same, "seeded build: oleans and .c byte-identical to the record's clean build (Lean is deterministic)")

print(f"{len(FAIL)} failure(s)")
sys.exit(1 if FAIL else 0)

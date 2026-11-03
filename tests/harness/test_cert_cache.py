#!/usr/bin/env python3
"""`evaluate.py cert`'s handling of entry data with the organiser side stubbed (a fake Org, a stub
comparator and gate, no badge build) and the one build a real Lake run (the repository's Lean
toolchain, core only, no package tree). Checks:
  * the record cache: restore before the build, prune before the binding (Q7), export
    only for status `ok`, the `record_cache` and `entry_build` fields;
  * the entry caps (`[entry]`): a breach is the entry's REJECT, before the source rule;
    a source rule or a renderer past its timeout is the entry's REJECT, not an ERROR.

  python3 -I tests/harness/test_cert_cache.py [WORKDIR]
"""
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import types

CORE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WORK = os.path.abspath(sys.argv[1]) if len(sys.argv) > 1 else tempfile.mkdtemp(prefix="rf-certcache-", dir=os.environ.get("RF_TEST_TMP"))
sys.path.insert(0, os.path.join(CORE, "harness"))
spec = importlib.util.spec_from_file_location("evaluate", os.path.join(CORE, "harness", "evaluate.py"))
ev = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ev)

PREFIX = subprocess.run(["lean", "--print-prefix"], cwd=CORE, capture_output=True, text=True, check=True).stdout.strip()
TOOLCHAIN = open(os.path.join(CORE, "lean-toolchain")).read()
os.environ["PATH"] = f"{PREFIX}/bin:/usr/bin:/bin"
os.environ["LAKE_NO_CACHE"] = "1"
FAIL = []


def check(c, what):
    print(("ok   " if c else "FAIL ") + what)
    c or FAIL.append(what)


shutil.rmtree(WORK, ignore_errors=True)
os.makedirs(WORK)
stub = os.path.join(WORK, "stub")
os.makedirs(os.path.join(stub, ".lake/build/bin"))
for b in ("comparator", "lean4export"):
    p = os.path.join(stub, ".lake/build/bin", b)
    open(p, "w").write("#!/bin/sh\necho Building Solution\nexit 0\n")
    os.chmod(p, 0o755)
os.environ.update(COMPARATOR_HOME=stub, COMPARATOR_LEAN4EXPORT=os.path.join(stub, ".lake/build/bin/lean4export"))


class FakeOrg:
    def __init__(self, d):
        self.dir, self.prefix, self.packages = d, PREFIX, d
        self.manifest = self.allowlist = os.path.join(WORK, "none")
        self.tools = stub

    def ro_roots(self, *more):
        return ()

    def manifest_ok(self, log):
        return True

    def environment(self):
        return {"core_commit": "c0ffee", "manifest_sha256": "-", "allowlist_sha256": "-"}


def mkfresh(t, org, entry, challenge, files):
    os.makedirs(os.path.join(t, "challenge"))
    os.makedirs(os.path.join(t, "submission"))
    open(os.path.join(t, "lean-toolchain"), "w").write(TOOLCHAIN)
    open(os.path.join(t, "challenge", "Challenge.lean"), "w").write("theorem chal : True := trivial\n")
    for f in files:
        shutil.copy(os.path.join(entry, "lean", f), os.path.join(t, "submission", f))
    mods = [f[:-5] for f in files]
    open(os.path.join(t, "lakefile.toml"), "w").write(
        'name = "rfentry"\n[[lean_lib]]\nname = "RFChallenge"\nsrcDir = "challenge"\nroots = ["Challenge"]\n'
        '[[lean_lib]]\nname = "RFSubmission"\nsrcDir = "submission"\nroots = ' + json.dumps(mods) + "\n")


def sandboxed(org, cmd, tree, log, rw=(), mem="12G", env=None, timeout=300, extra=()):
    if cmd[1:2] == ["build"]:
        return subprocess.run(cmd, cwd=tree, stdout=open(log, "ab"), stderr=subprocess.STDOUT, timeout=timeout).returncode
    open(log, "a").close()
    return 0        # the gate: PASS


def build_badge(org, tree, log, timeout, res):
    res["badge_s"] = 0.0
    out = os.path.join(os.path.dirname(tree), "badge")
    os.makedirs(out)
    open(os.path.join(out, "verify"), "w").write("stub")
    return out


ev.Org, ev.mkfresh, ev.sandboxed, ev.build_badge = FakeOrg, mkfresh, sandboxed, build_badge


def entry(name, src):
    e = os.path.join(WORK, name)
    os.makedirs(os.path.join(e, "lean"))
    shutil.copy(os.path.join(CORE, "tests/harness/ws-entry/claim.json"), e)
    for f, s in src.items():
        open(os.path.join(e, "lean", f), "w").write(s)
    return e


def msha(d):
    p = os.path.join(d or "", "manifest.json")
    return ev.buildcache._sha(p) if d and os.path.isfile(p) else None


def cert(name, src, seed=None, export=True, expect="manifest", incumbent=False):
    a = types.SimpleNamespace(org=CORE, season=os.path.join(CORE, "harness/season.toml"), work=os.path.join(WORK, f"w-{name}"),
                              entry=entry(name, src), out=os.path.join(WORK, f"{name}.json"), nanoda=False,
                              cert_mem="4G", nanoda_mem="4G", record_cache=seed, record_cache_key="rf-record-build-x-pr1" if seed else None,
                              record_manifest_sha256=msha(seed) if expect == "manifest" else expect, incumbent=incumbent,
                              export_build=os.path.join(WORK, f"export-{name}") if export else None)
    ev.cert_job(a)
    return json.load(open(a.out)), a


SRC = {"Foo.lean": "def foo : Nat := 41\n", "Unused.lean": "def u : Nat := 0\n",
       "Bar.lean": "import Foo\ndef bar : Nat := foo + 1\n", "Solution.lean": "import Bar\ntheorem sol : bar = 42 := rfl\n"}
r1, a1 = cert("record", SRC)
check(r1["status"] == "ok", f"record: status {r1['status']} {r1['reasons']}")
check("record_cache" not in r1 and r1.get("entry_build", {}).get("modules") == 3, f"record: entry_build {r1.get('entry_build')}")
check(os.path.exists(os.path.join(a1.export_build, "manifest.json")), "record: export written")

s2 = dict(SRC, **{"Solution.lean": "import Foo\ntheorem sol : foo = 41 := rfl\n"})
r2, a2 = cert("next", s2, seed=a1.export_build)
rc = r2.get("record_cache") or {}
check(r2["status"] == "ok", f"next: status {r2['status']} {r2['reasons']}")
check(rc.get("restored") == ["Bar", "Foo"] and rc.get("unused") == ["Bar"] and rc.get("key") == "rf-record-build-x-pr1",
      f"next: record_cache {rc}")
check(r2["built_modules"] == ["Challenge", "Foo", "Solution"], f"next: built_modules (Q7) {r2['built_modules']}")
log = open(os.path.join(a2.work, "build.log")).read()
check("Built Foo" not in log and "Built Solution" in log, "next: Foo reused, Solution built")

r3, a3 = cert("broken", dict(SRC, **{"Solution.lean": "import Bar\ntheorem sol : bar = 43 := rfl\n"}), seed=a1.export_build)
check(r3["status"] == "reject" and "entry_build" not in r3 and not os.path.exists(a3.export_build),
      f"a rejected certificate exports nothing ({r3['status']})")

r5, a5 = cert("unbound", s2, seed=a1.export_build, expect="0" * 64, export=False)
check(r5["status"] == "ok" and r5["record_cache"]["restored"] == [] and "attested" in r5["record_cache"].get("note", ""),
      f"a cache whose manifest is not the attested record's restores nothing: {r5.get('record_cache')}")
r6, a6 = cert("incumbent", SRC, seed=a1.export_build, export=False, incumbent=True)
check(r6["status"] == "ok" and r6["build_cap"] == "incumbent_build_s" and r2["build_cap"] == "build_s",
      f"the incumbent's build cap is incumbent_build_s, a candidate's build_s ({r6.get('build_cap')}, {r2.get('build_cap')})")
r4, a4 = cert("noseed", SRC, export=False)
check(r4["status"] == "ok" and "record_cache" not in r4 and "entry_build" not in r4, "without the flags: as before")

# the entry caps: a junk file past lean_bytes is the entry's REJECT before the source rule runs
small = os.path.join(WORK, "small.toml")
open(small, "w").write(open(os.path.join(CORE, "harness/season.toml")).read().replace("lean_bytes = 33554432", "lean_bytes = 4096"))
calls = []
real_sh = ev.sh
ev.sh = lambda cmd, **kw: (calls.append(cmd), real_sh(cmd, **kw))[1]


def cert_with(name, src, season, extra=None):
    e = entry(name, src)
    for rel, data in (extra or {}).items():
        os.makedirs(os.path.dirname(os.path.join(e, rel)), exist_ok=True)
        open(os.path.join(e, rel), "wb").write(data)
    a = types.SimpleNamespace(org=CORE, season=season, work=os.path.join(WORK, f"w-{name}"), entry=e,
                              out=os.path.join(WORK, f"{name}.json"), nanoda=False, cert_mem="4G", nanoda_mem="4G",
                              record_cache=None, record_cache_key=None, record_manifest_sha256=None, incumbent=False,
                              export_build=None)
    ev.cert_job(a)
    return json.load(open(a.out))


r = cert_with("junk", SRC, small, {"lean/Junk.lean": b"-- junk\n" * 1024})
check(r["status"] == "reject" and "lean_bytes = 4096" in " ".join(r["reasons"])
      and not any("source-rule.py" in " ".join(map(str, c)) for c in calls),
      f"lean/ past lean_bytes: REJECT before the source rule ({r['status']}: {r['reasons']})")
r = cert_with("bigfile", SRC, os.path.join(CORE, "harness/season.toml"))
check(r["status"] == "ok" and r["entry_size"]["lean_files"] == 4, f"within the caps: ok, sizes {r.get('entry_size')}")
small2 = os.path.join(WORK, "small2.toml")
open(small2, "w").write(open(os.path.join(CORE, "harness/season.toml")).read().replace("prover_files = 256", "prover_files = 1"))
r = cert_with("provers", SRC, small2, {"prover/a.s": b"", "prover/b.s": b""})
check(r["status"] == "reject" and "prover_files = 1" in " ".join(r["reasons"]), f"prover/ past prover_files: {r['reasons']}")
small3 = os.path.join(WORK, "small3.toml")
open(small3, "w").write(open(os.path.join(CORE, "harness/season.toml")).read().replace("claim_bytes = 65536", "claim_bytes = 10"))
r = cert_with("claim", SRC, small3)
check(r["status"] == "reject" and "claim_bytes = 10" in " ".join(r["reasons"]), f"claim.json past claim_bytes: {r['reasons']}")

# a source rule (or a renderer) past its timeout: the entry's REJECT, not an ERROR
for tool in ("source-rule.py", "render-challenge.py"):
    def slow(cmd, _tool=tool, **kw):
        if any(_tool in str(c) for c in cmd):
            raise subprocess.TimeoutExpired(cmd, ev.TIMEOUT)
        return real_sh(cmd, **kw)
    ev.sh = slow
    r = cert_with(f"slow-{tool[:6]}", SRC, os.path.join(CORE, "harness/season.toml"))
    check(r["status"] == "reject" and "did not" in " ".join(r["reasons"]), f"{tool} past its timeout: {r['status']} {r['reasons']}")
ev.sh = real_sh
print(f"{len(FAIL)} failure(s)")
sys.exit(1 if FAIL else 0)

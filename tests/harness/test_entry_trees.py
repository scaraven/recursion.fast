#!/usr/bin/env python3
"""What an entry's setup tree, its binary and a dying runner can do to a benchmark (review R3 H1-H3,
M1): never an organiser ERROR, never a pass.

  python3 tests/harness/test_entry_trees.py

Each case runs a prover through `harness/evaluate.py`'s `bench_job` (the mock badge; a prover that
implements `setup` only, so a run whose setup succeeds is REJECTed at its first request):

1. a setup file and directory whose names are not UTF-8 (`\\377`): the setup is accepted and hashed,
   the verdict is the entry's REJECT at `request`, never a harness ERROR (H1);
2. a setup tree 1,000 directories deep (relative paths up to 1,999 bytes): accepted, no recursion
   limit reached (H2); one 1,100 deep (paths above `MAX_REL_PATH` = 2,048 bytes) and one of 70,000
   entries (above `SETUP_ENTRIES` = 65,536): the entry's REJECT at `prover` (H2, M1);
3. a setup that writes without bound (fallocate of 2 GiB, a season whose prover cap is 512 MiB): its
   /setup is a private tmpfs charged to its memory cap, so the work disk is not filled (its free
   space within 64 MiB of before) and the setup is the entry's REJECT at `prover` (H3; systemd memory
   scopes only: under the prlimit fallback a tmpfs is not capped and the case is skipped);
4. the prover binary counts toward `setup_cap` (M1): a setup that fits alone but not with the binary
   is the entry's REJECT at `prover`, naming both;
5. a runner that dies after a checkpoint (its result file says `benchmark: incomplete`, stage not
   `done`) is a harness ERROR in `evaluate.py`, never an ACCEPT (H3);
6. a run log that cannot be written (ENOSPC: `/dev/full` behind its descriptor) does not stop the
   runner: the setup's failure is still the result's `benchmark: fail`, stage `done` (H3).
"""
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
FAILS = []


def check(cond, what):
    print(("ok   " if cond else "FAIL ") + what)
    if not cond:
        FAILS.append(what)


def badge_dir(tmp):
    badge = os.path.join(tmp, "badge")
    os.makedirs(badge)
    for f in sorted(x for x in os.listdir(os.path.join(HERE, "mock_badge")) if os.path.isfile(os.path.join(HERE, "mock_badge", x))):
        shutil.copy(os.path.join(HERE, "mock_badge", f), badge)
    shutil.copy(os.path.join(ROOT, "tests", "service", "wots_ref.py"), badge)
    shutil.copy(os.path.join(ROOT, "harness", "rfh", "signed.py"), badge)
    shutil.copy(os.path.join(ROOT, "tests", "service", "keccak_ref.c"), badge)
    os.makedirs(os.path.join(badge, "rfh"))
    shutil.copy(os.path.join(ROOT, "harness", "rfh", "keccak.py"), os.path.join(badge, "rfh"))
    return badge


def season(tmp, name, **subs):
    """smoke.toml with the given `key = value` lines replaced (the first occurrence of each key)."""
    lines = open(os.path.join(ROOT, "harness", "smoke.toml")).read().splitlines()
    for k, v in subs.items():
        i = next(j for j, l in enumerate(lines) if l.split("=")[0].strip() == k)
        lines[i] = f"{k} = {v}"
    path = os.path.join(tmp, f"{name}.toml")
    open(path, "w").write("\n".join(lines) + "\n")
    return path


def evaluate():
    spec = importlib.util.spec_from_file_location("evaluate", os.path.join(ROOT, "harness", "evaluate.py"))
    ev = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ev)
    ev.PART_S = 900
    return ev


def bench(tmp, name, setup_c, season_path=None):
    """`bench_job` of a prover whose `setup` runs `setup_c` (C statements, in /setup); its result."""
    d = os.path.join(tmp, name)
    os.makedirs(os.path.join(d, "entry", "prover"))
    c = os.path.join(d, "p.c")
    open(c, "w").write('#define _GNU_SOURCE\n#include <string.h>\n#include <stdio.h>\n#include <unistd.h>\n#include <fcntl.h>\n'
                       '#include <sys/stat.h>\nint main(int c, char **v){if(c>1&&!strcmp(v[1],"setup")){chdir(v[2]);'
                       + setup_c + '}return 0;}\n')
    subprocess.run(["gcc", "-S", "-O1", "-w", "-o", os.path.join(d, "entry", "prover", "p.s"), c], check=True)
    a = SimpleNamespace(season=season_path or os.path.join(ROOT, "harness", "smoke.toml"), entry=os.path.join(d, "entry"),
                        work=os.path.join(d, "work"), out=os.path.join(d, "result.json"), parts=None,
                        service=os.path.join(ROOT, "service", "target", "release", "rf-oracle"),
                        bench=os.path.join(ROOT, "service", "target", "release", "rf-bench"))
    return evaluate().bench_job(a, {"status": "ok", "badge_dir": BADGE})


def summary(res):
    return f"{res.get('verdict')} at {res.get('reject_stage')}: {' '.join(res.get('reasons', []))[:300]}"


def main():
    global BADGE
    from rfh.sandbox import memcap_method
    if memcap_method() == "prlimit":           # the test-only override (run-benchmark.py's organiser ERROR)
        os.environ["RF_ALLOW_PRLIMIT"] = "1"
    tmp = tempfile.mkdtemp(prefix="rf-entry-trees-", dir=os.environ.get("RF_TEST_TMP"))
    BADGE = badge_dir(tmp)

    # 1. names that are not UTF-8
    res = bench(tmp, "badname", 'close(creat("\\377",0644));mkdir("\\376d",0700);close(creat("\\376d/\\375",0644));'
                                'symlink("\\374",  "\\373");')
    st = res.get("setup") or {}
    check(res.get("verdict") == "REJECT" and res.get("reject_stage") == "request" and st.get("ok") and st.get("sha256"),
          f"a setup with names that are not UTF-8 is accepted and hashed; the verdict is the entry's: {summary(res)}")

    # 2. depth and entries
    res = bench(tmp, "deep1000", 'for(int i=0;i<1000;i++){mkdir("a",0700);chdir("a");}close(creat("f",0644));')
    st = res.get("setup") or {}
    check(res.get("verdict") == "REJECT" and res.get("reject_stage") == "request" and st.get("ok") and st.get("sha256"),
          f"a setup tree 1,000 directories deep is walked, hashed and copied (no recursion limit): {summary(res)}")
    res = bench(tmp, "deep1100", 'for(int i=0;i<1100;i++){mkdir("a",0700);chdir("a");}')
    check(res.get("verdict") == "REJECT" and res.get("reject_stage") == "prover" and "setup" in summary(res),
          f"a setup tree with paths above 2,048 bytes is the entry's REJECT at prover: {summary(res)}")
    res = bench(tmp, "many", 'char b[32];for(int i=0;i<70000;i++){sprintf(b,"%d",i);close(creat(b,0644));}')
    check(res.get("verdict") == "REJECT" and res.get("reject_stage") == "prover" and "65536" in summary(res),
          f"a setup of 70,000 entries is the entry's REJECT at prover: {summary(res)}")

    # 3. a setup that writes without bound: its tmpfs fills its memory cap, never the work disk
    if memcap_method() == "systemd":
        small = season(tmp, "small-mem", prover='"512M"')
        free0 = shutil.disk_usage(tmp).free
        res = bench(tmp, "unbounded", 'int f=open("big",O_WRONLY|O_CREAT,0644);fallocate(f,0,0,2LL<<30);'
                                      'for(int i=0;i<4096;i++)write(f,"x",1);', small)
        used = free0 - shutil.disk_usage(tmp).free
        check(res.get("verdict") == "REJECT" and res.get("reject_stage") == "prover" and used < 64 << 20,
              f"a setup writing 2 GiB under a 512 MiB cap: the work disk {used >> 20} MiB fuller (< 64), the entry's "
              f"REJECT at prover: {summary(res)}")
    else:
        print("skip a setup writing without bound: no systemd memory scopes here (a tmpfs is not capped by prlimit)")

    # 4. the binary counts toward setup_cap
    capped = season(tmp, "small-cap", setup_cap=1 << 20)
    res = bench(tmp, "binary", 'int f=open("data",O_WRONLY|O_CREAT,0644);static char z[900<<10];write(f,z,sizeof z);', capped)
    check(res.get("verdict") == "REJECT" and res.get("reject_stage") == "prover" and "prover binary" in summary(res),
          f"a 900 KiB setup and the binary together above setup_cap = 1 MiB: the entry's REJECT at prover: {summary(res)}")

    # 5. a runner that died after a checkpoint
    ev = evaluate()
    out = os.path.join(tmp, "died.json")

    def died(cmd, timeout=None):
        json.dump({"benchmark": "incomplete", "stage": "stream", "reasons": []}, open(out, "w"))
        return subprocess.CompletedProcess(cmd, -9)
    ev.subprocess = SimpleNamespace(run=died, TimeoutExpired=subprocess.TimeoutExpired)
    a = SimpleNamespace(season=os.path.join(ROOT, "harness", "smoke.toml"), entry=tmp, work=os.path.join(tmp, "w-died"),
                        out=out, parts=None, service="x", bench="x")
    res = ev.bench_job(a, {"status": "ok", "badge_dir": BADGE})
    check(res.get("verdict") == "ERROR" and res.get("benchmark") == "error" and "without completing" in summary(res),
          f"a runner that died after its checkpoint `stream` (benchmark: incomplete): {summary(res)}")

    # 6. a run log that cannot be written (the R3 H3 demonstration, ported)
    d = os.path.join(tmp, "logfull")
    os.makedirs(os.path.join(d, "entry", "prover"))
    open(os.path.join(d, "entry", "prover", "p.s"), "w").write("")
    probe = os.path.join(d, "probe.py")
    open(probe, "w").write(f'''
import os, sys, json
H = {os.path.join(ROOT, "harness")!r}
sys.path.insert(0, H)
import rfh.prover as P
def fake_setup(self, timeout, size_cap=None, max_entries=None):
    for fd in os.listdir("/proc/self/fd"):          # the run log's descriptor now writes to /dev/full
        try:
            if os.readlink(f"/proc/self/fd/{{fd}}").endswith("/work/run.log"):
                os.dup2(os.open("/dev/full", os.O_WRONLY), int(fd))
        except OSError:
            pass
    return False, 1.0, "the setup directory holds 999999999999 bytes, above setup_cap = 1"
P.Run.setup = fake_setup
sys.argv = ["run-benchmark.py", "--season", H + "/smoke.toml", "--entry", {os.path.join(d, "entry")!r}, "--badge", "x",
            "--service", "/bin/true", "--bench", "/bin/true", "--work", {os.path.join(d, "work")!r}, "--out", {os.path.join(d, "out.json")!r}]
g = {{"__name__": "rb", "__file__": H + "/run-benchmark.py"}}
exec(compile(open(H + "/run-benchmark.py").read(), "run-benchmark.py", "exec"), g)
g["build"] = lambda *a, **k: (True, {{"binary_sha256": "x", "binary_bytes": 0}})
g["build_calib"] = g["build_scrub"] = lambda d: ("/bin/true", {{}})
print("rc", g["main"]())
''')
    p = subprocess.run([sys.executable, "-I", probe], capture_output=True, text=True, timeout=300,
                       env=dict(os.environ, RF_ALLOW_PRLIMIT="1"))
    r = json.load(open(os.path.join(d, "out.json"))) if os.path.exists(os.path.join(d, "out.json")) else {}
    check(r.get("benchmark") == "fail" and r.get("stage") == "done" and r.get("reject_stage") == "prover" and "rc 1" in p.stdout,
          f"a run log on a full disk: the runner still writes its REJECT (benchmark {r.get('benchmark')}, stage "
          f"{r.get('stage')}, {p.stdout.strip()[-80:]!r} {p.stderr.strip()[-200:]!r})")

    print(f"{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())

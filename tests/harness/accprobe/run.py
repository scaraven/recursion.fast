#!/usr/bin/env python3
"""`acc` on a synthetic 2^16-query trace, timed by the badge's own `verify`; and the badge's glue
against a hostile submission.

  python3 tests/harness/accprobe/run.py         (from the repository root, after `lake build` and
                                                 `harness/org-setup.sh` steps 2-3)

Renders the badge's per-entry module (`harness/badge/Verify.lean.in`, around the organiser's
prebuilt glue `RecursionFast/Badge.lean`) around `AccProbeSub`, `HostileSub` and `MemoSub`, builds
the executables as one Lake package in `.lake/rf/accprobe` (requiring the organiser by path), and
runs them pinned to one core through the runner's own badge runner (`rfh.checks.Badge` without the
sandbox, `tests/harness/localbadge.py`: the organiser's warm-up input first, the start-up cap of
`harness/season.toml`, the request loop that also times each request from outside; the overhead of
that external time is printed).

1. `AccProbeSub`: its verifier asks `2^16` fixed queries of 100 bytes (signed by the service) and
   accepts. It is also the core CI's test of the organiser's canaries on a non-empty trace
   (`tests/harness/canaries.py`): every mutation that `acc` rejects (the file one byte longer or
   shorter, one answer or one query changed, an entry appended, a chain value or the index of the
   signature changed) is rejected by organiser code alone; each must be rejected, and the file
   itself accepted.
2. `HostileSub`: a verifier that accepts a 7-byte proof for the zero statement after about 0.1 s of
   work, in a module that declares high-priority `HSub Nat Nat Nat`, `HOr UInt64 UInt64 UInt64` and
   `GetElem? (Array Char) Nat Char` instances. The badge's timer, file parser and hex parser are
   compiled without them, so the proof must be accepted with the badge's own time above 50 ms (the
   hostile `-` reports such a difference as 1 ns), and rejected for another statement and when one
   byte longer. With the glue elaborated beside the entry (the badge before this fix), the proof
   is rejected: the hex parser reads the key as zeros and the length word 7 as 1000.
3. `MemoSub`: a verifier of about 0.5 to 1 s per statement that memoises across the checks of one
   process (a closed-term trie of thunks). Judged as the runner judges the final output (one
   fresh process warmed with the organiser's input, then `Bench.v_capped`'s two re-timings, each
   in a fresh process), its time must be above `v_cap`, so the entry would be REJECTed; warmed with
   the judged input itself (the runner before review R7) the judged check answers from the memo,
   below `v_cap`, which the test also shows.
4. The gate's rule 9 (`--wiring`) passes on every per-entry module (the hostile instances change
   nothing there).

Exit 1 on any failure.
"""
import json
import os
import shutil
import struct
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh.bench import Bench, Params  # noqa: E402
from rfh.service import Client, Service  # noqa: E402
from rfh.signed import from_wire  # noqa: E402

sys.path.insert(0, os.path.join(ROOT, "tests", "harness"))
from canaries import organiser_canaries  # noqa: E402
from localbadge import LocalBadge  # noqa: E402

D = os.path.join(ROOT, ".lake", "rf", "accprobe")
SUBS = {"accprobe": "AccProbeSub", "hostile": "HostileSub", "memo": "MemoSub"}   # executable: submission module
SEASON = Params.load(os.path.join(ROOT, "harness", "season.toml"))


def build():
    shutil.rmtree(D, ignore_errors=True)
    os.makedirs(os.path.join(D, "src"))
    tmpl = open(os.path.join(ROOT, "harness", "badge", "Verify.lean.in")).read()
    exes = ""
    for exe, sub in SUBS.items():
        shutil.copy(os.path.join(ROOT, "tests", "harness", "accprobe", f"{sub}.lean"), os.path.join(D, "src"))
        open(os.path.join(D, "src", f"RFBadge{sub}.lean"), "w").write(tmpl.replace("{{solution_module}}", sub))
        exes += f'[[lean_exe]]\nname = "{exe}"\nsrcDir = "src"\nroot = "RFBadge{sub}"\n'
    # its own Lake package that requires the organiser by path, so that nothing is built into the
    # organiser's `.lake/build` (whose modules every evaluation tree sees)
    m = json.load(open(os.path.join(ROOT, "lake-manifest.json")))
    pk = os.path.realpath(os.path.join(ROOT, m.get("packagesDir") or ".lake/packages"))
    open(os.path.join(D, "lakefile.toml"), "w").write(
        f'name = "accprobe"\npackagesDir = {json.dumps(pk)}\n[[require]]\nname = "RecursionFast"\npath = {json.dumps(ROOT)}\n'
        f'[[lean_lib]]\nname = "AccProbe"\nsrcDir = "src"\nroots = {json.dumps(list(SUBS.values()))}\n' + exes)
    for p in m["packages"]:
        p["inherited"] = True
    m["packages"].insert(0, {"type": "path", "scope": "", "name": "RecursionFast", "manifestFile": "lake-manifest.json",
                             "inherited": False, "dir": ROOT, "configFile": "lakefile.toml"})
    m["name"], m["packagesDir"] = "accprobe", pk
    json.dump(m, open(os.path.join(D, "lake-manifest.json"), "w"), indent=1)
    shutil.copy(os.path.join(ROOT, "lean-toolchain"), D)
    subprocess.run(["lake", "build", *SUBS], cwd=D, check=True, timeout=3600)


def badge(exe):
    """The runner's badge runner on the executable `exe`, with the season's start-up cap."""
    return LocalBadge([os.path.join(D, ".lake", "build", "bin", exe)], os.path.join(D, "scratch-" + exe),
                      SEASON.badge_start_s)


def run(exe, items, warm=True):
    """`exe` on (vk, stmt, path under D) items in one fresh process, warmed with the organiser's
    input (`warm`): [(accepted, judged ns, external ns, badge ns)]; exits on a failed run."""
    b = badge(exe)
    res = b.verify([(vk, c, os.path.relpath(f, D)) for vk, c, f in items], D, 600, warm=warm)
    return [(ok, ns, ext, own) for (ok, ns), (ext, own) in zip(res, b.last)]


def main():
    build()
    svc = Service(os.path.join(ROOT, "service", "target", "release", "rf-oracle"), os.path.join(D, "svc")).start()
    c = Client(svc.socket_path)
    qs = [struct.pack("<Q", k) + bytes(92) for k in range(1 << 16)]
    s = from_wire(b"", qs, c.sign(qs))
    h = from_wire(bytes(7), [], c.sign([]))
    c_memo = c.sign([])
    c.close()
    svc.stop()
    core = max(os.sched_getaffinity(0))
    m = from_wire(bytes(7), [], c_memo)
    fails = 0

    def report(name, want, ok, ns, ext, own, extra=True):
        nonlocal fails
        good = ok == (want == "accept") and extra
        fails += not good
        print(f"{'ok  ' if good else 'FAIL'} {name:18} {'accept' if ok else 'reject':7} {ns / 1e6:9.2f} ms "
              f"(external {ext / 1e6:.2f}, badge {own / 1e6:.2f}) (must {want})")

    # 1. the 2^16-query probe and the organiser's canaries
    good = os.path.join(D, "good.bin")
    open(good, "wb").write(s.encode())
    cases = [("good", good, "accept")] * 5
    for name, data in organiser_canaries(s.encode()):
        open(os.path.join(D, f"{name}.bin"), "wb").write(data)
        cases.append((name, os.path.join(D, f"{name}.bin"), "reject"))
    zero = bytes(32)
    print(f"file: {os.path.getsize(good)} bytes, 2^16 queries of 100 bytes, pinned core {core}")
    res = run("accprobe", [(svc.vk, zero, f) for _, f, _ in cases])
    for (name, _, want), (ok, ns, ext, own) in zip(cases, res):
        report(name, want, ok, ns, ext, own)
    over = sorted(ext - own for _, _, ext, own in res)
    print(f"external minus badge time: median {over[len(over) // 2] / 1e3:.0f} us, max {over[-1] / 1e3:.0f} us "
          f"(the request's round trip, the file read and the hex parse)")

    # 2. the hostile submission
    hf, hl = os.path.join(D, "hostile.bin"), os.path.join(D, "hostile-long.bin")
    open(hf, "wb").write(h.encode())
    open(hl, "wb").write(h.encode() + b"\x00")
    flip = bytes([1]) + zero[1:]
    res = run("hostile", [(svc.vk, zero, hf), (svc.vk, zero, hf), (svc.vk, flip, hf), (svc.vk, zero, hl)])
    for (name, want, slow), (ok, ns, ext, own) in zip(
            [("hostile", "accept", True), ("hostile again", "accept", True), ("hostile stmt-bit", "reject", False),
             ("hostile file+1", "reject", False)], res):
        report(name, want, ok, ns, ext, own, not slow or own > 50_000_000)

    # 3. the memoising submission, judged as the runner judges the final output
    mf = os.path.join(D, "memo.bin")
    open(mf, "wb").write(m.encode())
    item = (svc.vk, zero, os.path.relpath(mf, D))
    b = Bench.__new__(Bench)
    b.p, b.badge, b.store = SEASON, badge("memo"), D
    b.deadline = (time.monotonic() + 600, "the test's bound")
    ((ok, ns),) = b.check([item], "the final output")
    v, runs, again = b.v_capped(item, ns, "the final output (V above v_cap, timed again)")
    cap = SEASON.v_cap_ms * 1e6
    good = ok and again and v > cap
    fails += not good
    print(f"{'ok  ' if good else 'FAIL'} memo, judged as the final output: V = {v / 1e6:.2f} ms (the least of "
          f"{[round(r / 1e6, 2) for r in runs]}), above v_cap = {SEASON.v_cap_ms:g} ms: REJECT (must be above)")
    old = run("memo", [(svc.vk, zero, mf), (svc.vk, zero, mf)], warm=False)
    good = all(r[0] for r in old) and old[1][1] < cap
    fails += not good
    print(f"{'ok  ' if good else 'FAIL'} memo, warmed with the judged input (before review R7): judged "
          f"{old[1][1] / 1e6:.2f} ms after a {old[0][1] / 1e6:.0f} ms warm-up, below v_cap: it would have passed")

    # 4. rule 9 on every per-entry module
    gate = os.path.join(ROOT, "harness", "lean-tools", ".lake", "build", "bin", "gate")
    for sub in SUBS.values():
        r = subprocess.run(["lake", "env", gate, "--wiring", f"RFBadge{sub}", "--manifest",
                            os.path.join(ROOT, ".lake", "rf", "manifest.sha256")], cwd=D, capture_output=True,
                           text=True, timeout=300)
        ok = r.returncode == 0 and "gate: PASS" in r.stdout
        fails += not ok
        print(f"{'ok  ' if ok else 'FAIL'} gate rule 9 on RFBadge{sub}: {(r.stdout.strip().splitlines() or [''])[-1]}")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())

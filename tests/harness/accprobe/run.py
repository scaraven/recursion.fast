#!/usr/bin/env python3
"""`acc` on a synthetic 2^16-query trace, timed by the badge's own `verify` (C-m3; V4-A7 (d)).

  python3 tests/harness/accprobe/run.py         (from the repository root, after `lake build`)

Renders the badge (`harness/badge/Common.lean.in`, `Verify.lean.in`) around `AccProbeSub`, builds it
as its own Lake package in `.lake/rf/accprobe` (requiring the organiser by path), gets the service to sign the probe's
2^16 queries (100 bytes each), writes the signed-proof file, and runs `verify` pinned to one core
several times. It is also the core CI's test of the organiser's canaries on a non-empty trace
(V4-A9, `tests/harness/canaries.py`): the probe's verifier accepts once it has asked its queries, so
every mutation that `acc` rejects (the file one byte longer or shorter, one answer or one query
changed, an entry appended, a chain value or the index of the signature changed) is rejected by
organiser code alone; each must be rejected, and the file itself accepted (exit 1 otherwise).
"""
import json
import os
import shutil
import struct
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh.service import Client, Service  # noqa: E402
from rfh.signed import from_wire  # noqa: E402

sys.path.insert(0, os.path.join(ROOT, "tests", "harness"))
from canaries import organiser_canaries  # noqa: E402

D = os.path.join(ROOT, ".lake", "rf", "accprobe")


def main():
    shutil.rmtree(D, ignore_errors=True)
    os.makedirs(os.path.join(D, "src"))
    shutil.copy(os.path.join(ROOT, "tests", "harness", "accprobe", "AccProbeSub.lean"), os.path.join(D, "src"))
    for name in ("Common", "Verify"):
        src = open(os.path.join(ROOT, "harness", "badge", f"{name}.lean.in")).read().replace("{{solution_module}}", "AccProbeSub")
        open(os.path.join(D, "src", f"RFBadge{name}.lean"), "w").write(src)
    # its own Lake package that requires the organiser by path, so that nothing is built into the
    # organiser's `.lake/build` (whose modules every evaluation tree sees)
    m = json.load(open(os.path.join(ROOT, "lake-manifest.json")))
    pk = os.path.realpath(os.path.join(ROOT, m.get("packagesDir") or ".lake/packages"))
    open(os.path.join(D, "lakefile.toml"), "w").write(
        f'name = "accprobe"\npackagesDir = {json.dumps(pk)}\n[[require]]\nname = "RecursionFast"\npath = {json.dumps(ROOT)}\n'
        '[[lean_lib]]\nname = "AccProbe"\nsrcDir = "src"\nroots = ["AccProbeSub", "RFBadgeCommon"]\n'
        '[[lean_exe]]\nname = "accprobe"\nsrcDir = "src"\nroot = "RFBadgeVerify"\n')
    for p in m["packages"]:
        p["inherited"] = True
    m["packages"].insert(0, {"type": "path", "scope": "", "name": "RecursionFast", "manifestFile": "lake-manifest.json",
                             "inherited": False, "dir": ROOT, "configFile": "lakefile.toml"})
    m["name"], m["packagesDir"] = "accprobe", pk
    json.dump(m, open(os.path.join(D, "lake-manifest.json"), "w"), indent=1)
    shutil.copy(os.path.join(ROOT, "lean-toolchain"), D)
    subprocess.run(["lake", "build", "accprobe"], cwd=D, check=True, timeout=3600)
    exe = os.path.join(D, ".lake", "build", "bin", "accprobe")
    qs = [struct.pack("<Q", k) + bytes(92) for k in range(1 << 16)]
    svc = Service(os.path.join(ROOT, "service", "target", "release", "rf-oracle"), os.path.join(D, "svc")).start()
    c = Client(svc.socket_path)
    s = from_wire(b"", qs, c.sign(qs))
    c.close()
    svc.stop()
    good = os.path.join(D, "good.bin")
    open(good, "wb").write(s.encode())
    cases = [("good", "good.bin", "accept")] * 5
    for name, data in organiser_canaries(s.encode()):
        open(os.path.join(D, f"{name}.bin"), "wb").write(data)
        cases.append((name, f"{name}.bin", "reject"))
    stmt = bytes(32).hex()
    with open(os.path.join(D, "list.txt"), "w") as f:
        for _, file, _ in cases:
            f.write(f"{svc.vk.hex()} {stmt} {os.path.join(D, file)}\n")
    core = max(os.sched_getaffinity(0))
    out = subprocess.run(["taskset", "-c", str(core), exe, "--batch", os.path.join(D, "list.txt")], capture_output=True,
                         text=True, timeout=600).stdout.split("\n")
    size = os.path.getsize(good)
    print(f"file: {size} bytes, 2^16 queries of 100 bytes, pinned core {core}")
    fails = 0
    for (name, _, want), line in zip(cases, out + [""] * len(cases)):
        w = line.split()
        ok = len(w) == 2 and w[0] == want and w[1].isdigit()
        fails += not ok
        got = f"{w[0]:7} {int(w[1]) / 1e6:9.2f} ms" if len(w) == 2 and w[1].isdigit() else repr(line)
        print(f"{'ok  ' if ok else 'FAIL'} {name:14} {got} (must {want})")
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())

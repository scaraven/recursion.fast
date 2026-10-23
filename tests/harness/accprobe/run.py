#!/usr/bin/env python3
"""`acc` on a synthetic 2^16-query trace, timed by the badge's own `verify` (C-m3; V4-A7 (d)).

  python3 tests/harness/accprobe/run.py         (from the repository root, after `lake build`)

Renders the badge (`harness/badge/Common.lean.in`, `Verify.lean.in`) around `AccProbeSub`, builds it
with a separate Lake configuration into `.lake/rf/accprobe`, gets the service to sign the probe's
2^16 queries (100 bytes each), writes the signed-proof file, and runs `verify` pinned to one core
several times; also the same file with one answer changed (rejected at `SigOk`) and with the
signature's first chain value changed.
"""
import os
import shutil
import struct
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from rfh.service import Client, Service  # noqa: E402
from rfh.signed import Signed, from_wire  # noqa: E402

D = os.path.join(ROOT, ".lake", "rf", "accprobe")


def main():
    shutil.rmtree(D, ignore_errors=True)
    os.makedirs(os.path.join(D, "src"))
    shutil.copy(os.path.join(ROOT, "tests", "harness", "accprobe", "AccProbeSub.lean"), os.path.join(D, "src"))
    for name in ("Common", "Verify"):
        src = open(os.path.join(ROOT, "harness", "badge", f"{name}.lean.in")).read().replace("{{solution_module}}", "AccProbeSub")
        open(os.path.join(D, "src", f"RFBadge{name}.lean"), "w").write(src)
    cfg = open(os.path.join(ROOT, "scripts", "speed", "lakefile.toml")).read()
    cfg = cfg[:cfg.index("[[lean_exe]]")] + (
        '[[lean_lib]]\nname = "AccProbe"\nsrcDir = ".lake/rf/accprobe/src"\nroots = ["AccProbeSub", "RFBadgeCommon"]\n\n'
        '[[lean_exe]]\nname = "accprobe"\nsrcDir = ".lake/rf/accprobe/src"\nroot = "RFBadgeVerify"\n')
    open(os.path.join(D, "lakefile.toml"), "w").write(cfg)
    subprocess.run(["lake", "-f", os.path.join(D, "lakefile.toml"), "build", "accprobe"], cwd=ROOT, check=True, timeout=3600)
    exe = os.path.join(ROOT, ".lake", "build", "bin", "accprobe")
    qs = [struct.pack("<Q", k) + bytes(92) for k in range(1 << 16)]
    svc = Service(os.path.join(ROOT, "service", "target", "release", "rf-oracle"), os.path.join(D, "svc")).start()
    c = Client(svc.socket_path)
    s = from_wire(b"", qs, c.sign(qs))
    c.close()
    svc.stop()
    good = os.path.join(D, "good.bin")
    open(good, "wb").write(s.encode())
    bad_answer = Signed(s.pi, [(qs[0], bytes([s.trace[0][1][0] ^ 1]) + s.trace[0][1][1:])] + s.trace[1:], s.idx, s.ots, s.path)
    open(os.path.join(D, "bad-answer.bin"), "wb").write(bad_answer.encode())
    bad_sig = Signed(s.pi, s.trace, s.idx, [bytes([s.ots[0][0] ^ 1]) + s.ots[0][1:]] + s.ots[1:], s.path)
    open(os.path.join(D, "bad-sig.bin"), "wb").write(bad_sig.encode())
    stmt = bytes(32).hex()
    with open(os.path.join(D, "list.txt"), "w") as f:
        for name in ["good.bin"] * 5 + ["bad-answer.bin"] * 2 + ["bad-sig.bin"] * 2:
            f.write(f"{svc.vk.hex()} {stmt} {os.path.join(D, name)}\n")
    core = max(os.sched_getaffinity(0))
    out = subprocess.run(["taskset", "-c", str(core), exe, "--batch", os.path.join(D, "list.txt")], capture_output=True,
                         text=True, timeout=600).stdout.split("\n")
    size = os.path.getsize(good)
    print(f"file: {size} bytes, 2^16 queries of 100 bytes, pinned core {core}")
    for name, line in zip(["good"] * 5 + ["changed answer"] * 2 + ["changed signature"] * 2, out):
        r, ns = line.split()
        print(f"{name:18} {r:7} {int(ns) / 1e6:9.2f} ms")


if __name__ == "__main__":
    main()

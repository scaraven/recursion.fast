#!/usr/bin/env python3
"""The service's signatures against stage A's compiled Lean reference signer (V4-A4).

  python3 tests/service/test_lean_signer.py SIGNER [RF_ORACLE]

SIGNER is `lake -f scripts/speed/lakefile.toml build signer`'s `.lake/build/bin/signer`
(`Library/SignerFast.lean`: `chainStartF` = the contract-side `chainStart`, the tree = `node`, the
signature = `Signer.sign`, proved `SigOk`). The service runs with fixed test keys; its first two
signatures (the empty trace, then a three-query trace) must equal, byte for byte, the Lean signer's
signatures with the same seed and index on the same trace digests, and its `vk` the Lean `vk`.
"""
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
sys.path.insert(0, HERE)
import wots_ref as W  # noqa: E402
from rfh.service import Client  # noqa: E402
from rfh.signed import from_wire  # noqa: E402
import test_service  # noqa: E402
from test_service import SEED, start, stop  # noqa: E402

SIGNER = os.path.abspath(sys.argv[1])
# test_service reads its binary from argv[1] at import; here argv[1] is the signer
test_service.BIN = sys.argv[2] if len(sys.argv) > 2 else os.path.join(ROOT, "service", "target", "test-keys", "release",
                                                                       "rf-oracle")


def lean_sign(j, m):
    out = subprocess.run([SIGNER, SEED.hex(), str(j), m.hex()], capture_output=True, text=True, timeout=1800).stdout.split()
    return {"vk": bytes.fromhex(out[0]), "idx": int(out[1]), "ots": [bytes.fromhex(x) for x in out[2:135]],
            "path": [bytes.fromhex(x) for x in out[135:151]], "ok": out[151]}


def main():
    import tempfile
    tmp = tempfile.mkdtemp(prefix="rf-lean-signer-", dir=os.environ.get("RF_TEST_TMP"))
    p, info, sock = start(os.path.join(tmp, "svc"))
    c = Client(sock)
    traces = [[], [b"abc", bytes(64), b"x" * 1000]]
    sigs = [from_wire(b"", qs, c.sign(qs)) for qs in traces]
    c.close()
    stop(p)
    digests = [W.trace_digest(s.trace) for s in sigs]
    with ThreadPoolExecutor(2) as ex:
        lean = list(ex.map(lambda jm: lean_sign(*jm), [(s.idx, d) for s, d in zip(sigs, digests)]))
    fails = 0
    for k, (s, L) in enumerate(zip(sigs, lean)):
        same = (L["vk"].hex() == info["vk"] and L["idx"] == s.idx and L["ots"] == s.ots and L["path"] == s.path
                and L["ok"] == "true")
        print(("ok   " if same else "FAIL ") + f"signature {k} (index {s.idx}, {len(s.trace)} queries): service = Lean signer, "
              f"vk {info['vk'][:16]}…, Lean SigOkF {L['ok']}")
        fails += not same
    print(f"{fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())

"""The checks of a run (TRUSTED RUNTIME). The one predicate is the compiled `acc` (V4-7), run by the
badge executable `verify` that the harness renders and builds per entry; the runner only decides
which (vk, statement, file) triples to ask about and what the answers must be.

Badge executables (`harness/badge/`, built by `evaluate.py`; the command-line contract):

  verify --batch LIST        LIST: lines `VK_HEX STMT_HEX PATH`; prints one line per input,
                             `accept NS` or `reject NS`, NS the nanoseconds of parsing the file's
                             bytes and evaluating `acc` (a monotonic clock in the process, which runs
                             pinned to one core, so it bounds the check's CPU time); exit 0.
  chaincheck LEAVES ROOT_HEX the organiser's compiled-Lean interleaved chain checker: recompute the
                             leaf statements of LEAVES (`leaves.json`) and their tree root; prints
                             `ok NS` if it equals ROOT_HEX, else `mismatch NS`.
  liveness LOG VK_HEX STMT_HEX FILE
                             the extractor liveness check (`evaluate.py` renders it with the entry's
                             `ext`): runs `ext` on the root's tape with the service's query log LOG,
                             decodes the witness, checks it against `Rel (acc vk)` and recurses into
                             the children; prints `ok …` or `fail REASON`.

`verify` runs the entry's compiled verifier, so it runs in the sandbox, pinned to one core.
"""
import os
import random
import subprocess

from . import signed
from .prover import Drain
from .sandbox import Sandbox

LIB_ROOT = ("/usr", "/bin", "/lib", "/lib64", "/etc/ld.so.cache")


class BadgeError(Exception):
    pass


def pinned_core():
    """The core the checks run on: the highest-numbered CPU this process may use."""
    return max(os.sched_getaffinity(0))


class Badge:
    def __init__(self, badge_dir, mem, verify_s, scratch):
        self.dir, self.mem, self.verify_s, self.scratch = badge_dir, mem, verify_s, scratch
        self.core = pinned_core()
        self.n = 0

    def _run(self, args, binds, timeout):
        self.n += 1
        sb = Sandbox(["/badge/" + args[0]] + args[1:], [("ro", self.dir, "/badge")] + binds, self.mem,
                     env={"PATH": "/usr/bin:/bin"}, cwd="/", stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                     extra_ro_root=LIB_ROOT, cpus=self.core)
        out, err = Drain(sb.proc.stdout), Drain(sb.proc.stderr)
        try:
            code = sb.proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            code = "timeout"
        sb.kill()
        out.join(5)
        err.join(5)
        return code, out.kept.decode(errors="replace"), err.kept.decode(errors="replace")

    def verify(self, items, store):
        """`acc` on each (vk, stmt, relative path under `store`): a list of (accepted, ns)."""
        if not items:
            return []
        d = os.path.join(self.scratch, f"list{self.n}")
        os.makedirs(d)
        with open(os.path.join(d, "list.txt"), "w") as f:
            for vk, stmt, rel in items:
                f.write(f"{vk.hex()} {stmt.hex()} /store/{rel}\n")
        code, out, err = self._run(["verify", "--batch", "/list/list.txt"], [("ro", store, "/store"), ("ro", d, "/list")],
                                   self.verify_s * len(items) + 60)
        lines = out.split("\n")[:len(items)]
        res = []
        for line in lines:
            w = line.split()
            if len(w) != 2 or w[0] not in ("accept", "reject") or not w[1].isdigit():
                break
            res.append((w[0] == "accept", int(w[1])))
        if code != 0 or len(res) != len(items):
            raise BadgeError(f"verify: exit {code}, {len(res)} of {len(items)} answers; stderr: {err[-500:]}")
        slow = [ns for _, ns in res if ns > self.verify_s * 1e9]
        if slow:
            raise BadgeError(f"verify: a check took {max(slow) / 1e9:.1f} s, above verify_s")
        return res

    def chaincheck(self, leaves_json, root):
        d = os.path.dirname(leaves_json)
        code, out, err = self._run(["chaincheck", f"/in/{os.path.basename(leaves_json)}", root.hex()],
                                   [("ro", d, "/in")], 3600)
        w = out.split()
        if code != 0 or len(w) < 2 or w[0] != "ok":
            raise BadgeError(f"chaincheck: exit {code}, output {out[:200]!r} {err[-300:]!r}")
        return int(w[1])

    def liveness(self, log, vk, stmt, proof_file):
        code, out, err = self._run(["liveness", "/in/log.bin", vk.hex(), stmt.hex(), "/in/root.bin"],
                                   [("ro", log, "/in/log.bin"), ("ro", proof_file, "/in/root.bin")], 3600)
        return code == 0 and out.startswith("ok"), (out.strip() or err.strip())[-2000:]


# ---- canaries -------------------------------------------------------------------------------------

def canaries(data: bytes, stmt: bytes, sibling: bytes = None):
    """The mutations of one accepted signed proof that must all be rejected (v3 §8.3 step 7 for
    signed proofs): (name, statement, file bytes)."""
    s = signed.parse(data)
    out = [("file+1", stmt, data + b"\x00"), ("file-1", stmt, data[:-1])]
    if s is None:
        return out
    flip = bytearray(stmt)
    flip[0] ^= 1
    out.append(("stmt-bit", bytes(flip), data))
    if sibling is not None and sibling != stmt:
        out.append(("swapped-child", sibling, data))
    out.append(("pi+1", stmt, signed.Signed(s.pi + b"\x00", s.trace, s.idx, s.ots, s.path).encode()))
    if s.pi:
        out.append(("pi-1", stmt, signed.Signed(s.pi[:-1], s.trace, s.idx, s.ots, s.path).encode()))
    if s.trace:
        q, a = s.trace[0]
        tr = [(q, bytes([a[0] ^ 1]) + a[1:])] + s.trace[1:]
        out.append(("trace-answer", stmt, signed.Signed(s.pi, tr, s.idx, s.ots, s.path).encode()))
    out.append(("trace-extra", stmt, signed.Signed(s.pi, s.trace + [(b"", bytes(32))], s.idx, s.ots, s.path).encode()))
    ots = [bytes([s.ots[0][0] ^ 1]) + s.ots[0][1:]] + s.ots[1:]
    out.append(("sig-ots", stmt, signed.Signed(s.pi, s.trace, s.idx, ots, s.path).encode()))
    out.append(("sig-idx", stmt, signed.Signed(s.pi, s.trace, s.idx ^ 1, s.ots, s.path).encode()))
    return out


def dos_inputs(root_file: bytes, count: int, rnd: random.Random):
    """`count` random and mutated signed proofs for the DoS column: random bytes, random `π` with
    the root's trace and signature, and bit flips, truncations and extensions of the root's file."""
    s = signed.parse(root_file)
    out = []
    for k in range(count):
        kind = k % 4
        if kind == 0:
            out.append(rnd.randbytes(rnd.randint(0, 4096)))
        elif kind == 1 and s is not None:
            out.append(signed.Signed(rnd.randbytes(rnd.randint(0, 1 << 12)), s.trace, s.idx, s.ots, s.path).encode())
        elif kind == 2 and s is not None and s.pi:
            pi = bytearray(s.pi)
            for _ in range(rnd.randint(1, 8)):
                pi[rnd.randrange(len(pi))] ^= 1 << rnd.randrange(8)
            out.append(signed.Signed(bytes(pi), s.trace, s.idx, s.ots, s.path).encode())
        else:
            b = bytearray(root_file)
            for _ in range(rnd.randint(1, 8)):
                if b:
                    b[rnd.randrange(len(b))] ^= 1 << rnd.randrange(8)
            out.append(bytes(b[:rnd.randint(0, len(b))]) if rnd.random() < 0.3 else bytes(b))
    return out

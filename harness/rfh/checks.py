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

`verify` runs the entry's compiled verifier, so it runs in the sandbox, pinned to one core.

Only checks about the entry are made here (V4-A9): a proof the entry produced, accepted for its
statement, and the same proof rejected for another statement. Mutations that `acc` rejects before
the entry's `V` runs (the file parser, the trace digest, the signature) test organiser code and run
in the core CI (`tests/harness/canaries.py`).
"""
import os
import random
import subprocess

from . import signed
from .prover import Drain
from .sandbox import Sandbox

LIB_ROOT = ("/usr", "/bin", "/lib", "/lib64", "/etc/ld.so.cache")


class BadgeError(Exception):
    """A badge run that did not give every answer in time. `kind`: `timeout` (killed at its time
    limit), `crash` (another exit or missing answers) or `slow` (every answer given, one of them
    above `verify_s`); `partial`: the answers given."""

    def __init__(self, msg, kind, partial):
        super().__init__(msg)
        self.kind, self.partial = kind, partial


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

    def verify(self, items, store, timeout=None, warm=False):
        """`acc` on each (vk, stmt, relative path under `store`): a list of (accepted, ns). With
        `warm`, the first item is checked once more before the timed ones and that result dropped,
        so no timed item is the fresh process's first, coldest check (RF-m3). `timeout` bounds the
        whole batch (default `verify_s` per item and 60 s); a batch that times out, crashes or has a
        check above `verify_s` raises `BadgeError`."""
        if not items:
            return []
        lst = ([items[0]] if warm else []) + list(items)
        d = os.path.join(self.scratch, f"list{self.n}")
        os.makedirs(d)
        with open(os.path.join(d, "list.txt"), "w") as f:
            for vk, stmt, rel in lst:
                f.write(f"{vk.hex()} {stmt.hex()} /store/{rel}\n")
        code, out, err = self._run(["verify", "--batch", "/list/list.txt"], [("ro", store, "/store"), ("ro", d, "/list")],
                                   timeout if timeout is not None else self.verify_s * len(lst) + 60)
        res = []
        for line in out.split("\n")[:len(lst)]:
            w = line.split()
            if len(w) != 2 or w[0] not in ("accept", "reject") or not w[1].isdigit():
                break
            res.append((w[0] == "accept", int(w[1])))
        res = res[1:] if warm else res
        if code != 0 or len(res) != len(items):
            raise BadgeError(f"verify: exit {code}, {len(res)} of {len(items)} answers; stderr: {err[-500:]}",
                             "timeout" if code == "timeout" else "crash", res)
        slow = [ns for _, ns in res if ns > self.verify_s * 1e9]
        if slow:
            raise BadgeError(f"verify: a check took {max(slow) / 1e9:.1f} s, above verify_s", "slow", res)
        return res

    def chaincheck(self, leaves_json, root):
        d = os.path.dirname(leaves_json)
        code, out, err = self._run(["chaincheck", f"/in/{os.path.basename(leaves_json)}", root.hex()],
                                   [("ro", d, "/in")], 120)
        w = out.split()
        if code != 0 or len(w) < 2 or w[0] != "ok":
            raise RuntimeError(f"chaincheck: exit {code}, output {out[:200]!r} {err[-300:]!r}")
        return int(w[1])


# ---- canaries -------------------------------------------------------------------------------------

def canaries(stmt: bytes, sibling: bytes = None):
    """The statement canaries (C15, v3 §8.3 step 7) of a proof accepted for `stmt`: the statements it
    must be rejected for, as (name, statement): `stmt` with its first bit flipped, and the statement
    of its sibling in the tree it belongs to, if there is one."""
    flip = bytearray(stmt)
    flip[0] ^= 1
    out = [("stmt-bit", bytes(flip))]
    if sibling is not None and sibling != stmt:
        out.append(("swapped-child", sibling))
    return out


def dos_inputs(root_file: bytes, count: int, rnd: random.Random):
    """`count` random and mutated signed proofs for the DoS column, in turn: random bytes; random
    `π` with the root's trace and signature; the root's `π` with 1–8 bits flipped; the root's file
    with 1–8 bits flipped, cut to a random prefix in 30% of cases (no input extends the file)."""
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

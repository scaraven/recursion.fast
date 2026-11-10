"""The checks of a run (TRUSTED RUNTIME). The one predicate is the compiled `acc`, run by the
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

Only checks about the entry are made here: a proof the entry produced, accepted for its
statement, and the same proof rejected for another statement. Mutations that `acc` rejects before
the entry's `V` runs (the file parser, the trace digest, the signature) test organiser code and run
in the core CI (`tests/harness/canaries.py`).
"""
import os
import subprocess

from .prover import Drain
from .sandbox import Sandbox

LIB_ROOT = ("/usr", "/bin", "/lib", "/lib64", "/etc/ld.so.cache")


class BadgeError(Exception):
    """A badge run that did not give every answer in time. `kind`: `timeout` (killed at its time
    limit) or `crash` (another exit or missing answers)."""

    def __init__(self, msg, kind):
        super().__init__(msg)
        self.kind = kind


def pinned_core():
    """The core the checks run on: the highest-numbered CPU this process may use."""
    return max(os.sched_getaffinity(0))


class Badge:
    def __init__(self, badge_dir, mem, scratch):
        self.dir, self.mem, self.scratch = badge_dir, mem, scratch
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

    def verify(self, items, store, timeout, warm=False):
        """`acc` on each (vk, stmt, relative path under `store`): a list of (accepted, ns). With
        `warm`, the first item is checked once more before the timed ones and that result dropped,
        so no timed item is the fresh process's first, coldest check. `timeout` (seconds) bounds the
        whole batch; no single check has a bound of its own. A batch that times out or crashes
        raises `BadgeError`."""
        if not items:
            return []
        lst = ([items[0]] if warm else []) + list(items)
        d = os.path.join(self.scratch, f"list{self.n}")
        os.makedirs(d)
        with open(os.path.join(d, "list.txt"), "w") as f:
            for vk, stmt, rel in lst:
                f.write(f"{vk.hex()} {stmt.hex()} /store/{rel}\n")
        code, out, err = self._run(["verify", "--batch", "/list/list.txt"], [("ro", store, "/store"), ("ro", d, "/list")],
                                   timeout)
        res = []
        for line in out.split("\n")[:len(lst)]:
            w = line.split()
            if len(w) != 2 or w[0] not in ("accept", "reject") or not w[1].isdigit():
                break
            res.append((w[0] == "accept", int(w[1])))
        res = res[1:] if warm else res
        if code != 0 or len(res) != len(items):
            raise BadgeError(f"verify: exit {code}, {len(res)} of {len(items)} answers; stderr: {err[-500:]}",
                             "timeout" if code == "timeout" else "crash")
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

def canaries(stmt: bytes, others=()):
    """The statement canaries (AGENTS.md §6) of a proof accepted for `stmt`: the
    statements it must be rejected for, as (name, statement): `stmt` with its first bit flipped, and
    each (name, statement) of `others` that differs from `stmt` (in the stream: the statement of the
    leaf the next step adds, `next-leaf`, and the step's first child, `first-child`)."""
    flip = bytearray(stmt)
    flip[0] ^= 1
    out = [("stmt-bit", bytes(flip))]
    out += [(name, c) for name, c in others if c is not None and c != stmt]
    return out


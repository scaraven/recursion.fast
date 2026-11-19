"""The checks of a run (TRUSTED RUNTIME). The one predicate is the compiled `acc`, run by the
badge executable `verify` that the harness renders and builds per entry; the runner only decides
which (vk, statement, file) triples to ask about and what the answers must be.

Badge executables (`harness/badge/`, `RecursionFast/Badge.lean`, built by `evaluate.py`; the
command-line contract):

  verify --serve             requests on standard input, one line `VK_HEX STMT_HEX PATH` each; every
                             request is answered with one line, `accept NS` or `reject NS`, before
                             the next is read, NS the nanoseconds of parsing the file's bytes and
                             evaluating `acc` (a monotonic clock in the process); exit 0 at the end
                             of the input.
  verify --batch LIST        the same lines read from the file LIST (manual and CI use).

`verify` runs the entry's compiled verifier, so it runs in the sandbox, pinned to one core.

**Two clocks.** The runner times each request itself (`serve`): from just before it writes the
request line to the moment the answer line has arrived, on its own monotonic clock, outside the
badge's process. What is judged against `v_cap` is the larger of that external time and the badge's
own `NS`, so a badge whose in-process timer under-reports (a compiler or runtime surprise, or glue
that is not what it should be) gains nothing. The external time adds the request's round trip
through two pipes, reading the file and parsing the two hex strings: about 0.3 ms plus about
0.4 ms per MiB of file from the page cache (measured by `tests/harness/accprobe/run.py`, which
prints it: 0.3 ms for a 5 KB file, 3.6 to 5.7 ms for a 9.2 MB one), against `v_cap` = 128 ms; the
checked files are at most `file_cap`. The first request of a process also pays the process's
start-up (about 80 ms there), which is one reason every judged batch is warmed. The runner's own
thread is not pinned, so its scheduling can only add to the external time, never subtract (a check
near the cap is timed twice more and the least counts). An answer that arrives before its request
was written, or more than one answer to a request, is a crash.

Only checks about the entry are made here: a proof the entry produced, accepted for its
statement, and the same proof rejected for another statement. Mutations that `acc` rejects before
the entry's `V` runs (the file parser, the trace digest, the signature) test organiser code and run
in the core CI (`tests/harness/canaries.py`).
"""
import os
import select
import subprocess
import time

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

    def verify(self, items, store, timeout, warm=False):
        """`acc` on each (vk, stmt, relative path under `store`): a list of (accepted, ns), `ns` the
        larger of the runner's external time of the request and the badge's own (`serve`); the pairs
        (external, badge) of the last run are kept in `self.last`. With `warm`, the first item is
        checked once more before the timed ones and that result dropped, so no timed item is the
        fresh process's first, coldest check. `timeout` (seconds) bounds the whole batch; no single
        check has a bound of its own. A batch that times out or crashes raises `BadgeError`."""
        if not items:
            return []
        lst = ([items[0]] if warm else []) + list(items)
        self.n += 1
        sb = Sandbox(["/badge/verify", "--serve"], [("ro", self.dir, "/badge"), ("ro", store, "/store")], self.mem,
                     env={"PATH": "/usr/bin:/bin"}, cwd="/", stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                     stderr=subprocess.PIPE, extra_ro_root=LIB_ROOT, cpus=self.core)
        err = Drain(sb.proc.stderr)
        try:
            res, why = serve(sb.proc, [f"{vk.hex()} {stmt.hex()} /store/{rel}" for vk, stmt, rel in lst],
                             time.monotonic() + timeout)
        finally:
            sb.kill()
            err.join(5)
            for f in (sb.proc.stdin, sb.proc.stdout):
                try:
                    if f is not None:
                        f.close()
                except OSError:
                    pass
        self.last = [(ext, own) for _, _, ext, own in res][1 if warm else 0:]
        res = [(ok, ns) for ok, ns, _, _ in res][1 if warm else 0:]
        if why is not None or len(res) != len(items):
            raise BadgeError(f"verify: {why}, {len(res)} of {len(items)} answers; stderr: "
                             f"{err.kept.decode(errors='replace')[-500:]}", "timeout" if why == "timeout" else "crash")
        return res


def serve(proc, lines, deadline):
    """Run the requests `lines` through a `verify --serve` process `proc` (stdin and stdout pipes),
    one at a time, timing each from outside: ([(accepted, judged ns, external ns, badge ns)], None)
    if every request was answered and the process then exited 0, else (the answers so far, why):
    `timeout` at `deadline` (a `time.monotonic()` value), or what went wrong. The external time runs
    from just before the request is written to the arrival of its answer's newline; the judged time
    is the larger of it and the badge's own."""
    fin, fout, buf, out = proc.stdin.fileno(), proc.stdout.fileno(), b"", []
    os.set_blocking(fin, False)

    def read_some():
        left = deadline - time.monotonic()
        if left <= 0 or not select.select([fout], [], [], left)[0]:
            return None
        return os.read(fout, 1 << 16)
    for line in lines:
        if buf or select.select([fout], [], [], 0)[0]:
            if proc.poll() is not None:
                return out, f"the badge exited (code {proc.returncode}) before request {len(out) + 1}"
            return out, "output before a request was written (an answer ahead of its request)"
        t0 = time.monotonic_ns()
        req = (line + "\n").encode()
        while req:                                    # bounded by the deadline, never blocking
            left = deadline - time.monotonic()
            if left <= 0 or not select.select([], [fin], [], left)[1]:
                return out, "timeout"
            try:
                req = req[os.write(fin, req):]
            except BlockingIOError:
                continue
            except OSError as e:
                return out, f"the badge stopped reading its requests ({e})"
        while b"\n" not in buf:
            c = read_some()
            if c is None:
                return out, "timeout"
            if not c:
                return out, f"the badge exited (code {proc.poll()}) before answering"
            buf += c
        ext = time.monotonic_ns() - t0
        ans, buf = buf.split(b"\n", 1)
        if buf:
            return out, "more than one answer to a request"
        w = ans.decode(errors="replace").split()
        if len(w) != 2 or w[0] not in ("accept", "reject") or not w[1].isdigit():
            return out, f"a malformed answer {ans[:80]!r}"
        out.append((w[0] == "accept", max(ext, int(w[1])), ext, int(w[1])))
    try:
        proc.stdin.close()
    except OSError:
        pass
    while True:
        c = read_some()
        if c is None:
            return out, "timeout"
        if not c:
            break
        return out, "output after the last answer"
    try:
        code = proc.wait(timeout=max(0.0, deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        return out, "timeout"
    return out, None if code == 0 else f"exit {code}"


# ---- canaries -------------------------------------------------------------------------------------

def canaries(stmt: bytes, others=()):
    """The statement canaries (AGENTS.md §6) of a proof accepted for `stmt`: the
    statements it must be rejected for, as (name, statement): `stmt` with its first bit flipped, and
    each (name, statement) of `others` that differs from `stmt` (in the stream: the output's first
    child, `first-child`: `c_{i-1}` for a step `i ≥ 2`; step 1's output, a leaf, has none)."""
    flip = bytearray(stmt)
    flip[0] ^= 1
    out = [("stmt-bit", bytes(flip))]
    out += [(name, c) for name, c in others if c is not None and c != stmt]
    return out

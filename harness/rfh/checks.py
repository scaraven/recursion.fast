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
through two pipes, reading the file (a copy on the runner's tmpfs, `Badge.stage`) and parsing the
two hex strings: about 0.3 ms plus about 0.4 ms per MiB of file (measured by
`tests/harness/accprobe/run.py`, which prints it: 0.3 ms for a 5 KB file, 3.6 to 5.7 ms for a
9.2 MB one, from the page cache before the copies), against `v_cap` = 64 ms; the
checked files are at most `file_cap`. The first request of a process also pays the process's
start-up (about 80 ms there).

**The warm-up.** Every run whose times are judged is a fresh process that first checks the
organiser's warm-up input (`warm_file`: a fixed, well-formed signed proof under a fresh random key
and statement, rejected at the signature) and drops that answer; then the items, all distinct. Each
checked proof is judged in three such runs of its own (`Bench.judged`: three fresh, warmed
processes, each checking that one proof once and nothing else), and the median of its three times
is its `V`. So no judged check runs in a process that has seen its input or any other output of the
stream: an entry's verifier can keep state across the checks of one process (a top-level constant
is one object for the life of the process, and a `Thunk` in it is forced once); a warm-up on the
judged input itself would have paid a memoised verifier's work untimed (review R7,
`tests/harness/accprobe/MemoSub.lean`), and since output `i + 1` contains `π_i`, a run that checked
outputs `i` and `i + 1` together would have let a verifier that memoises its children's acceptance
answer the check of `π_i` inside output `i + 1` from the memo (review LR2,
`tests/harness/accprobe/MemoChildSub.lean`). The warm-up is recognisable, which costs nothing: it only
pays the start-up and the page-in. The start-up, from the sandbox's release to the warm-up's
answer, is capped by the season's `badge_start_s` (2 s, against about 0.08 s measured), since the
entry's top-level constants are evaluated then, untimed; past it the run fails like a timed-out
one. Work done inside a judged check is that check's. The runner's own
thread is not pinned, so its scheduling can only add to the external time, never subtract (one slow
run of three does not decide: the median counts). An answer that arrives before its request
was written, or more than one answer to a request, is a crash.

Only checks about the entry are made here: a proof the entry produced, accepted for its
statement, and the same proof rejected for another statement. Mutations that `acc` rejects before
the entry's `V` runs (the file parser, the trace digest, the signature) test organiser code and run
in the core CI (`tests/harness/canaries.py`).
"""
import os
import select
import stat
import subprocess
import time

from .prover import Drain
from .sandbox import Sandbox, copy_file, copy_tree, remove_tree, runner_path
from .signed import Signed

LD_CACHE = "/etc/ld.so.cache"
HOST_ROOT = ("/usr", "/bin", "/lib", "/lib64", LD_CACHE)     # `host_root` (a test's stand-in badge) only


def copy_bytes(path, data):
    """Write `data` to the new read-only file `path`; its length."""
    with open(path, "xb") as f:
        f.write(data)
    os.chmod(path, 0o444)
    return len(data)


def needed(path):
    """The host files a dynamically linked executable `path` loads (its interpreter and libraries, as
    the system's `ldd` lists them: the dynamic loader in its list mode, which runs none of the
    executable's code), and the interpreter of a `#!` script; [] for a static executable."""
    with open(path, "rb") as f:
        head = f.read(256)
    if head.startswith(b"#!"):
        w = head[2:].split(b"\n")[0].split()
        return [os.fsdecode(w[0])] if w else []
    p = subprocess.run(["ldd", path], capture_output=True, text=True, timeout=60)
    out = []
    for line in p.stdout.splitlines():
        w = line.split()
        if "=>" in w and len(w) > w.index("=>") + 1 and w[w.index("=>") + 1].startswith("/"):
            out.append(w[w.index("=>") + 1])
        elif w and w[0].startswith("/"):
            out.append(w[0])
    return out


def mirror(root, path, depth=0):
    """Reproduce the host path `path` under `root`: its directories (mode 0700), every symbolic link
    on the way (as the same link, then followed), and the file at its end (`copy_file`)."""
    if depth > 40:
        raise OSError(f"too many links resolving {path}")
    cur, parts = "/", [x for x in path.split("/") if x]
    for i, name in enumerate(parts):
        host = os.path.join(cur, name)
        here = root + host
        st = os.lstat(host)
        if stat.S_ISLNK(st.st_mode):
            target = os.readlink(host)
            if not os.path.lexists(here):
                os.symlink(target, here)
            nxt = os.path.normpath(os.path.join(cur, target))
            return mirror(root, os.path.join(nxt, *parts[i + 1:]), depth + 1)
        if stat.S_ISDIR(st.st_mode):
            if not os.path.isdir(here):
                os.mkdir(here, 0o700)
            cur = host
        elif i == len(parts) - 1 and stat.S_ISREG(st.st_mode):
            if not os.path.exists(here):
                copy_file(host, here)
        else:
            raise OSError(f"{host} is neither a directory nor a regular file")


def lib_files(executable, tools=(), skip=None):
    """The host files the dynamically linked `executable` and the host executables `tools` load:
    their interpreters and libraries (`needed`), recursively, and the loader's cache, as host paths
    (sorted); paths under the directory `skip` (the badge directory, which /badge copies whole) left
    out."""
    todo, seen = needed(executable) + list(tools), set()
    while todo:
        p = todo.pop()
        if p in seen:
            continue
        seen.add(p)
        todo += needed(p)
    if os.path.isfile(LD_CACHE):
        seen.add(LD_CACHE)
    base = os.path.realpath(skip) + "/" if skip else None
    return sorted(p for p in seen if not (base and os.path.realpath(p).startswith(base)))


def lib_view(root, files):
    """A tree under `root` (on the runner's tmpfs) holding the host files `files` (`lib_files`) at
    their host paths (`mirror`). Returns its binds for the sandbox's root: each top-level directory
    read-only, each top-level link as a link."""
    for p in files:
        mirror(root, p)
    out = []
    for n in sorted(os.listdir(root)):
        full = os.path.join(root, n)
        out.append(("symlink", os.readlink(full), "/" + n) if os.path.islink(full) else ("ro", full, "/" + n))
    return out


class BadgeError(Exception):
    """A badge run that did not give every answer in time. `kind`: `timeout` (killed at its time
    limit) or `crash` (another exit or missing answers)."""

    def __init__(self, msg, kind):
        super().__init__(msg)
        self.kind = kind


def pinned_core():
    """The core the checks run on: the highest-numbered CPU this process may use."""
    return max(os.sched_getaffinity(0))


WARM_PI = b"recursion.fast: the badge's warm-up input; not a proof"


def warm_file():
    """The organiser's warm-up file: a well-formed signed proof (`WARM_PI`, no trace, an all-zero
    signature) that `acc` rejects at the signature, under any key, before the entry's `V` runs."""
    return Signed(WARM_PI).encode()


class Badge:
    """The badge executable `verify` in the sandbox. `start_s` (the season's `badge_start_s`): the
    cap on a warmed run's start-up, from the moment the process may run to the warm-up's answer.
    Everything a badge run sees is on the runner's tmpfs (`sandbox.runner_dir`), never the work disk
    or the host's /usr (review LR4 H1: a lookup there leaves a negative dentry that a later badge
    run, one of a proof's three judged runs, could time), and **fresh for every run**, removed after
    it (`view`): a copy of the badge directory at /badge; at their host paths, copies of the files
    `verify` loads (`lib_files`, listed once, at the first run) and of /etc/ld.so.cache; the warm-up
    file at /warm; a directory holding copies of that run's checked files alone at /store (`stage`).
    A tmpfs file keeps state a process holding it read-only can set (its shared memory policy,
    `mbind` on a read-only `MAP_SHARED` mapping: review LR5 H1), so no badge run sees a file another
    badge run, or a request, saw: one of a proof's three judged runs cannot leave a memo for the
    next. `tools`: host executables a stand-in badge (a script, in the tests) runs, put in the same
    tree with what they load. `host_root` (tests only: the Python stand-in badge of `smoke.py --mock`
    needs the host's Python library; `run-benchmark.py` refuses it outside the tests, and the
    aggregation refuses a result that used it) binds the host's /usr, /bin, /lib and /lib64 in place
    of that tree, as before review LR4. `copies` records (bytes, seconds) of each run's copies."""

    def __init__(self, badge_dir, mem, scratch, start_s=None, tools=(), host_root=False):
        self.dir, self.mem, self.scratch, self.start_s, self.tools = badge_dir, mem, scratch, start_s, tuple(tools)
        self.host_root = host_root
        self.core = pinned_core()
        self.n = 0
        self.last = []
        self.copies = []
        self.run_s = 0.0             # the last run's time from its release to its last answer
        self._libs = None

    def stage(self, items, store, d=None):
        """A fresh directory on the runner's tmpfs (`d`, made here, or a new one) with a copy of each
        item's file (its path relative to `store` kept): the /store of one badge run."""
        if d is None:
            d = runner_path("store")
        else:
            os.mkdir(d, 0o700)
        for rel in sorted({rel for _, _, rel in items}):
            dst = os.path.join(d, rel)
            os.makedirs(os.path.dirname(dst), mode=0o700, exist_ok=True)
            if not os.path.exists(dst) and os.path.lexists(os.path.join(store, rel)):   # a missing one stays missing
                copy_file(os.path.join(store, rel), dst, 0o444)
        return d

    def view(self, items, store, warm):
        """The files of one badge run, made fresh in a new directory on the runner's tmpfs: (that
        directory, its binds). The list of the files `verify` loads is made at the first run."""
        import time as _t
        t0 = _t.monotonic()
        root = runner_path("badge")
        try:
            bdir = os.path.join(root, "badge")
            n = copy_tree(self.dir, bdir)            # directories, regular files (read-only) and links
            if self.host_root:
                binds = [("symlink", os.readlink(p), p) if os.path.islink(p) else ("ro", p, p)
                         for p in HOST_ROOT if os.path.lexists(p)]
            else:
                if self._libs is None:
                    self._libs = lib_files(os.path.join(self.dir, "verify"), self.tools, skip=self.dir)
                libs = os.path.join(root, "root")
                os.mkdir(libs, 0o700)
                binds = lib_view(libs, self._libs)
                n += sum(os.lstat(os.path.join(r, f)).st_size for r, _, fs in os.walk(libs) for f in fs)
            binds += [("ro", bdir, "/badge"), ("ro", self.stage(items, store, os.path.join(root, "store")), "/store")]
            if warm:
                wd = os.path.join(root, "warm")
                os.mkdir(wd, 0o700)
                n += copy_bytes(os.path.join(wd, "warm.bin"), warm_file())
                binds.append(("ro", wd, "/warm"))
        except BaseException:
            remove_tree(root)
            raise
        self.copies.append((n, _t.monotonic() - t0))
        return root, binds

    def start(self, binds):
        """A fresh `verify --serve` process with the run's binds (`view`): (process, stop(), the
        monotonic time it was let run, the store's path and the warm-up directory's path as the
        process sees them). The sandbox is set up held, and the clock starts when it is released, so
        the start-up cap counts the badge's own start-up, not the sandbox's."""
        sb = Sandbox(["/badge/verify", "--serve"], binds, self.mem, env={"PATH": "/usr/bin:/bin"}, cwd="/",
                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                     cpus=self.core, hold=True)
        sb.wait_ready()
        t0 = time.monotonic()
        sb.release()
        return sb.proc, sb.kill, t0, "/store", "/warm"

    def verify(self, items, store, timeout, warm=False, clock=None):
        """`acc` on each (vk, stmt, relative path under `store`), in one fresh process: a list of
        (accepted, ns), `ns` the larger of the runner's external time of the request and the
        badge's own (`serve`); the pairs (external, badge) of the run are kept in `self.last`.

        With `warm` (every run whose times are judged), the process first checks the organiser's
        warm-up input (`warm_file`, under a fresh random key and statement), so that no timed item
        is the process's first, coldest check, and no timed item is one the process has seen: the
        items of a run are distinct, and each of a proof's three judged runs is a fresh process that
        checks that proof alone (`Bench.judged`). The warm-up is recognisable (an entry may detect it); it only pays the start-up and the page-in. The
        start-up, from release to the warm-up's answer, is capped by `start_s`: work an entry's
        top-level constants do when the process starts is untimed, and this bounds it. `timeout`
        (seconds) bounds the whole run; no single check has a bound of its own. A run that times
        out, starts up too slowly or crashes raises `BadgeError`. `clock(running, spent_s=0.0)`, if
        given, is told when the process is released (`clock(True)`) and when its time ends
        (`clock(False, run_s)`): the copies before and the removal after are the runner's
        (`Bench.verify`, the stream's checkpoint)."""
        if not items:
            return []
        self.n += 1
        root, binds = self.view(items, store, warm)
        try:
            return self._verify(items, binds, timeout, warm, clock)
        finally:
            remove_tree(root)

    def _verify(self, items, binds, timeout, warm, clock=None):
        proc, stop, t0, sp, wp = self.start(binds)
        if clock is not None:
            clock(True)
        lines = [f"{os.urandom(32).hex()} {os.urandom(32).hex()} {wp}/warm.bin"] if warm else []
        lines += [f"{vk.hex()} {stmt.hex()} {sp}/{rel}" for vk, stmt, rel in items]
        first = t0 + self.start_s if warm and self.start_s else None
        err = Drain(proc.stderr)
        try:
            res, why = serve(proc, lines, time.monotonic() + timeout, first)
        finally:
            self.run_s = time.monotonic() - t0       # the badge process's own time: the entry's (`Bench.charge`)
            if clock is not None:
                clock(False, self.run_s)
            stop()
            err.join(5)
            for f in (proc.stdin, proc.stdout):
                try:
                    if f is not None:
                        f.close()
                except OSError:
                    pass
        k = 1 if warm else 0
        self.last = [(ext, own) for _, _, ext, own in res][k:]
        res = [(ok, ns) for ok, ns, _, _ in res][k:]
        if why == "start-up":
            raise BadgeError(f"verify: its start-up and the warm-up check took more than badge_start_s = "
                             f"{self.start_s} s (work at start-up is untimed, so it is capped); stderr: "
                             f"{err.kept.decode(errors='replace')[-300:]}", "timeout")
        if why is not None or len(res) != len(items):
            raise BadgeError(f"verify: {why}, {len(res)} of {len(items)} answers; stderr: "
                             f"{err.kept.decode(errors='replace')[-500:]}", "timeout" if why == "timeout" else "crash")
        return res


def serve(proc, lines, deadline, first_deadline=None):
    """Run the requests `lines` through a `verify --serve` process `proc` (stdin and stdout pipes),
    one at a time, timing each from outside: ([(accepted, judged ns, external ns, badge ns)], None)
    if every request was answered and the process then exited 0, else (the answers so far, why):
    `timeout` at `deadline` (a `time.monotonic()` value), `start-up` if the first answer has not
    arrived by `first_deadline`, or what went wrong. The external time runs from just before the
    request is written to the arrival of its answer's newline; the judged time is the larger of it
    and the badge's own."""
    fin, fout, buf, out = proc.stdin.fileno(), proc.stdout.fileno(), b"", []
    os.set_blocking(fin, False)
    dl = [deadline]

    def late():
        return "start-up" if not out and first_deadline is not None and first_deadline < deadline else "timeout"

    def read_some():
        left = dl[0] - time.monotonic()
        if left <= 0 or not select.select([fout], [], [], left)[0]:
            return None
        return os.read(fout, 1 << 16)
    for line in lines:
        dl[0] = min(deadline, first_deadline) if not out and first_deadline is not None else deadline
        if buf or select.select([fout], [], [], 0)[0]:
            if proc.poll() is not None:
                return out, f"the badge exited (code {proc.returncode}) before request {len(out) + 1}"
            return out, "output before a request was written (an answer ahead of its request)"
        t0 = time.monotonic_ns()
        req = (line + "\n").encode()
        while req:                                    # bounded by the deadline, never blocking
            left = dl[0] - time.monotonic()
            if left <= 0 or not select.select([], [fin], [], left)[1]:
                return out, late()
            try:
                req = req[os.write(fin, req):]
            except BlockingIOError:
                continue
            except OSError as e:
                return out, f"the badge stopped reading its requests ({e})"
        while b"\n" not in buf:
            c = read_some()
            if c is None:
                return out, late()
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
    dl[0] = deadline
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

"""The benchmark of one entry (TRUSTED RUNTIME): the IVC stream, its checks and calibration, the
timed passes and the score (the rules are in `AGENTS.md` §6, §7). One stream per evaluation, with
its own service lifetime: first the **service run** (the stream against the service, untimed, every
output checked before any secret is revealed), then `timed_runs` **timed passes** against the
service's replay mode, each output byte-identical to the service run's. Every request is a fresh
sandboxed process; the service run and each timed pass bind their own copy of the binary and the
setup (`Bench.fresh_copy`), every badge run its own copies of what it sees (`checks.Badge`); every
check and every calibration sample runs while no entry process is alive.
Every step the entry controls is capped by the season file, inside its job's time limit: a request
over its cap, and a benchmark that reaches `stream_s` of the entry's time (a slow or hung check
included; the runner's own work is off that clock, `Bench.deadline`), fails with the reason.
"""
import hashlib
import json
import math
import os
import platform
import secrets
import shutil
import statistics
import subprocess
import time
import tomllib
from dataclasses import dataclass

from . import digest, draws, signed
from .checks import Badge, BadgeError, canaries
from .prover import fresh_dir, remove_tree, request
from .sandbox import memcap, memcap_method, runner_path
from .service import Service, ServiceError


class Fail(Exception):
    """The entry fails the benchmark (the message says why). `kind`: the badge's failure kind when a
    check failed (`timeout`, `crash`), else None. `stage`: where it was rejected, the result's
    `reject_stage` (one of `REJECT_STAGES`; AGENTS.md §7): `prover` (the prover's build or setup, or
    anything else before the stream), `request` (a service-run request failed: its exit, a timeout, a
    cap of the request or of its output), `check` (an output's check by the badge failed or broke a
    cap, or a statement canary was accepted), `timed-pass` (a byte or replay mismatch, or a timed
    request failed), `stream-cap` (`stream_s` reached). The bot re-runs a REJECT without the record
    build cache only for `certificate` and `check`, the stages a sabotaged cache can cause. None is
    filled in by the stream from the phase it was in (`Bench.phase`)."""

    def __init__(self, msg, kind=None, stage=None):
        super().__init__(msg)
        self.kind, self.stage = kind, stage


REJECT_STAGES = ("certificate", "prover", "request", "check", "timed-pass", "stream-cap")


def printable(text, limit=1200):
    """Untrusted text (a prover's output) as printable ASCII for a result and a public comment:
    every other character becomes `?`, backticks become `'`, and it is put in a code
    span."""
    t = "".join(c if 32 <= ord(c) < 127 else "?" for c in text.replace("`", "'"))
    return "`" + t[-limit:] + "`"


@dataclass
class Params:
    name: str
    size_ref: int
    M: int
    n: int
    ready_s: float
    step_s: float
    stream_s: float
    check_every: int
    timed_runs: int
    calib_every: int
    calib_idle_s: float
    calib_rounds: int
    calib_ref_ns: float
    calib_drift: float
    calib_runs: int
    calib_ref_provisional: bool
    service_calib_s: float
    pi_cap: int
    final_pi_cap: int
    v_cap_ms: float
    badge_start_s: float
    file_cap: int
    setup_s: float
    setup_cap: int
    work_cap: int
    build_s: float
    mem_prover: str
    mem_service: str
    mem_badge: str
    fingerprint: str

    @staticmethod
    def load(path, check=True):
        """The season file at `path`; with `check`, its `[stream]` shape validated (a ValueError
        naming the defect). `check=False` is for the aggregation alone, which names a malformed
        shape as the organiser's ERROR instead of failing."""
        t = tomllib.load(open(path, "rb"))
        g = lambda sec, k: t[sec][k]  # noqa: E731 (a KeyError names the missing parameter)
        s = t["stream"]
        p = Params(
            name=t["name"], size_ref=g("score", "size_ref"),
            M=s.get("M"), n=s.get("n"), ready_s=g("stream", "ready_s"),
            step_s=g("stream", "step_s"), stream_s=g("stream", "stream_s"), check_every=g("stream", "check_every"),
            timed_runs=g("stream", "timed_runs"),
            calib_every=g("calibration", "every"), calib_idle_s=float(g("calibration", "idle_s")),
            calib_rounds=g("calibration", "rounds"), calib_ref_ns=float(g("calibration", "ref_ns")),
            calib_drift=float(g("calibration", "c_P_drift")), calib_runs=g("calibration", "runs_per_sample"),
            calib_ref_provisional=bool(g("calibration", "ref_provisional")), service_calib_s=g("calibration", "service_s"),
            pi_cap=g("caps", "pi_cap"), final_pi_cap=g("caps", "final_pi_cap"), v_cap_ms=float(g("caps", "v_cap_ms")),
            badge_start_s=float(g("caps", "badge_start_s")),
            file_cap=g("caps", "file_cap"), setup_s=g("caps", "setup_s"),
            setup_cap=g("caps", "setup_cap"), work_cap=g("caps", "work_cap"), build_s=g("caps", "build_s"),
            mem_prover=g("memory", "prover"), mem_service=g("memory", "service"), mem_badge=g("memory", "badge"),
            fingerprint=g("machine", "fingerprint"))
        if check:
            p.check_shape()
        return p

    def shape(self):
        """The stream's shape, as the result records it (`stream.shape`) and the aggregation compares."""
        return {"M": self.M, "n": self.n}

    def check_shape(self):
        """The season's stream shape (`[stream] M`, `n`): positive integers, `1 ≤ n ≤ LEAF_CAP =
        leafCap = 2^20` blocks (the contract's bound on a leaf), and `timed_runs` an odd positive
        integer (`P_total` is the median of the pass totals, `score`); else a ValueError naming the
        defect, its message naming `[stream]` (so the aggregation names it `lengths`)."""
        bad = [k for k in ("M", "n") if type(getattr(self, k)) is not int or getattr(self, k) < 1]
        if bad:
            raise ValueError(f"[stream] {', '.join(bad)} not a positive integer")
        if self.n > LEAF_CAP:
            raise ValueError(f"[stream] n = {self.n} above the contract's leafCap = 2^20 blocks")
        if type(self.timed_runs) is not int or self.timed_runs < 1 or self.timed_runs % 2 == 0:
            raise ValueError(f"[stream] timed_runs = {self.timed_runs!r}, not an odd positive integer (P_total is "
                             "the median of the pass totals)")


LEAF_CAP = digest.LEAF_CAP       # the contract's leafCap = 2^20 blocks (`Relation.lean`)


def leaf_json(n):
    """`leaf.json`: the leaf's number of blocks (its data is `leaf.bin`, `32 · n` bytes)."""
    return json.dumps({"n": n}).encode()


FP_HASHED = ("cpu_model", "vm_shape", "frequency_policy", "image_id")    # what comparability is about
FP_RECORDED = ("host_kernel",)       # published in the result, never hashed (it changes on updates)
# the file's other fields (`microcode`) are neither hashed nor recorded in the result


def fingerprint(path=None):
    """The machine fingerprint (AGENTS.md §6) from the file named by `RF_MACHINE_FINGERPRINT`, which
    the evaluation VM provides: a JSON object with the required fields `cpu_model`,
    `frequency_policy`, `image_id` (non-empty strings) and `vm_shape` (`{"vcpus": positive int,
    "memory": non-empty}`). `hash` is the sha256 of the canonical JSON (`json.dumps(obj,
    sort_keys=True, separators=(",", ":"))`, UTF-8) of exactly those four fields; `host_kernel` is
    recorded, not hashed; the file's other fields (`microcode` among them) are ignored. `status`: `ok`, `missing` (no variable or no file) or
    `unreadable` (not JSON, not an object with the required fields), with `reason`. The CPU model
    itself is never recorded."""
    path = path or os.environ.get("RF_MACHINE_FINGERPRINT")
    out = {"status": "missing", "hash": None, "reason": None}
    if not path:
        out["reason"] = "RF_MACHINE_FINGERPRINT is not set"
        return out
    if not os.path.isfile(path):
        out["reason"] = "the fingerprint file named by RF_MACHINE_FINGERPRINT does not exist"
        return out
    out["status"] = "unreadable"
    try:
        obj = json.load(open(path))
    except (OSError, ValueError) as e:
        out["reason"] = f"the fingerprint file is not JSON ({e.__class__.__name__})"
        return out
    if not isinstance(obj, dict):
        out["reason"] = "the fingerprint file is not a JSON object"
        return out
    nonempty = lambda v: isinstance(v, str) and v.strip() != ""  # noqa: E731
    shape = obj.get("vm_shape")
    bad = [k for k in ("cpu_model", "frequency_policy", "image_id") if not nonempty(obj.get(k))]
    if not (isinstance(shape, dict) and type(shape.get("vcpus")) is int and shape["vcpus"] > 0
            and (nonempty(shape.get("memory")) or (type(shape.get("memory")) is int and shape["memory"] > 0))):
        bad.append("vm_shape")
    if bad:
        out["reason"] = f"the fingerprint file lacks the required field(s) {sorted(bad)}"
        return out
    canon = json.dumps({k: obj[k] for k in FP_HASHED}, sort_keys=True, separators=(",", ":"))
    out.update(status="ok", hash=hashlib.sha256(canon.encode()).hexdigest())
    for k in FP_RECORDED:
        out[k] = str(obj[k])[:200] if obj.get(k) is not None else None
    return out


def machine():
    """What the result records about the machine (no CPU model, no CPU flags): the fingerprint's
    hash and status, the unhashed `host_kernel`, the job's CPUs and memory, and the
    runner as the workflow names it (AGENTS.md §8: `RUNNER_NAME`, `RF_RUNNER_ENVIRONMENT` =
    `runner.environment`, `RF_RUNNER_LABELS` = the job's `runs-on` labels, comma-separated)."""
    mem = next((int(l.split()[1]) for l in open("/proc/meminfo") if l.startswith("MemTotal")), None)
    labels = [x for x in os.environ.get("RF_RUNNER_LABELS", "").split(",") if x]
    fp = fingerprint()
    return {"fingerprint": fp["hash"], "fingerprint_status": fp["status"], "fingerprint_reason": fp["reason"],
            "host_kernel": fp.get("host_kernel"),
            "nproc": os.cpu_count(), "mem_total_kb": mem, "kernel": platform.release(),
            "memcap": memcap_method(), "runner_name": os.environ.get("RUNNER_NAME"),
            "runner_environment": os.environ.get("RF_RUNNER_ENVIRONMENT"), "runner_labels": labels}


def fingerprint_problem(fp_status, fp_hash, expected):
    """Why the machine is not the season's (an organiser ERROR, AGENTS.md §6), or None: the season's
    `"any"` (the smoke) accepts every machine."""
    if expected == "any":
        return None
    if fp_status == "missing":
        return "missing"
    if fp_status != "ok" or not fp_hash:
        return "unreadable"
    return None if fp_hash == expected else "mismatched"


def build_tool(name, out_dir):
    """Build the runner's tool `harness/tools/NAME.c` with the runner's `gcc`, before any entry code
    runs; (path, info)."""
    src = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools", f"{name}.c")
    os.makedirs(out_dir, exist_ok=True)
    out = os.path.join(out_dir, name)
    p = subprocess.run(["gcc", "-O2", "-pthread", "-o", out, src], capture_output=True, text=True, timeout=120)
    if p.returncode != 0:
        raise RuntimeError(f"{name} build failed: {p.stderr[-500:]}")
    return out, {"source_sha256": hashlib.sha256(open(src, "rb").read()).hexdigest(),
                 "binary_sha256": hashlib.sha256(open(out, "rb").read()).hexdigest()}


def build_calib(out_dir):
    """The calibration workload (`harness/tools/calib.c`); (path, info)."""
    return build_tool("calib", out_dir)


def build_scrub(out_dir):
    """The per-CPU inode counters' scrub (`harness/tools/scrub.c`, `Bench.scrub`); (path, info)."""
    return build_tool("scrub", out_dir)


class Bench:
    def __init__(self, p: Params, run, badge_dir, service_bin, bench_bin, work, calib_bin=None, log=print,
                 scrub_bin=None):
        self.p, self.run, self.service_bin, self.bench_bin = p, run, service_bin, bench_bin
        self.work, self.log, self.calib_bin, self.scrub_bin = work, log, calib_bin, scrub_bin
        self.phase = "prover"                # the reject stage of a Fail without one (`Fail.stage`)
        self.store = os.path.join(work, "store")
        os.makedirs(self.store, exist_ok=True)
        # the leaf data: runner-only, beside the store and never under it (the badge binds the store at
        # /store); nothing is bound into any sandbox from it, a request gets a staged copy at `go`
        self.leafdata = os.path.join(work, "leafdata")
        self.badge = Badge(badge_dir, p.mem_badge, os.path.join(work, "badge-scratch"), p.badge_start_s,
                           host_root=os.environ.get("RF_TEST_BADGE_HOST_ROOT") == "1")     # tests only
        os.makedirs(self.badge.scratch, exist_ok=True)
        self.deadline = None                 # the running cap (`stream_s`), on the entry's clock (`deadline`)
        self.samples = []                    # the interleaved calibration samples

    # -- the stream's clock: the entry's time alone (review R3 L1) ---------------------------------
    @property
    def deadline(self):
        """(monotonic time, reason) of the running cap, or None: the time at which the cap is
        reached if only the entry runs from now on. The clock counts **the entry's time alone**:
        its requests (start-up to `ready`, and the timed part, `Bench.one`) and its badge runs (from
        the process's release to its last answer, `verify`), charged as each ends (`charge`).
        Everything the runner does in between (the copies, the scrubs, the sandboxes' views and
        set-up, the staging, the outputs' reads and walks, the calibration samples, the service's
        control lines, the untimed delays) is off the clock: recorded as the runner's overhead
        (`stream.clock`) and bounded by the benchmark job's `PART_S` (`harness/evaluate.py`), so an
        entry is never rejected for the runner's own time. Setting it to (t, reason) starts a cap
        that is reached when the entry has used `t − now` more seconds; None stops it."""
        cap = getattr(self, "_cap", None)
        return None if cap is None else (time.monotonic() + cap - self.entry_s, self._cap_why)

    @deadline.setter
    def deadline(self, v):
        if v is None:
            self._cap = None
        else:
            self._cap, self._cap_why, self.entry_s = v[0] - time.monotonic(), v[1], 0.0

    def charge(self, seconds):
        """Count `seconds` of the entry's time on the stream's clock."""
        if getattr(self, "_cap", None) is not None and seconds:
            self.entry_s += seconds

    # -- the service ---------------------------------------------------------------------------
    def service(self, name):
        # the socket directory on the runner's tmpfs: each request's own socket directory is made
        # beside it (a hard link cannot cross filesystems), and no request sees the work disk
        # a connection idle, or a response unread, for `step_s` is closed (`--io-timeout`): no request
        # lasts longer, and `drop` closes the rest after every request (review R5 HIGH 1)
        svc = Service(self.service_bin, os.path.join(runner_path("svc"), name),
                      wrap=memcap(self.p.mem_service, f"rf-svc-{name}-{os.getpid()}"),
                      stderr_path=os.path.join(self.work, "svc", f"{name}.stderr"),
                      io_timeout=max(1, math.ceil(self.p.step_s)))
        os.makedirs(os.path.join(self.work, "svc"), exist_ok=True)
        return svc.start()

    @staticmethod
    def diag(svc, output):
        """What a failed run said: the prover's output tail and the service's refusals."""
        out = f"; prover output (tail): {printable(output.strip())}" if output.strip() else ""
        ref = svc.refusals(5)
        return out + (f"; service refusals: {printable('; '.join(ref), 600)}" if ref else "")

    def stop(self, svc, rec):
        rec["service_refusals"] = svc.refusals()
        rec["service_mismatches"] = svc.mismatches()[:8]
        try:
            rec["service_stats"] = svc.stop()
        except ServiceError as e:
            raise Fail(f"the service failed during the run ({e}); the run is aborted")

    def alive(self, svc):
        if svc.proc is None or svc.proc.poll() is not None:
            raise Fail("the service died during the run (a restart is a new key; the run is aborted)")

    # -- storage and checks ----------------------------------------------------------------------
    def keep(self, rel, data):
        path = os.path.join(self.store, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "wb") as f:
            f.write(data)
        return rel

    def left(self):
        """Seconds of the entry's time left before the running cap (None without one)."""
        return None if getattr(self, "_cap", None) is None else self._cap - self.entry_s

    def verify(self, items, what, timeout, warm=False):
        """The badge on (vk, stmt, store-relative path) items within `timeout` seconds for the whole
        run; a badge failure is the entry's (reject stage `check`, also for a run cut by `capped` 30 s
        past the stream's cap, whose message then says so: a badge built from a sabotaged record cache could
        hang, and the bot re-runs a `check` REJECT without the cache)."""
        shared = self.deadline is not None and timeout >= self.left() + 30 - 1e-3   # the run had the shared bound
        self.scrub()        # as before a request: no badge run reads an earlier one's per-CPU inode counts
        self.badge.run_s = 0.0
        try:
            return self.badge.verify(items, self.store, timeout=timeout, warm=warm)
        except BadgeError as e:
            self.charge(self.badge.run_s)
            self.badge.run_s = 0.0
            late = shared and self.left() + 30 <= 0.5
            raise Fail(f"{what}: {e}" + (f" (cut 30 s past the stream's cap: {self.deadline[1]})" if late else ""),
                       kind=e.kind, stage="check")
        finally:
            self.charge(getattr(self.badge, "run_s", 0.0))     # the badge process's own time (`Badge.run_s`)

    def capped(self):
        """The timeout of one badge run: what is left of one absolute bound, 30 s past the stream's
        cap, shared by every badge run of the benchmark (work begun before the cap ends within 30 s of
        it, however many runs remain; `due` starts none past the cap). No check has a bound of its
        own; every badge run of the benchmark is inside the stream."""
        if self.deadline is None:
            raise RuntimeError("a badge run outside the stream has no time bound")
        return max(0.0, self.left() + 30)

    def due(self, what):
        """Before a badge run: once the stream's cap has passed, no badge run starts; the stream is
        the entry's REJECT (`stream-cap`)."""
        if self.deadline is not None and self.left() <= 0:
            raise Fail(f"{what}: {self.deadline[1]}", stage="stream-cap")

    def check(self, items, what, timeout=None):
        """`acc` on items (vk, stmt, store-relative path): [(accepted, V ns)], each `V` one
        measurement, in one fresh badge process warmed with the organiser's warm-up input (never an
        item; its start-up capped by `badge_start_s`, `Badge.verify`). A rejection is an answer, not a
        failure (the caller decides what it means); a badge run that times out or crashes is the
        entry's failure. The badge run ends within `timeout`, by default within 30 s of the stream's
        cap. None starts once the stream's cap has passed (`due`)."""
        self.due(what)
        return self.verify(items, what, timeout if timeout is not None else self.capped(), warm=True)

    def judged(self, item, what, bounded=False):
        """The verifier check of one checked proof `item` (vk, stmt, store-relative path; AGENTS.md
        §6): `JUDGED_RUNS` = 3 separate badge runs (`check`), each a fresh process warmed with the
        organiser's input that checks this proof once and nothing else. So no judged check runs in a
        process that has seen its input, or any other output of the stream: a process that had
        checked a proof could answer it again from state kept since
        (`tests/harness/accprobe/MemoSub.lean`), and output `i + 1` contains `π_i`, so a process
        that had checked output `i` could answer the check of output `i` inside output `i + 1` from a
        memo (`MemoChildSub.lean`). Returns (accepted in the first run, accepted in every run, its
        three times in run order, their median `V`). A rejection is an answer; a failed run (timed
        out, too slow to start, crashed) raises `Fail` and the caller decides. Each run ends within
        `bounded(1)` with `bounded`, else within 30 s of the stream's cap. **All three runs are made
        even when one fails** (the first failure is raised after them, unless it is the stream's cap):
        the number of sandboxes the benchmark creates (their mount and namespace ids, the inode
        numbers of their copies on the runner's tmpfs) must not depend on the entry's verifier
        crashing, which a later request could read (review LR5 L1)."""
        runs, failed = [], None
        for r in range(1, JUDGED_RUNS + 1):
            try:
                (got,) = self.check([item], f"{what}, judged run {r} of {JUDGED_RUNS}",
                                    self.bounded(1) if bounded else None)
                runs.append(got)
            except Fail as e:
                if e.stage == "stream-cap":
                    raise
                failed = failed or e
        if failed:
            raise failed
        times = [ns for _, ns in runs]
        return runs[0][0], all(ok for ok, _ in runs), times, statistics.median(times)

    def canary_check(self, vk, targets, what, bounded=False):
        """The statement canaries (AGENTS.md §6) of every target (key, store path, stmt, others): the
        accepted file, checked against another statement, must be rejected. Each canary is checked
        once, all in one badge run (they test rejection, not time), which ends within
        `bounded(the number of canaries)` with `bounded`, else within 30 s of the stream's cap.
        Returns {key: [the names of the canaries `acc` accepted]} and the number of canaries
        checked; the caller decides. A badge failure raises `Fail`."""
        items = [(key, name, (vk, c, rel)) for key, rel, stmt, others in targets for name, c in canaries(stmt, others)]
        self.due(f"{what} canaries")
        res = self.verify([it for _, _, it in items], f"{what} canaries", self.bounded(len(items)) if bounded else self.capped())
        out = {key: [] for key, _, _, _ in targets}
        for (key, name, _), (ok, _) in zip(items, res):
            if ok:
                out[key].append(name)
        return out, len(items)

    def bounded(self, c):
        """The timeout of one badge run of `c` checks whose failure costs only the track `every` (a
        judged run of an intermediate output, `c = 1`, or a canary run of `c` canaries), its warm-up
        included: `INTERMEDIATE_SLACK_S + 2·(c + 1)·v_cap`, within the stream's cap; also the final
        output's canary run (its failure is still the entry's REJECT; review R8 HIGH 1). (The final
        output's three judged runs are bounded by the stream's cap alone: their `V` is capped by
        `v_cap`.)"""
        return min(self.capped(), INTERMEDIATE_SLACK_S + 2 * (c + 1) * self.p.v_cap_ms / 1e3)

    def scrub(self, batches=0):
        """Before every request, untimed and with no entry process alive: the
        per-CPU inode counters (pipes, sockets and other pseudo files; memfds) set to a fresh batch
        and a uniform random offset on every CPU of the job (`harness/tools/scrub.c`), so that what an
        earlier request did on a CPU does not show in a later request's inode numbers. With
        `batches` (before every timed request: `SCRUB_BATCHES`), the scrub also takes a uniform random
        number in [0, batches) of fresh batches of each kind from the machine-wide counters, so that
        the batch a timed request reads carries an earlier request's count only under that noise
        (review R8 HIGH 1; AGENTS.md §12 states what is left). Seconds, or
        None without the tool (the unit tests' benches). A failure is the runner's. It also runs
        before every badge run (`verify`), so that one of a proof's three judged runs cannot leave a
        count there for the next (a memo across the judged runs)."""
        if not getattr(self, "scrub_bin", None):
            return None
        t0 = time.monotonic()
        p = subprocess.run([self.scrub_bin] + ([str(batches)] if batches else []), capture_output=True, text=True,
                           timeout=120)
        if p.returncode != 0:
            raise RuntimeError(f"the inode counters' scrub failed: {p.stderr.strip()[-300:]}")
        return time.monotonic() - t0

    # -- calibration -------------------------------------------------------------------------------
    def calibrate(self):
        """Before the stream: the service's calls/s and permutations/s (published, not in the
        score). `c_P` is sampled during the stream (`sample`)."""
        cal = {"pinned_core": self.badge.core}
        svc = self.service("calibration")
        rec = {"keygen_ms": float(svc.info.get("keygen_ms", "nan"))}     # no CPU flags in a result
        try:
            # the CPUs this job may use, not the machine's count
            for threads in sorted({1, len(os.sched_getaffinity(0))}):
                out = subprocess.run([self.bench_bin, "oracle.sock", "throughput", str(threads), "1024", "64",
                                      str(self.p.service_calib_s)], cwd=svc.sock_dir, capture_output=True, text=True,
                                     timeout=60).stdout
                kv = dict(x.split("=") for x in out.split())
                # QUERY batches of 1,024 queries of 64 bytes; a keyed query of q bytes is
                # Keccak-256(k ‖ q) with |k| = 32: floor((32 + q) / 136) + 1 permutations
                per = (32 + int(kv["size"])) // 136 + 1
                rec[f"threads_{threads}"] = {"query_bytes": int(kv["size"]), "batch": int(kv["batch"]),
                                             "calls_per_s": float(kv["calls_per_s"]), "permutations_per_query": per,
                                             "permutations_per_s": float(kv["calls_per_s"]) * per,
                                             "us_per_request": float(kv["us_per_request"])}
        except Fail as e:
            e.rec = rec        # a failed run keeps its measurements in the result
            raise
        finally:
            # no entry process runs during the calibration: a service failing at its stop here is
            # the organiser's (a harness ERROR), never the entry's REJECT (review LR4 L2)
            try:
                self.stop(svc, rec)
            except Fail as e:
                raise RuntimeError(f"the calibration's service failed at its stop: {e}") from None
        cal["service"] = rec
        return cal

    def sample(self, before):
        """One calibration sample (AGENTS.md §6), with no entry process alive: an idle
        gap (`idle_s`), then `runs_per_sample` short runs of the prover-shaped workload `calib` on the
        job's CPUs (their median is the sample, every run is published). `before` names where in the
        benchmark it was taken."""
        time.sleep(self.p.calib_idle_s)
        s = {"before": before}
        if self.calib_bin:
            runs = []
            for _ in range(self.p.calib_runs):
                out = subprocess.run([self.calib_bin, str(len(os.sched_getaffinity(0))), str(self.p.calib_rounds)],
                                     capture_output=True, text=True, timeout=120).stdout
                kv = dict(x.split("=", 1) for x in out.split()[1:] if "=" in x)
                runs.append(int(kv["ns"]))
            s["calib_runs_ns"], s["calib_ns"] = runs, statistics.median(runs)
        self.samples.append(s)
        return s

    def calibration(self):
        """`c_P` (median of the samples over the season's fixed `ref_ns`), a health check of the
        machine, never a factor of the score (AGENTS.md §6): `c_P_drift = |c_P - 1|`, and `c_P_ok`
        unless it exceeds the season's `c_P_drift` while `ref_ns` is measured (`c_P_provisional`
        false; while it is a placeholder the drift is recorded, not enforced). The samples' relative
        spread is published."""
        cs = [s["calib_ns"] for s in self.samples if "calib_ns" in s]
        raw = statistics.median(cs) / self.p.calib_ref_ns if cs else 1.0
        cv = lambda xs: statistics.stdev(xs) / statistics.fmean(xs) if len(xs) > 1 else 0.0  # noqa: E731
        drift = abs(raw - 1.0)
        return {"c_P": raw, "c_P_drift": drift, "c_P_drift_cap": self.p.calib_drift,
                "c_P_ok": self.p.calib_ref_provisional or drift <= self.p.calib_drift, "calib_ref_ns": self.p.calib_ref_ns,
                "c_P_provisional": self.p.calib_ref_provisional, "calib_cv": cv(cs),
                "calib_within_sample_cv": [cv(s["calib_runs_ns"]) for s in self.samples if "calib_runs_ns" in s],
                "samples": self.samples}

    # -- the stream ----------------------------------------------------------------------------------
    def one(self, svc, tag, kind, inputs):
        """One timed request, within `ready_s`, `step_s` and the stream's cap: its `Step` record.
        Every failure is the entry's: the request's own errors (`request`; reject stage `request` in
        the service run, `timed-pass` in a timed pass, `Bench.phase`), the stream's cap reached
        during it (`stream-cap`). Before it the per-CPU inode counters are scrubbed (`scrub`); the
        setup and the binary need no warming, their copies on the runner's tmpfs being always
        resident (`Run.publish`). The request's /work
        is a private tmpfs of its own (`request` with no host directory), which holds `vk.hex` when
        the prover starts and is gone with the request: no file, inode number or free-space count of
        it reaches a later request. The service's socket appears in the request's `/run/rf` only at
        `go`. `tag` (`service{i}`, `timed{t}-step{i}`) names the request in the runner's log, its
        `Fail` messages and the records, never in the sandbox: the socket directory, whose path
        `/proc/self/mountinfo` shows, has 16 random hex characters from the CSPRNG for a name, and is
        removed after the request. Every request stages the same number of unnamed inodes on its
        /work, `STAGED`'s five, an input's placeholder (never linked, of the input's fixed size where
        it has one) for each input it does not get, so that a prover counting inode numbers before
        `go` cannot tell a timed request from the service run's or step 1 from step i (review LR4
        L1)."""
        # the request's own socket directory, on the service socket's filesystem (a hard link cannot
        # cross filesystems), runner-owned and empty until `go` (`request`, `sock_at_go`)
        sock = os.path.join(os.path.dirname(svc.sock_dir), "requests", secrets.token_hex(8))
        fresh_dir(sock)
        scrub_s = self.scrub(batches=SCRUB_BATCHES if key_of(inputs) else 0)
        dl = self.deadline[0] if self.deadline else None       # after the runner's own work (off the clock)
        pads = [bytes(n) for name, n in STAGED.items() if name not in inputs]
        r = request(self.run, kind, None, sock, inputs, self.p.step_s, self.p.file_cap, deadline=dl,
                    ready_s=self.p.ready_s, work_cap=self.p.work_cap, sock_at_go=svc.socket_path,
                    preset={"vk.hex": (svc.vk.hex() + "\n").encode()}, pads=pads)
        r.scrub_s = scrub_s
        self.charge((r.startup_s or 0.0) + (r.seconds or 0.0))      # the entry's time: start-up and the timed part
        self.alive(svc)
        self.dropped(svc, tag)
        remove_tree(sock)
        if r.status != "ok":
            if dl is not None and getattr(r, "at_deadline", False) and r.status in ("timeout", "no ready line"):
                raise Fail(f"{tag}: {self.deadline[1]} ({r.status})" + self.diag(svc, r.log), stage="stream-cap")
            raise Fail(f"{tag}: {r.status}" + self.diag(svc, r.log), stage=self.phase)
        return r

    def dropped(self, svc, tag):
        """After every request, with no entry process alive: the service closes every connection
        still open (the control line `drop`, `Service.drop`) and must report none left (`live=0`):
        no connection, and nothing parked in one (a response never read, a descriptor in its
        receive queue), outlives the request that opened it (review R5 HIGH 1, R4 MED 1). A count
        above zero, or no answer, is the runner's failure (a harness error): every connection of a
        dead request ends at its shutdown."""
        drop = getattr(svc, "drop", None)
        if drop is None:                    # the unit tests' stand-in services
            return
        try:
            live = drop()
        except ServiceError as e:
            raise RuntimeError(f"{tag}: the service did not answer `drop` ({e})") from None
        if live != 0:
            raise RuntimeError(f"{tag}: {live} connection(s) to the service still open after `drop`")

    def inputs(self, i, data, stmts, prev, key=None):
        """Step `i`'s request: (`first` or `step`, name → bytes). Every step gets its leaf,
        `leaf.json` (`{"n": n}`) and `leaf.bin` (the step's data, `32 · n` bytes `x_0 ‖ … ‖ x_(n−1)`,
        read from the runner's own file `data[i - 1]`; never its seed); a step `i ≥ 2` also
        `prev.stmt` (`c_{i-1}`) and `prev.bin` (`prev`, the service run's output of step `i - 1`); a
        timed request also `oracle.key` (the service's PRF key `k`, 64 lowercase hex characters and a
        newline). All are staged and appear in /work together when the clock runs."""
        ins = {} if i == 1 else {"prev.stmt": (stmts[i - 2].hex() + "\n").encode(), "prev.bin": prev}
        ins["leaf.json"] = leaf_json(self.p.n)
        with open(data[i - 1], "rb") as f:
            ins["leaf.bin"] = f.read()
        if key is not None:
            ins["oracle.key"] = (key + "\n").encode()
        return ("first" if i == 1 else "step"), ins

    def write_leaf_data(self, seeds):
        """Every step's data, `leaf_data(s_i, n)`, written to `leafdata/step{i}.bin` (a fresh
        runner-only directory beside the store): the files' paths, in step order."""
        if os.path.exists(self.leafdata):
            shutil.rmtree(self.leafdata)
        os.makedirs(self.leafdata, mode=0o700)
        paths = []
        for i, s in enumerate(seeds, 1):
            path = os.path.join(self.leafdata, f"step{i}.bin")
            with open(path, "wb") as f:
                f.write(draws.leaf_data(s, self.p.n))
            paths.append(path)
        return paths

    def stored(self, step):
        return open(os.path.join(self.store, step["file"]), "rb").read()

    def stream_run(self):
        """The stream (AGENTS.md §6) under one service lifetime: the service run (`service_run`),
        then the timed passes (`timed`), all within `stream_s`, which is the entry's REJECT if
        reached. `M` steps, a fresh process each, `PROVER first` then `PROVER step`; step `i` proves
        `c_i` from one fresh leaf of `n` blocks (`rfh.digest.stream_statements`). Before the first
        request every step's data is drawn and expanded (`rfh.draws.leaf_data`) into a file of the
        runner-only directory `leafdata` (never under the store, never bound into a sandbox), and
        every leaf statement is computed from those files."""
        p, name = self.p, "stream"
        p.check_shape()
        M = p.M
        seeds = draws.starts(M)               # fresh CSPRNG draws per evaluation, one per step
        data = self.write_leaf_data(seeds)
        self.log(f"[{name}] computing {M} leaf digests (n = {p.n} blocks each)")
        ld = digest.leaf_digests(data, self.service_bin)   # all before the first request, from the runner's data
        stmts, first = digest.stream_statements(ld)
        svc = self.service(name)
        rec = {"vk": svc.vk.hex(), "service": {k: v for k, v in svc.info.items() if k != "simd"}, "shape": p.shape(),
               "seeds": [s.hex() for s in seeds], "leaf_data": dict(draws.LEAF_DATA), "leaf_digests": [d.hex() for d in ld],
               "statements": [c.hex() for c in stmts], "steps": [],
               "truncated": False, "timed_runs": p.timed_runs,
               "request_dir": "a private tmpfs per request"}
        if self.run.view is None or self.run.seen:      # the service run's own copy (`fresh_copy`)
            self.fresh_copy(rec, "the service run")
        else:
            n, dt = self.run.copies[-1]
            rec["copies"] = [{"for": "the service run", "bytes": n, "seconds": dt}]
        t_stream = time.monotonic()
        self.deadline = (t_stream + p.stream_s, f"the stream's cap stream_s = {p.stream_s} s of the entry's time was reached")

        def clock():
            """The stream's clock (`deadline`): the entry's time it counted, the wall time, and the
            runner's overhead, off the clock, between them."""
            wall = time.monotonic() - t_stream
            rec["clock"] = {"stream_s": p.stream_s, "entry_s": self.entry_s, "wall_s": wall,
                            "runner_overhead_s": wall - self.entry_s}
        try:
            try:
                self.phase = "request"
                self.service_run(svc, rec, data, stmts, first)
                self.phase = "timed-pass"
                self.timed(svc, rec, data, stmts)
                self.alive(svc)
            except BaseException:
                # the failure in flight decides (its stage, or a harness error); the service's own
                # failure at its stop is only recorded
                clock()
                self.deadline = None
                shutil.rmtree(self.leafdata, ignore_errors=True)
                try:
                    self.stop(svc, rec)
                except Fail as e2:
                    rec["stop_error"] = str(e2)
                raise
            clock()
            self.deadline = None
            shutil.rmtree(self.leafdata, ignore_errors=True)     # the seeds, published, regenerate it
            self.stop(svc, rec)
            self.audit_replays(rec)
        except Fail as e:
            e.rec = rec        # a failed run keeps its measurements in the result
            e.stage = e.stage or self.phase
            raise
        finally:
            self.phase = "prover"
        rec["M"] = len(rec["steps"])
        rec["last_file"], rec["last_stmt"] = rec["steps"][-1]["file"], stmts[-1].hex()
        rec["calibration"] = self.calibration()
        return rec

    def fresh_copy(self, rec, what):
        """A fresh copy of the prover binary and the setup on the runner's tmpfs for the service run or
        a timed pass (`Run.publish`, the previous copy removed first), recorded in `rec["copies"]`.
        Only the steps of one pass share a copy: a tmpfs file keeps state a request holding it
        read-only can set (its shared memory policy; review LR5 H1), which would otherwise carry
        work from the untimed service run into a timed pass, or from one timed pass to the next
        (the median of three totals would then take a pass another had precomputed for). A timed
        pass's copy is made inside the stream, so its time counts toward `stream_s` (AGENTS.md §9);
        the service run's is made before the stream's cap starts."""
        n, dt = self.run.publish()
        rec.setdefault("copies", []).append({"for": what, "bytes": n, "seconds": dt})

    def service_run(self, svc, rec, data, stmts, first):
        """The service run (AGENTS.md §6), untimed: the stream against the service, every output
        kept. Its times are recorded (`P_service_s`), never scored. Every output's size is at most
        `pi_cap`: its `|π|` if it parses as a signed proof that `acc` accepts, else its file size
        (`|π|` checked as it arrives, the file size of a rejected one after its check: a rejected
        file's trace is no place to keep state uncounted); a breach is the entry's REJECT.

        The intermediate outputs are checked with `acc` against the runner's statements between
        steps (every `check_every` steps), each output judged on its own in three fresh warmed badge
        runs that check nothing else (`judged`, each run bounded by `bounded(1)`): `V_i` is the
        median of the output's three times (`V_runs_ns`, in run order); rejected in the first run is
        `accepted = False`, accepted there and rejected in a later run is `recheck_rejected`. Then,
        with no entry process alive, the **final** output on its own, in three runs of its own: it must be accepted against `c_M` in all three, with
        `|π_M| ≤ final_pi_cap`, `V_M ≤ v_cap` (the median of its three times) and its statement
        canaries (`stmt-bit`, `first-child`) rejected; any breach, and any failure of its checks, is
        the entry's REJECT. Last the track `every`: the canaries of outputs 1 and 2, checked even once
        the track is lost (so that the number of badge runs never depends on the entry's outputs,
        review LR5 L1; likewise every judged run is made after a failed one, `judged`). A breach of the track's conditions, or a failed (crashed or timed-out) check
        of an intermediate output or of those canaries, is recorded per step and only excludes the
        entry from that track (`every_reasons`)."""
        p, steps, pending, M = self.p, rec["steps"], [], self.p.M
        v_cap = p.v_cap_ms * 1e6

        def rejected_size(s):
            """An output that `acc` did not accept (rejected, or its check crashed or timed out) is
            sized by its whole file: its trace is no place to keep state uncounted."""
            if s["signed_proof"]:
                s["pi_bytes"], s["signed_proof"] = s["file_bytes"], False
            if s["pi_bytes"] > p.pi_cap:
                raise Fail(f"service run, step {s['index']}: the output, not accepted by acc (rejected, or its check "
                           f"failed), has {s['pi_bytes']} bytes, above pi_cap = {p.pi_cap}", stage="check")

        def flush():
            """Check the pending intermediate outputs, each in its own three runs; a failed badge run
            costs the track `every` (the stream's cap reached is the entry's REJECT)."""
            todo = list(pending)
            pending.clear()
            for k, it in todo:
                try:
                    ok, again, runs, v = self.judged(it, f"the service run's intermediate output {k + 1}", bounded=True)
                except Fail as e:
                    if e.stage == "stream-cap":
                        raise
                    steps[k]["check_error"] = printable(str(e), 300)
                    rejected_size(steps[k])
                    continue
                steps[k]["accepted"], steps[k]["V_runs_ns"], steps[k]["V_ns"] = ok, runs, v
                if ok and not again:
                    steps[k]["recheck_rejected"] = True
                if not (ok and again):
                    rejected_size(steps[k])
        for i in range(1, M + 1):
            if (i - 1) % p.calib_every == 0:
                flush()
                self.sample(f"service run, step {i}")
            if self.left() <= 0:
                raise Fail(f"service run, step {i}: {self.deadline[1]}", stage="stream-cap")
            kind, ins = self.inputs(i, data, stmts, self.stored(steps[-1]) if steps else None)
            r = self.one(svc, f"service{i}", kind, ins)
            rel = self.keep(f"stream/step{i}.bin", r.proof)
            steps.append(step_record(i, p.n, r, rel))
            s = steps[-1]
            self.log(f"[service run] step {i}: n={s['n']} P={r.seconds:.4f} s file={s['file_bytes']} B "
                     f"|π|={s['pi_bytes'] if s['signed_proof'] else 'not a signed proof'}")
            if s["pi_bytes"] > p.pi_cap:
                raise Fail(f"service run, step {i}: the output's {'|π|' if s['signed_proof'] else 'file size'} is "
                           f"{s['pi_bytes']} bytes, above pi_cap = {p.pi_cap}", stage="request")
            if i < M:
                pending.append((i - 1, (svc.vk, stmts[i - 1], rel)))
                if len(pending) >= p.check_every:
                    flush()
        flush()
        # the final output, on its own: every failure here is the entry's REJECT
        final, item = steps[-1], (svc.vk, stmts[M - 1], steps[-1]["file"])
        ok, again, runs, v = self.judged(item, "service run: the final output")
        final["accepted"], final["V_runs_ns"], final["V_ns"] = ok, runs, v
        if not ok:
            raise Fail(f"service run: the final output (step {M}) is rejected by acc against c_{M}"
                       + self.diag(svc, ""), stage="check")
        if not again:
            final["recheck_rejected"] = True
            raise Fail(f"service run: the final output (step {M}), accepted by acc in its first judged run, is "
                       "rejected when checked again in another", stage="check")
        if final["pi_bytes"] > p.final_pi_cap:
            # |π| is parsed by the runner, not judged by the badge: a cap of the request's output
            raise Fail(f"service run: the final output (step {M}) has |π| = {final['pi_bytes']} bytes, above "
                       f"final_pi_cap = {p.final_pi_cap}", stage="request")
        if final["V_ns"] > v_cap:
            raise Fail(f"service run: the final output (step {M}) takes V = {final['V_ns'] / 1e6:.3f} ms (the median "
                       f"of its three judged runs, {[round(x / 1e6, 3) for x in runs]} ms), above v_cap = "
                       f"{p.v_cap_ms:g} ms", stage="check")
        # bounded like every canary run (review R8 HIGH 1: a verifier stalling on the final output's
        # canaries for a chosen time would otherwise move the clock a timed request reads)
        bad, rec["canaries"] = self.canary_check(svc.vk, [(M, final["file"], stmts[M - 1], [("first-child", first[M - 1])])],
                                                 "service run: the final output", bounded=True)
        final["canaries_accepted"] = bad[M]
        if bad[M]:
            raise Fail(f"service run: the final output (step {M}): statement canaries accepted by acc (a proof "
                       f"accepted for another statement): {bad[M]}", stage="check")
        # the track `every`: never the run's failure. The canary run is made even once the track is
        # lost, so that the number of badge runs does not depend on the entry's outputs (review LR5 L1)
        ks = [k for k in (1, 2) if k < M]
        if ks:
            try:
                bad, n = self.canary_check(svc.vk, [(k, steps[k - 1]["file"], stmts[k - 1], [("first-child", first[k - 1])])
                                                    for k in ks], "service run: outputs 1 and 2", bounded=True)
                rec["canaries"] += n
                for k in ks:
                    steps[k - 1]["canaries_accepted"] = bad[k]
            except Fail as e:
                if e.stage == "stream-cap":
                    raise
                for k in ks:
                    steps[k - 1]["canary_error"] = printable(str(e), 300)
        for s in steps[:-1]:              # every output not accepted after all its checks: sized by its file
            if not s.get("accepted") or s.get("check_error") or s.get("recheck_rejected"):
                rejected_size(s)
        why = every_reasons(p, rec)
        rec["every"] = {"eligible": not why, "reasons": why}
        self.log(f"[service run] final output accepted (|π| {final['pi_bytes']} B, V {final['V_ns'] / 1e6:.3f} ms); "
                 + ("eligible for the track `every`" if not why else f"not eligible for `every`: {'; '.join(why)[:300]}"))

    def audit_replays(self, rec):
        """After the service has exited (its `stats` in `rec`): the timed passes made exactly the
        service run's signatures, each pass all of them and nothing else: no `MISMATCH`
        (`mismatches = 0`) and `replays = timed_runs · signatures`. A replay refusal is a bit a timed
        pass could read (OK or MISMATCH at an index), so any is the entry's REJECT."""
        st, want = rec.get("service_stats") or {}, self.p.timed_runs
        if not all(isinstance(st.get(k), int) for k in ("signatures", "replays", "mismatches")):
            raise Fail(f"the service reported no replay statistics ({sorted(st)})", stage="timed-pass")
        if st["mismatches"]:
            raise Fail(f"a SIGN in a timed pass differed from the service run's ({st['mismatches']} MISMATCH refusals"
                       + (f"; {printable(rec['service_mismatches'][0], 300)}" if rec.get("service_mismatches") else "") + ")",
                       stage="timed-pass")
        if st["replays"] != want * st["signatures"]:
            raise Fail(f"the timed passes made {st['replays']} signatures, not timed_runs · signatures = {want} · "
                       f"{st['signatures']}: a timed pass must make exactly the service run's SIGN requests",
                       stage="timed-pass")

    def timed(self, svc, rec, data, stmts):
        """The timed passes (AGENTS.md §6): `timed_runs` passes of steps `1 … M`, each a fresh
        sandbox as in the service run, after the service run's request directories are gone. Each
        pass binds a fresh copy of the binary and the setup, the previous pass's removed first
        (`fresh_copy`). Before each pass the service enters replay mode (`Service.replay`) and reveals its PRF key `k`; a
        timed request gets the same leaf (`leaf.json` and `leaf.bin`, the same bytes), the runner's
        statement, the **service run's** output of step `i - 1` as `prev.bin`, and `oracle.key`.
        Each output must be byte-identical to the service run's output of that step, else the
        entry's REJECT naming the pass, the step and the first differing byte; a pass that does not
        finish (a request's failure, the stream's cap) is the entry's REJECT too. Each step records
        its `timed_runs` times in pass order (`P_timed_s`); `score` takes the median pass."""
        p, steps = self.p, rec["steps"]
        for t in range(1, p.timed_runs + 1):
            self.fresh_copy(rec, f"timed pass {t}")
            self.sample(f"timed pass {t}")
            # an untimed delay, uniform in [0, PASS_DELAY_S) from the CSPRNG, before each pass: the
            # clock a timed request reads carries a service-run request's chosen duration only under
            # that noise (review R8 HIGH 1)
            delay = secrets.randbelow(int(PASS_DELAY_S * 1e6)) / 1e6
            time.sleep(delay)
            rec.setdefault("pass_delays_s", []).append(delay)
            try:
                key = svc.replay()
            except ServiceError as e:
                raise Fail(f"timed pass {t}: the service did not enter replay mode ({e})", stage="timed-pass")
            for i in range(1, p.M + 1):
                if self.left() <= 0:
                    raise Fail(f"timed pass {t}, step {i}: {self.deadline[1]}", stage="stream-cap")
                ref = self.stored(steps[i - 1])
                kind, ins = self.inputs(i, data, stmts, self.stored(steps[i - 2]) if i > 1 else None, key)
                r = self.one(svc, f"timed{t}-step{i}", kind, ins)
                if r.proof != ref:
                    rel = self.keep(f"stream/timed{t}-step{i}.bin", r.proof)
                    off = next((k for k, (x, y) in enumerate(zip(r.proof, ref)) if x != y), min(len(r.proof), len(ref)))
                    raise Fail(f"timed pass {t}, step {i}: the output differs from the service run's output of the "
                               f"step, first at byte offset {off} ({len(r.proof)} bytes, the service run's {len(ref)}; "
                               f"kept as {rel}): a prover's output must be a function of its inputs, its setup and the "
                               "oracle answers", stage="timed-pass")
                s = steps[i - 1]
                s.setdefault("P_timed_s", []).append(r.seconds)
                s.setdefault("timed", []).append({"startup_s": r.startup_s, "kill_s": r.kill_s, "mem_peak": r.mem_peak,
                                                  "work_bytes": r.work_bytes, "ended_by": r.ended,
                                                  "scrub_s": getattr(r, "scrub_s", None)})
                self.log(f"[timed pass {t}] step {i}: P={r.seconds:.4f} s (identical output)")
            # the replay refusals of the pass, from the service's own counter (`stats`), not from its
            # log, which keeps only its first 32 refusals (review R5 LOW 5)
            mism, n_mism = svc.mismatches(), None
            if hasattr(svc, "stats"):
                try:
                    n_mism = svc.stats().get("mismatches")
                except ServiceError as e:
                    raise RuntimeError(f"timed pass {t}: the service did not answer `stats` ({e})") from None
            if mism or n_mism:
                raise Fail(f"timed pass {t}: a SIGN in a timed pass differed from the service run's "
                           f"({n_mism if n_mism is not None else len(mism)} refused"
                           + (f"; the first: {printable(mism[0], 300)}" if mism else "") + "): a timed pass must make "
                           "exactly the service run's SIGN requests, in its order", stage="timed-pass")
        if self.left() > 30:              # a closing sample, only with 30 s of the cap to spare
            self.sample("closing")


# the inputs a request can get, with the size of the placeholder staged for each it does not get
# (`Bench.one`): a statement or a key is 65 bytes (64 hex characters and a newline) in every request
# that has one; the leaf's files and `prev.bin` have the step's sizes in the service run and in the
# timed passes alike (step 1, which has no `prev.*`, is told by its command, `first`)
STAGED = {"leaf.json": 0, "leaf.bin": 0, "prev.stmt": 65, "prev.bin": 0, "oracle.key": 65}
SCRUB_BATCHES = 256        # before every timed request the scrub takes [0, 256) machine-wide batches of each kind
PASS_DELAY_S = 2.0         # the untimed delay before each timed pass is uniform in [0, 2) s


def key_of(inputs):
    """Whether a request's inputs are a timed request's (they hold `oracle.key`)."""
    return "oracle.key" in inputs
INTERMEDIATE_SLACK_S = 60  # seconds a badge run of intermediate checks may take beyond 2 v_cap per check
JUDGED_RUNS = 3           # the fresh badge runs that judge each checked proof; its V is their median


def fs_free(path):
    """(free bytes, free inodes) of the filesystem of `path`, or None."""
    try:
        st = os.statvfs(path)
        return st.f_bavail * st.f_frsize, st.f_favail
    except OSError:
        return None


def output_size(data):
    """(size, signed): an output's size for the caps, its `|π|` if it parses as one signed proof
    (`harness/FORMAT.md`), else its file size."""
    s = signed.parse(data)
    return (len(s.pi), True) if s is not None else (len(data), False)


def step_record(i, n_i, r, rel):
    """The per-step record of the service run (the timed passes add `P_timed_s`, the checks
    `accepted`, `V_runs_ns`, `V_ns`, the canaries, the score its derived fields `P_s`, `share_P`)."""
    size, ok = output_size(r.proof)
    return {"index": i, "n": n_i, "P_service_s": r.seconds, "startup_s": r.startup_s, "kill_s": r.kill_s,
            "mem_peak": r.mem_peak, "file": rel, "file_bytes": len(r.proof), "pi_bytes": size, "signed_proof": ok,
            "ended_by": r.ended, "work_bytes": r.work_bytes, "t_stop_ns": r.t_stop_ns,
            "scrub_s": getattr(r, "scrub_s", None)}


def every_reasons(p, stream, canaries=True):
    """Why the stream is not eligible for the track `every` (AGENTS.md §7), [] if it is: every
    output checked and accepted by `acc` against its statement in each of its three judged runs, with
    `|π_i| ≤ pi_cap` and `V_i ≤ v_cap` (the median of its three times), and the statement canaries of
    outputs 1 and 2 checked and rejected (with `canaries`). (The final output's own conditions are
    the run's: their breach is a REJECT, never a reason here.) From the per-step records alone, so
    the aggregation recomputes it."""
    out, v_cap = [], p.v_cap_ms * 1e6
    for s in stream["steps"]:
        i = s.get("index")
        if s.get("check_error"):
            out.append(f"output {i}: its check failed ({s['check_error']})")
            continue
        if not s.get("accepted"):
            out.append(f"output {i} rejected by acc")
            continue
        if s.get("recheck_rejected"):
            out.append(f"output {i}: rejected by acc when checked again (accepted in its first judged run)")
            continue
        if not isinstance(s.get("pi_bytes"), int) or s["pi_bytes"] > p.pi_cap:
            out.append(f"output {i}: |π| = {s.get('pi_bytes')} bytes above pi_cap = {p.pi_cap}")
        if not isinstance(s.get("V_ns"), (int, float)) or s["V_ns"] > v_cap:
            v = s.get("V_ns")
            out.append(f"output {i}: V = {v / 1e6 if isinstance(v, (int, float)) else v} ms above v_cap = {p.v_cap_ms:g} ms")
    for s in stream["steps"][:2] if canaries else []:
        if s.get("canary_error"):
            out.append(f"output {s.get('index')}: its statement canaries' check failed ({s['canary_error']})")
        elif s.get("accepted") and s.get("canaries_accepted") != []:
            out.append(f"output {s.get('index')}: statement canaries "
                       + (f"accepted by acc {s['canaries_accepted']}" if s.get("canaries_accepted") else "not checked"))
    return out


class MalformedStream(ValueError):
    """A stream record the score cannot be computed from: a step whose `P_timed_s` is not exactly
    the season's `timed_runs` times (`pass_totals`), or a record not of the shape `check_record`
    requires. A runner fault, never the entry's: the runner and the aggregation record it as an
    organiser ERROR named `malformed`."""


def _number(x):
    return type(x) in (int, float) and math.isfinite(x) and x >= 0


def check_record(p: Params, stream):
    """The shape of a passed stream record, before its score is computed (the runner's and the
    aggregation's; `MalformedStream` if not): a record with exactly the season's `M` steps, their
    `index` 1 … M in order; every step's `pi_bytes` a non-negative integer; every step that records
    a verifier time (`V_ns` or `V_runs_ns`) records `JUDGED_RUNS` finite, non-negative times in
    `V_runs_ns` whose median is `V_ns`; and the final step, the run's own conditions: accepted (not
    rejected when checked again, no failed check), timed, `|π_M| ≤ final_pi_cap`, `V_M ≤ v_cap`. So
    a record that kept two of its sixteen steps, or a `V_ns` that is not its runs' median, is never
    scored (review LR2 M3)."""
    steps = stream.get("steps") if isinstance(stream, dict) else None
    if not isinstance(steps, list) or not steps:
        raise MalformedStream("the passed run has no stream record or no steps")
    if not all(isinstance(s, dict) for s in steps) or [s.get("index") for s in steps] != list(range(1, p.M + 1)):
        got = [s.get("index") if isinstance(s, dict) else None for s in steps][:20]
        raise MalformedStream(f"the steps' indices are {got}, not 1 … M = {p.M}")
    for s in steps:
        if type(s.get("pi_bytes")) is not int or s["pi_bytes"] < 0:
            raise MalformedStream(f"step {s['index']}: pi_bytes = {str(s.get('pi_bytes'))[:40]} is not a size")
        if "V_ns" in s or "V_runs_ns" in s:
            runs = s.get("V_runs_ns")
            if not (isinstance(runs, list) and len(runs) == JUDGED_RUNS and all(_number(x) for x in runs)
                    and _number(s.get("V_ns")) and statistics.median(runs) == s["V_ns"]):
                raise MalformedStream(f"step {s['index']}: V_runs_ns = {str(runs)[:80]} and V_ns = "
                                      f"{str(s.get('V_ns'))[:30]} are not {JUDGED_RUNS} judged times and their median")
    f = steps[-1]
    if not (f.get("accepted") is True and not f.get("recheck_rejected") and not f.get("check_error")
            and "V_ns" in f and f["pi_bytes"] <= p.final_pi_cap and f["V_ns"] <= p.v_cap_ms * 1e6):
        raise MalformedStream(f"the final step (step {p.M}) of a passed run is not accepted within final_pi_cap and v_cap")


def pass_totals(p: Params, steps):
    """`T_t = Σ_i P_{i,t}` for each timed pass `t` (in pass order, summed in step order), from each
    step's `P_timed_s`; `MalformedStream` unless every step holds exactly `timed_runs` finite,
    non-negative times."""
    for s in steps:
        t = s.get("P_timed_s")
        if not (isinstance(t, list) and len(t) == p.timed_runs
                and all(type(x) in (int, float) and math.isfinite(x) and x >= 0 for x in t)):
            raise MalformedStream(f"step {s.get('index')}: P_timed_s = {str(t)[:80]} is not {p.timed_runs} times, "
                                  "one per timed pass")
    totals = [0.0] * p.timed_runs
    for s in steps:
        for t in range(p.timed_runs):
            totals[t] += s["P_timed_s"][t]
    return totals


def median_pass(totals):
    """`t*` (1-based): the pass whose total is the median of `totals` (an odd number of them); among
    passes with that total, the lowest index."""
    med = sorted(totals)[len(totals) // 2]
    return totals.index(med) + 1


def score(p: Params, stream):
    """The score (AGENTS.md §7; seconds, lower is better), from the per-step records alone:

        T_t      = Σ_i P_{i,t}                         the total of timed pass t (t = 1 … timed_runs)
        t*       = the pass whose total is the median of the T_t (ties: the lowest such index)
        P_total  = T_{t*},   P_i = P_{i,t*}            (so Σ_i P_i = P_total)
        S        = P_total · 2^(|π_M| / size_ref)                  the track `final`
        S_every  = P_total · 2^(max_i |π_i| / size_ref)            the track `every`, when eligible

    `tracks` names the score field of each track the run is in: always `final` (a run that fails a
    `final` condition is REJECTed), `every` too when `every_reasons` is empty, else
    `tracks_reason` says why not (and `S_every`, `size_factor_every`, `max_pi_bytes` are absent).
    Published diagnostics: the pass totals and the median pass, the untimed service run's total,
    each step's share of `P_total`. Adds the derived per-step fields in place (`P_s`, `share_P`).
    A step without exactly `timed_runs` timed times raises `MalformedStream`."""
    if not stream or not stream.get("steps"):
        return {}
    steps, cal = stream["steps"], stream.get("calibration") or {}
    totals = pass_totals(p, steps)
    t_star = median_pass(totals)
    P = totals[t_star - 1]
    pi_M = steps[-1]["pi_bytes"]
    f = 2 ** (pi_M / p.size_ref)
    why = every_reasons(p, stream)
    out = {"S": P * f, "P_total_s": P, "size_factor": f, "final_pi_bytes": pi_M,
           "final_file_bytes": steps[-1].get("file_bytes"),       # published beside |π_M|, never scored
           "pass_totals_s": totals, "median_pass": t_star,
           "tracks": {"final": "S", **({} if why else {"every": "S_every"})}}
    if why:
        out["tracks_reason"] = {"every": "; ".join(why)[:2000]}
    else:
        pi_max = max(s["pi_bytes"] for s in steps)
        f_every = 2 ** (pi_max / p.size_ref)
        out.update(S_every=P * f_every, size_factor_every=f_every, max_pi_bytes=pi_max)
    out.update(size_ref=p.size_ref, M=len(steps), sum_n=sum(s["n"] for s in steps),
               c_P=cal.get("c_P"), c_P_provisional=bool(cal.get("c_P_provisional")))
    if all(isinstance(s.get("P_service_s"), (int, float)) for s in steps):
        out["P_total_service_run_s"] = sum(s["P_service_s"] for s in steps)      # published, never scored
    for s in steps:
        s["P_s"] = s["P_timed_s"][t_star - 1]
        s["share_P"] = s["P_s"] / P if P else 0.0
    return out

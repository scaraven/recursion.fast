"""The benchmark of one entry (TRUSTED RUNTIME): the IVC stream, its checks and calibration, the
re-timing and the score (the rules are in `AGENTS.md` §6, §7). One stream per
evaluation, with its own service lifetime; every request is a fresh sandboxed process; every check
and every calibration sample runs while no entry process is alive. Every step the entry controls is
capped by the season file, inside its job's time limit: a request over its cap fails with the
reason; a stream that reaches `stream_s` (a slow or hung check included) is truncated, or fails if
no step was checked.
"""
import hashlib
import json
import math
import os
import platform
import shutil
import statistics
import subprocess
import tempfile
import time
import tomllib
from dataclasses import dataclass

from . import digest, draws
from .checks import Badge, BadgeError, canaries
from .prover import fresh_dir, remove_tree, request
from .sandbox import memcap, memcap_method
from .service import Service, ServiceError


class Fail(Exception):
    """The entry fails the benchmark (the message says why). `kind`: the badge's failure kind when a
    check failed (`timeout`, `crash`), else None."""

    def __init__(self, msg, kind=None):
        super().__init__(msg)
        self.kind = kind


def printable(text, limit=1200):
    """Untrusted text (a prover's output) as printable ASCII for a result and a public comment:
    every other character becomes `?`, backticks become `'`, and it is put in a code
    span."""
    t = "".join(c if 32 <= ord(c) < 127 else "?" for c in text.replace("`", "'"))
    return "`" + t[-limit:] + "`"


class _Cap(Exception):
    """The stream's cap stopped a check batch (the stream is truncated there)."""


@dataclass
class Params:
    name: str
    K: float
    kappa: float
    n_ref: int
    s_ref: int
    R: float
    M: int
    n_lo: int
    n_hi: int
    lengths: list
    ready_s: float
    step_s: float
    stream_s: float
    check_every: int
    retime_factor: float
    retime_frac: float
    calib_every: int
    calib_idle_s: float
    calib_rounds: int
    calib_ref_ns: float
    calib_drift: float
    calib_runs: int
    calib_ref_provisional: bool
    triv_chains: int
    triv_n: int
    v_ref_ms: float
    service_calib_s: float
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
        """The season file at `path`; with `check`, its `[stream] lengths` validated (a ValueError
        naming the defect). `check=False` is for the aggregation alone, which names a malformed list
        as the organiser's ERROR instead of failing."""
        t = tomllib.load(open(path, "rb"))
        g = lambda sec, k: t[sec][k]  # noqa: E731 (a KeyError names the missing parameter)
        p = Params(
            name=t["name"], K=float(g("score", "K")), kappa=float(g("score", "kappa")),
            n_ref=g("score", "n_ref"), s_ref=g("score", "s_ref"), R=float(g("score", "R")),
            M=g("stream", "M"),
            n_lo=g("stream", "n_lo"), n_hi=g("stream", "n_hi"), ready_s=g("stream", "ready_s"),
            step_s=g("stream", "step_s"), stream_s=g("stream", "stream_s"), check_every=g("stream", "check_every"),
            retime_factor=float(g("stream", "retime_factor")), retime_frac=float(g("stream", "retime_frac")),
            calib_every=g("calibration", "every"), calib_idle_s=float(g("calibration", "idle_s")),
            calib_rounds=g("calibration", "rounds"), calib_ref_ns=float(g("calibration", "ref_ns")),
            calib_drift=float(g("calibration", "c_P_drift")), calib_runs=g("calibration", "runs_per_sample"),
            calib_ref_provisional=bool(g("calibration", "ref_provisional")), triv_chains=g("calibration", "triv_chains"),
            triv_n=g("calibration", "triv_n"), v_ref_ms=float(t["calibration"].get("v_ref_ms", 0.0)),
            service_calib_s=g("calibration", "service_s"),
            file_cap=g("caps", "file_cap"), setup_s=g("caps", "setup_s"),
            setup_cap=g("caps", "setup_cap"), work_cap=g("caps", "work_cap"), build_s=g("caps", "build_s"),
            mem_prover=g("memory", "prover"), mem_service=g("memory", "service"), mem_badge=g("memory", "badge"),
            fingerprint=g("machine", "fingerprint"), lengths=t["stream"].get("lengths"))
        if check:
            p.check_lengths()
        return p

    def check_lengths(self):
        """The season's fixed chain lengths (`[stream] lengths`): exactly `M + 1` integers (step 1's
        two chains, then one per step), each in `[n_lo, n_hi]`; else a ValueError naming the defect."""
        ns, M = self.lengths, self.M
        if not (isinstance(ns, list) and all(type(n) is int for n in ns)):
            raise ValueError("[stream] lengths is not a list of integers")
        if type(M) is not int:
            raise ValueError(f"[stream] M is not an integer ({M!r}), so [stream] lengths cannot be checked")
        if len(ns) != M + 1:
            raise ValueError(f"[stream] lengths has {len(ns)} entries, M + 1 = {M + 1} expected "
                             "(step 1's two chains, then one per step)")
        bad = [(k, n) for k, n in enumerate(ns) if not self.n_lo <= n <= self.n_hi]
        if bad:
            raise ValueError(f"[stream] lengths outside [n_lo, n_hi] = [{self.n_lo}, {self.n_hi}] at (index, n) {bad[:4]}")


def chain_json(n, start):
    return json.dumps({"n": n, "start": start.hex()}).encode()


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


def build_calib(out_dir):
    """Build the calibration workload (`harness/tools/calib.c`) with the runner's `gcc`, before any
    entry code runs; (path, info)."""
    src = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools", "calib.c")
    os.makedirs(out_dir, exist_ok=True)
    out = os.path.join(out_dir, "calib")
    p = subprocess.run(["gcc", "-O2", "-pthread", "-o", out, src], capture_output=True, text=True, timeout=120)
    if p.returncode != 0:
        raise RuntimeError(f"calib build failed: {p.stderr[-500:]}")
    return out, {"source_sha256": hashlib.sha256(open(src, "rb").read()).hexdigest(),
                 "binary_sha256": hashlib.sha256(open(out, "rb").read()).hexdigest()}


def request_root():
    """Where request directories live: a tmpfs (`/dev/shm`), whose pages a prover writes are
    charged to its own memory cgroup, so a request cannot fill the runner's disk; else None (the
    work directory)."""
    d = "/dev/shm"
    if os.path.isdir(d) and os.access(d, os.W_OK) and not os.environ.get("RF_NO_SHM"):
        return tempfile.mkdtemp(prefix="rf-req-", dir=d)
    return None


class Bench:
    def __init__(self, p: Params, run, badge_dir, service_bin, bench_bin, work, calib_bin=None, log=print):
        self.p, self.run, self.service_bin, self.bench_bin = p, run, service_bin, bench_bin
        self.work, self.log, self.calib_bin = work, log, calib_bin
        self.store = os.path.join(work, "store")
        os.makedirs(self.store, exist_ok=True)
        self.badge = Badge(badge_dir, p.mem_badge, os.path.join(work, "badge-scratch"))
        os.makedirs(self.badge.scratch, exist_ok=True)
        self.deadline = None                 # (monotonic time, reason) of the running cap (`stream_s`)
        self.triv = None                     # the chain checker's calibration instance (leaves.json, root)
        self.samples = []                    # the interleaved calibration samples
        self.req_root = None

    # -- the service ---------------------------------------------------------------------------
    def service(self, name):
        svc = Service(self.service_bin, os.path.join(self.work, "svc", name),
                      wrap=memcap(self.p.mem_service, f"rf-svc-{name}-{os.getpid()}"),
                      stderr_path=os.path.join(self.work, "svc", f"{name}.stderr"))
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
        """Seconds left before the running cap (None without one)."""
        return None if self.deadline is None else self.deadline[0] - time.monotonic()

    def verify(self, items, what, timeout, warm=False):
        """The badge on (vk, stmt, store-relative path) items within `timeout` seconds for the whole
        run; a badge failure is the entry's."""
        try:
            return self.badge.verify(items, self.store, timeout=timeout, warm=warm)
        except BadgeError as e:
            raise Fail(f"{what}: {e}", kind=e.kind)

    def capped(self):
        """The timeout of one badge run: 30 s past the stream's cap (work begun before the cap ends
        within 30 s of it). No check has a bound of its own; every badge run of the benchmark is
        inside the stream."""
        if self.deadline is None:
            raise RuntimeError("a badge run outside the stream has no time bound")
        return max(0.0, self.left()) + 30

    def check(self, items, what, timeout=None):
        """`acc` on items (vk, stmt, store-relative path, label): every one must be accepted, and its
        time `V_i` is one measurement, the batch warmed with an untimed first check. The badge
        run ends within `timeout`, by default within 30 s of the stream's cap. Returns [ns]."""
        bare = [(vk, c, rel) for vk, c, rel, _ in items]
        res = self.verify(bare, what, timeout if timeout is not None else self.capped(), warm=True)
        for (_, _, _, label), (ok, _) in zip(items, res):
            if not ok:
                raise Fail(f"{what}: {label} rejected by acc")
        return [ns for _, ns in res]

    def canary_check(self, vk, targets, what):
        """The statement canaries of every target (store path, stmt, others): the accepted file,
        checked against another statement, must be rejected."""
        items = [(vk, c, rel, f"{rel} {name}") for rel, stmt, others in targets for name, c in canaries(stmt, others)]
        res = self.verify([(vk, c, rel) for vk, c, rel, _ in items], f"{what} canaries", self.capped())
        bad = [label for (_, _, _, label), (ok, _) in zip(items, res) if ok]
        if bad:
            raise Fail(f"{what}: canaries accepted (a proof accepted for another statement): {bad[:5]}")
        return len(items)

    # -- calibration -------------------------------------------------------------------------------
    def calibrate(self):
        """Before the stream: the chain checker's instance (`triv_chains` chains of `triv_n` steps,
        `2^24` permutations in season 1, fresh starts, its root computed here) and the service's
        calls/s and permutations/s (published, not in the score). `T_triv` and `c_P` are
        sampled during the stream (`sample`)."""
        inst = os.path.join(self.work, "instance")
        os.makedirs(inst, exist_ok=True)
        starts = draws.starts(self.p.triv_chains)
        root = digest.tree_root(digest.leaf_digests(starts, self.p.triv_n, self.service_bin))
        with open(os.path.join(inst, "leaves.json"), "w") as f:
            json.dump({"n": self.p.triv_n, "starts": [s.hex() for s in starts]}, f)
        self.triv = (os.path.join(inst, "leaves.json"), root)
        cal = {"triv_permutations": self.p.triv_chains * self.p.triv_n, "pinned_core": self.badge.core}
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
            self.stop(svc, rec)
        cal["service"] = rec
        return cal

    def sample(self, before_step):
        """One calibration sample (AGENTS.md §6), with no entry process alive: an idle
        gap (`idle_s`), then `runs_per_sample` short runs of the prover-shaped workload `calib` on the
        job's CPUs (their median is the sample, every run is published) and one run of the chain
        checker on one pinned core."""
        time.sleep(self.p.calib_idle_s)
        s = {"before_step": before_step}
        if self.calib_bin:
            runs = []
            for _ in range(self.p.calib_runs):
                out = subprocess.run([self.calib_bin, str(len(os.sched_getaffinity(0))), str(self.p.calib_rounds)],
                                     capture_output=True, text=True, timeout=120).stdout
                kv = dict(x.split("=", 1) for x in out.split()[1:] if "=" in x)
                runs.append(int(kv["ns"]))
            s["calib_runs_ns"], s["calib_ns"] = runs, statistics.median(runs)
        s["triv_ns"] = self.badge.chaincheck(self.triv[0], self.triv[1])
        self.samples.append(s)
        return s

    def calibration(self):
        """`c_P` (median of the samples over the season's fixed `ref_ns`), a health check of the
        machine, never a factor of the score (AGENTS.md §6): `c_P_drift = |c_P - 1|`, and `c_P_ok`
        unless it exceeds the season's `c_P_drift` while `ref_ns` is measured (`c_P_provisional`
        false; while it is a placeholder the drift is recorded, not enforced). `T_triv` (median of
        the chain checker's samples); `v_ref = T_triv / R`, or the season's fixed `v_ref_ms` (the
        smoke). The samples' relative spread is published."""
        cs = [s["calib_ns"] for s in self.samples if "calib_ns" in s]
        ts = [s["triv_ns"] for s in self.samples]
        raw = statistics.median(cs) / self.p.calib_ref_ns if cs else 1.0
        triv = statistics.median(ts)
        v_ref = self.p.v_ref_ms * 1e6 if self.p.v_ref_ms else triv / self.p.R
        cv = lambda xs: statistics.stdev(xs) / statistics.fmean(xs) if len(xs) > 1 else 0.0  # noqa: E731
        drift = abs(raw - 1.0)
        return {"c_P": raw, "c_P_drift": drift, "c_P_drift_cap": self.p.calib_drift,
                "c_P_ok": self.p.calib_ref_provisional or drift <= self.p.calib_drift, "calib_ref_ns": self.p.calib_ref_ns,
                "c_P_provisional": self.p.calib_ref_provisional, "T_triv_ns": triv, "R": self.p.R, "v_ref_ns": v_ref,
                "v_ref_source": "fixed by the season file" if self.p.v_ref_ms else "measured: T_triv / R",
                "calib_cv": cv(cs), "triv_cv": cv(ts),
                "calib_within_sample_cv": [cv(s["calib_runs_ns"]) for s in self.samples if "calib_runs_ns" in s],
                "samples": self.samples}

    # -- the stream ----------------------------------------------------------------------------------
    def one(self, svc, tag, kind, inputs):
        """One timed request, within `ready_s`, `step_s` and the stream's cap: its `Step` record, or
        None when the stream's cap stopped it. Every other failure is the entry's:
        the request's own errors (`request`), a directory the runner cannot prepare or remove, and a
        filesystem left fuller than before the request (bytes or inodes of the request
        directories' filesystem, after cleanup)."""
        root = self.req_root or os.path.join(self.work, "requests")
        os.makedirs(root, exist_ok=True)
        before = fs_free(root)
        work = os.path.join(root, tag)
        try:
            fresh_dir(work)
            with open(os.path.join(work, "vk.hex"), "w") as f:
                f.write(svc.vk.hex() + "\n")
        except OSError as e:          # only a previous request can have left the filesystem so
            raise Fail(f"step {tag}: the request directory cannot be prepared ({e.strerror or e}); "
                       "the filesystem is in the state the prover's requests left it")
        dl = self.deadline[0] if self.deadline else None
        r = request(self.run, kind, work, svc.sock_dir, inputs, self.p.step_s, self.p.file_cap, deadline=dl,
                    ready_s=self.p.ready_s, work_cap=self.p.work_cap)
        self.alive(svc)
        gone = remove_tree(work) & remove_tree(work + ".stage")
        after = fs_free(root)
        if r.status == "ok" and not gone:
            r.status = "the prover left files in /work that the runner cannot remove"
        elif r.status == "ok" and before and after and (before[0] - after[0] > FS_SLACK or before[1] - after[1] > 64):
            r.status = (f"the prover left the filesystem fuller ({before[0] - after[0]} bytes, "
                        f"{before[1] - after[1]} inodes after cleanup)")
        if r.status != "ok":
            if dl is not None and time.monotonic() >= dl - 1e-3 and r.status in ("timeout", "no ready line"):
                return None
            raise Fail(f"step {tag}: {r.status}" + self.diag(svc, r.log))
        return r

    def stream_run(self):
        """The stream (AGENTS.md §6): `M` steps, a fresh process each, `PROVER first` then `PROVER
        step`, under one service lifetime; every output checked with `acc` against the runner's own
        statement (one timed check), the statement canaries of `π_1`, `π_2`, `π_M`, interleaved
        calibration samples, the re-timing, all within `stream_s`. A stream that reaches the cap is
        scored over its completed, checked steps and flagged `truncated`."""
        p, name = self.p, "stream"
        M = p.M
        p.check_lengths()
        ns = list(p.lengths)                  # the season's fixed, published lengths
        starts = draws.starts(M + 1)          # fresh CSPRNG draws per evaluation
        self.log(f"[{name}] computing {M + 1} leaf digests (sum of lengths {sum(ns)})")
        ld = digest.leaf_digests(starts, ns, self.service_bin)  # all before the first request
        stmts = [digest.node_stmt(ld[0], ld[1])]
        for i in range(2, M + 1):
            stmts.append(digest.node_stmt(stmts[-1], ld[i]))
        self.req_root = request_root()
        svc = self.service(name)
        rec = {"vk": svc.vk.hex(), "service": {k: v for k, v in svc.info.items() if k != "simd"}, "M_drawn": M, "lengths": ns,
               "starts": [s.hex() for s in starts], "leaf_digests": [d.hex() for d in ld],
               "statements": [c.hex() for c in stmts], "steps": [], "truncated": False,
               "request_dir": "tmpfs (/dev/shm)" if self.req_root else "the work directory"}
        steps, pending = rec["steps"], []

        def flush(after_cap=False):
            """Check the pending outputs in one badge run, within 30 s of the cap; after truncation
            within 30 s. A batch the cap stops (a timeout past it; a crash is the entry's
            failure) leaves its steps unscored and truncates the stream."""
            if pending:
                items = [it for _, it in pending]
                try:
                    res = self.check(items, f"{name} outputs", timeout=30 if after_cap else None)
                except Fail as e:
                    if e.kind != "timeout":           # a timeout is past the cap (the only bound)
                        raise
                    del steps[len(steps) - len(pending):]       # the cap stopped it: unchecked, unscored
                    pending.clear()
                    rec["truncated"] = True
                    raise _Cap()
                for (k, _), ns in zip(pending, res):
                    steps[k]["V_ns"] = ns
                pending.clear()

        def inputs(i):
            if i == 1:
                return "first", {"chainA.json": chain_json(ns[0], starts[0]), "chainB.json": chain_json(ns[1], starts[1])}
            return "step", {"prev.stmt": (stmts[i - 2].hex() + "\n").encode(),
                            "prev.bin": open(os.path.join(self.store, steps[i - 2]["file"]), "rb").read(),
                            "chain.json": chain_json(ns[i], starts[i])}
        def run_steps():
            for i in range(1, M + 1):
                if (i - 1) % p.calib_every == 0:
                    flush()
                    self.sample(i)
                if self.left() <= 0:
                    rec["truncated"] = True
                    break
                kind, ins = inputs(i)
                r = self.one(svc, f"step{i}", kind, ins)
                if r is None:
                    rec["truncated"] = True
                    break
                rel = self.keep(f"{name}/step{i}.bin", r.proof)
                steps.append(step_record(i, ns[0] + ns[1] if i == 1 else ns[i], r, rel))
                pending.append((len(steps) - 1, (svc.vk, stmts[i - 1], rel, f"{name} step {i}")))
                self.log(f"[{name}] step {i}: n={steps[-1]['n']} P={r.seconds:.4f} s file={len(r.proof)} B")
                if len(pending) >= p.check_every:
                    flush()
            # the completed steps' checks; after the cap, one badge run of at most 30 s (a batch the
            # cap stops leaves its steps unscored)
            flush(after_cap=rec["truncated"])
        self.deadline = (time.monotonic() + p.stream_s, f"the stream's cap stream_s = {p.stream_s} s was reached")
        try:
            try:
                run_steps()
            except _Cap:
                pass
            if rec["truncated"]:
                self.log(f"[{name}] truncated after {len(steps)} checked steps")
            if not steps:
                raise Fail(f"{name}: no step completed within stream_s = {p.stream_s} s")
            # a closing sample when the last is old, only with 30 s of the cap to spare; none after
            # truncation
            if (not rec["truncated"] and self.left() > 30
                    and self.samples[-1]["before_step"] <= len(steps) + 1 - max(1, p.calib_every // 2)):
                self.sample(len(steps) + 1)
            last = len(steps)

            def target(k):
                return (steps[k - 1]["file"], stmts[k - 1],
                        [("next-leaf", ld[k + 1] if k < M else None), ("first-child", ld[0] if k == 1 else stmts[k - 2])])
            if not rec["truncated"]:      # no canaries after truncation; a cap reached
                try:                      # during them truncates the stream
                    rec["canaries"] = self.canary_check(svc.vk, [target(k) for k in sorted({1, min(2, last), last})], name)
                except Fail as e:
                    if e.kind != "timeout":
                        raise
                    rec["truncated"], rec["canaries"] = True, None
            if not rec["truncated"]:
                rec["retime"] = self.retime(svc, steps, stmts, inputs)
            self.alive(svc)
        except Fail as e:
            e.rec = rec        # a failed run keeps its measurements in the result
            raise
        finally:
            self.deadline = None
            self.stop(svc, rec)
            if self.req_root:
                shutil.rmtree(self.req_root, ignore_errors=True)
        rec["M"] = len(steps)
        rec["last_file"], rec["last_stmt"] = steps[-1]["file"], stmts[len(steps) - 1].hex()
        rec["calibration"] = self.calibration()
        for s in steps:
            s["calib_sample"] = max((k for k, c in enumerate(self.samples) if c["before_step"] <= s["index"]), default=0)
        return rec

    # -- re-timing -----------------------------------------------------------------------------------
    def retime(self, svc, steps, stmts, inputs):
        """The re-timing (AGENTS.md §6): fit `P ≈ a·n + b` by trimmed least squares; every step with
        `P_i > retime_factor · (a·n_i + b)`, largest ratio first, at most `retime_frac` of the steps,
        is run once more in a fresh process on the same inputs (the same `prev.bin`); its output must
        be accepted. The faster run is **kept**: its `P_i`, `V_i` and `|π_i|` are scored; the first
        output stays the child of step `i + 1`. If `stream_s` is reached the first times stand."""
        a, b, _ = fit([s["n"] for s in steps], [s["P_s"] for s in steps])
        over = sorted(((s["P_s"] / max(1e-9, a * s["n"] + b), k) for k, s in enumerate(steps)), reverse=True)
        over = [(q, k) for q, k in over if q > self.p.retime_factor]
        limit = int(self.p.retime_frac * len(steps))
        out = {"fit": {"a_s_per_permutation": a, "b_s": b}, "candidates": len(over), "limit": limit, "rerun": []}
        keys = ("P_s", "V_ns", "pi_bytes", "file_bytes", "file", "startup_s", "kill_s", "mem_peak")
        for q, k in over[:limit]:
            if self.left() <= 0:
                out["stopped_by_cap"] = True
                break
            s, i = steps[k], steps[k]["index"]
            kind, ins = inputs(i)
            r = self.one(svc, f"retime{i}", kind, ins)
            if r is None:
                out["stopped_by_cap"] = True
                break
            rel = self.keep(f"stream/step{i}.retime.bin", r.proof)
            try:
                (ns,) = self.check([(svc.vk, stmts[i - 1], rel, f"stream step {i} (re-timed)")], "stream re-timing")
            except Fail as e:
                if e.kind != "timeout":
                    raise
                out["stopped_by_cap"] = True              # the first times stand
                break
            again = step_record(i, s["n"], r, rel)
            again["V_ns"] = ns
            first = {key: s[key] for key in keys}
            kept = 2 if again["P_s"] < s["P_s"] else 1
            if kept == 2:
                s.update({key: again[key] for key in keys if key != "file"}, scored_file=rel)
            s["retime"] = {"ratio": q, "first": first, "second": {key: again[key] for key in keys}, "kept": kept,
                           "calib_sample": len(self.samples) - 1}      # the last sample
            out["rerun"].append(i)
        return out


FS_SLACK = 1 << 20        # bytes the request directories' filesystem may lose to other processes


def fs_free(path):
    """(free bytes, free inodes) of the filesystem of `path`, or None."""
    try:
        st = os.statvfs(path)
        return st.f_bavail * st.f_frsize, st.f_favail
    except OSError:
        return None


def step_record(i, n_i, r, rel):
    """The per-step record (the score adds its derived fields)."""
    return {"index": i, "n": n_i, "P_s": r.seconds, "startup_s": r.startup_s, "kill_s": r.kill_s,
            "mem_peak": r.mem_peak, "file": rel, "file_bytes": len(r.proof), "pi_bytes": pi_size(r.proof),
            "ended_by": r.ended, "work_bytes": r.work_bytes, "t_stop_ns": r.t_stop_ns}


def pi_size(file_bytes):
    """`|π|` of a signed-proof file: its first `u64` (harness/FORMAT.md)."""
    return int.from_bytes(file_bytes[:8], "little") if len(file_bytes) >= 8 else len(file_bytes)


def fit(ns, ps):
    """The robust per-step fit: least squares of `P` on `n` over the
    steps whose residual is among the lowest 80% (at least 3), refitted until that set is stable. The
    first set is ranked against the Theil–Sen line (median pairwise slope), so that the slow steps
    being trimmed cannot pull the first fit (with a least-squares start, two slow steps at small `n`
    could tilt it and get fast steps trimmed instead). Returns (a, b, (standard error of a, of b) on
    the final set, for a diagnostic 95% interval)."""
    m = len(ps)
    if m == 0:
        return 0.0, 0.0, (float("nan"), float("nan"))
    sl = [(ps[j] - ps[i]) / (ns[j] - ns[i]) for i in range(m) for j in range(i + 1, m) if ns[j] != ns[i]]
    a = statistics.median(sl) if sl else 0.0
    b = statistics.median(p - a * n for n, p in zip(ns, ps))
    se, idx = (float("nan"), float("nan")), None
    for _ in range(10):
        order = sorted(range(m), key=lambda i: ps[i] - (a * ns[i] + b))
        new = sorted(order[:max(3, int(0.8 * m))])
        if new == idx:
            break
        idx = new
        xs, ys = [ns[i] for i in idx], [ps[i] for i in idx]
        if len(xs) < 2:
            break
        mx, my = statistics.fmean(xs), statistics.fmean(ys)
        sxx = sum((x - mx) ** 2 for x in xs) or 1.0
        a = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
        b = my - a * mx
        if len(xs) > 2:
            s2 = sum((y - a * x - b) ** 2 for x, y in zip(xs, ys)) / (len(xs) - 2)
            se = (math.sqrt(s2 / sxx), math.sqrt(s2 * (1 / len(xs) + mx * mx / sxx)))
    return a, b, se


def score_parts(p, steps, v_ref_ns, d_P=0.0, f_P=1.0, d_V=0.0, d_pi=0):
    """`(P̄, V̄, V̄ₘ)` (AGENTS.md §7; `V̄ₘ` the mean check time in seconds), optionally at a perturbed
    point: every `P_i` times `f_P` minus `d_P` seconds, every `V_i` minus `d_V` seconds, every `|π_i|`
    minus `d_pi` bytes."""
    num = sum(s["n"] * (max(0.0, s["P_s"] * f_P - d_P) / s["n"]) ** 3 for s in steps)
    P = p.n_ref * (num / sum(s["n"] for s in steps)) ** (1 / 3)
    vs = [max(0.0, s["V_ns"] / 1e9 - d_V) for s in steps]
    xs = [v / (v_ref_ns / 1e9) + max(0, s["pi_bytes"] - d_pi) / p.s_ref for v, s in zip(vs, steps)]
    return P, p.kappa * statistics.fmean(xs), statistics.fmean(vs)


def product(P, V_mean_s, v_ref_ns):
    """The product track's score `S× = P̄ · g`, `g = 1 + (V̄ₘ / v_ref)²` (AGENTS.md §7): `(S×, g)`."""
    g = 1 + (V_mean_s / (v_ref_ns / 1e9)) ** 2
    return P * g, g


def score(p: Params, stream):
    """The two scores (AGENTS.md §7; seconds per `2^18`-permutation step, lower is better) from the
    one stream run, every step at its kept run:

        P̄  = n_ref · (Σ_i n_i (P_i/n_i)³ / Σ_i n_i)^(1/3)
        S  = P̄ + V̄,   V̄ = κ · (1/M) Σ_i x_i,   x_i = V_i / v_ref + |π_i| / s_ref,   κ = K · v0   (sum)
        S× = P̄ · g,   g = 1 + (V̄ₘ / v_ref)²,   V̄ₘ = (1/M) Σ_i V_i                              (product)

    with the published diagnostics (AGENTS.md §7): shares, `P̄` per octave, marginal values of both,
    the fit (never scored), the largest `x_i`, a batching indicator. `tracks` names each track's
    score field. Adds the derived per-step fields in place."""
    if not stream or not stream.get("steps"):
        return {}
    steps, cal = stream["steps"], stream["calibration"]
    v_ref = cal["v_ref_ns"]
    P, V, Vm = score_parts(p, steps, v_ref)
    S = P + V
    Sx, g = product(P, Vm, v_ref)
    out = {"S": S, "P_bar": P, "V_bar": V, "share_P": P / S, "share_V": V / S, "K": p.K, "kappa": p.kappa,
           "n_ref": p.n_ref, "s_ref": p.s_ref, "c_P": cal.get("c_P"), "T_triv_ns": cal["T_triv_ns"], "v_ref_ns": v_ref,
           "M": len(steps), "sum_n": sum(s["n"] for s in steps), "truncated": bool(stream.get("truncated")),
           "c_P_provisional": bool(cal.get("c_P_provisional")),
           "x_bar": V / p.kappa, "V_mean_s": Vm, "g": g, "S_product": Sx,
           "pi_mean_bytes": statistics.fmean(s["pi_bytes"] for s in steps),
           "tracks": {"sum": "S", "product": "S_product"}}
    tot_p3 = sum(s["n"] * (s["P_s"] / s["n"]) ** 3 for s in steps)
    for s in steps:
        xv, xp = s["V_ns"] / v_ref, s["pi_bytes"] / p.s_ref
        s.update(P_per_n=s["P_s"] / s["n"], x=xv + xp, x_verifier=xv, x_size=xp,
                 share_P3=s["n"] * (s["P_s"] / s["n"]) ** 3 / tot_p3 if tot_p3 else 0.0)
    tot_x = sum(s["x"] for s in steps)
    for s in steps:
        s["share_V"] = s["x"] / tot_x if tot_x else 0.0
    a, b, (sa, sb) = fit([s["n"] for s in steps], [s["P_s"] for s in steps])
    for s in steps:
        s["fit_P_s"] = a * s["n"] + b
        s["fit_ratio"] = s["P_s"] / max(1e-9, s["fit_P_s"])
    out["fit"] = {"a_s_per_permutation": a, "b_s": b, "a_ci95": [a - 1.96 * sa, a + 1.96 * sa],
                  "b_ci95": [b - 1.96 * sb, b + 1.96 * sb],
                  "estimator": "trimmed least squares (lowest 80% of residuals, from a Theil–Sen start, to a fixed point)",
                  "scored": False}
    out["P_bar_per_octave"] = {f"2^{lo}": score_parts(p, sub, v_ref)[0] for lo in range(17, 21)
                               if (sub := [s for s in steps if (1 << lo) <= s["n"] < (1 << (lo + 1))])}
    moves = {"chain_speed_1pct": {"f_P": 0.99}, "overhead_0.1s_per_step": {"d_P": 0.1},
             "verifier_10ms": {"d_V": 0.01}, "proof_100KB": {"d_pi": 100_000}}
    out["marginal"] = {}
    for name, kw in moves.items():
        P2, V2, Vm2 = score_parts(p, steps, v_ref, **kw)
        out["marginal"][name] = (P2 + V2) / S - 1
        out["marginal"][f"product_{name}"] = product(P2, Vm2, v_ref)[0] / Sx - 1 if Sx else 0.0
    out["marginal"]["note"] = ("relative change of S (and, prefixed product_, of S_product) at the current point "
                               "(negative: better)")
    k = max(range(len(steps)), key=lambda j: steps[j]["x"])
    out["largest_x"] = {key: steps[k][key] for key in ("index", "x", "x_verifier", "x_size")}
    res = [s["P_s"] - s["fit_P_s"] for s in steps]
    mr = statistics.fmean(res)
    den = sum((r - mr) ** 2 for r in res)
    top = sorted((s["share_P3"] for s in steps), reverse=True)[:max(1, len(steps) // 10)]
    out["batching"] = {"top_decile_share_of_P3": sum(top),
                       "residual_lag1_autocorrelation":
                           sum((res[j] - mr) * (res[j + 1] - mr) for j in range(len(res) - 1)) / den if den else 0.0,
                       "note": "diagnostic only: work deferred to some steps shows as a large top-decile share"}
    return out

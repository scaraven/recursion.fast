"""The benchmark of one entry (TRUSTED RUNTIME): the IVC stream, its checks and calibration, the
timed passes and the score (the rules are in `AGENTS.md` §6, §7). One stream per evaluation, with
its own service lifetime: first the **service run** (the stream against the service, untimed, every
output checked before any secret is revealed), then `timed_runs` **timed passes** against the
service's replay mode, each output byte-identical to the service run's. Every request is a fresh
sandboxed process; every check and every calibration sample runs while no entry process is alive.
Every step the entry controls is capped by the season file, inside its job's time limit: a request
over its cap, and a benchmark that reaches `stream_s` (a slow or hung check included), fails with
the reason.
"""
import hashlib
import json
import os
import platform
import shutil
import stat
import statistics
import subprocess
import tempfile
import time
import tomllib
from dataclasses import dataclass

from . import digest, draws, signed
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
        """The season's stream shape (`[stream] M`, `n`): positive integers, `n ≤ leafCap = 2^22`
        (the contract's bound on a leaf), `timed_runs ≥ 1`; else a ValueError naming the defect."""
        bad = [k for k in ("M", "n") if type(getattr(self, k)) is not int or getattr(self, k) < 1]
        if bad:
            raise ValueError(f"[stream] {', '.join(bad)} not a positive integer")
        if self.n > LEAF_CAP:
            raise ValueError(f"[stream] n = {self.n} above the contract's leafCap = 2^22")
        if type(self.timed_runs) is not int or self.timed_runs < 1:
            raise ValueError(f"[stream] timed_runs = {self.timed_runs!r}, not a positive integer")


LEAF_CAP = digest.LEAF_CAP       # the contract's leafCap (`Relation.lean`)


def leaf_json(n, seed):
    return json.dumps({"n": n, "seed": seed.hex()}).encode()


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
        """`acc` on items (vk, stmt, store-relative path): [(accepted, V ns)], each `V` one
        measurement, the batch warmed with an untimed first check. A rejection is an answer, not a
        failure (the caller decides what it means); a badge run that times out or crashes is the
        entry's failure. The badge run ends within `timeout`, by default within 30 s of the stream's
        cap."""
        return self.verify(items, what, timeout if timeout is not None else self.capped(), warm=True)

    def v_capped(self, item, first_ns, what, timeout=None):
        """`V` of an accepted proof against `v_cap` (AGENTS.md §6): its one measurement `first_ns`;
        above the cap the check is timed twice more (one warmed badge run) and the minimum counts.
        Returns (V ns, every measurement, whether every check accepted it); a badge failure raises
        `Fail`."""
        runs, again = [first_ns], True
        if first_ns > self.p.v_cap_ms * 1e6:
            res = self.check([item, item], what, timeout)
            again = all(ok for ok, _ in res)
            runs += [ns for _, ns in res]
        return min(runs), runs, again

    def canary_check(self, vk, targets, what, timeout=None):
        """The statement canaries (AGENTS.md §6) of every target (key, store path, stmt, others): the
        accepted file, checked against another statement, must be rejected. Returns {key: [the names
        of the canaries `acc` accepted]} and the number of canaries checked; the caller decides. A
        badge failure raises `Fail`."""
        items = [(key, name, (vk, c, rel)) for key, rel, stmt, others in targets for name, c in canaries(stmt, others)]
        res = self.verify([it for _, _, it in items], f"{what} canaries", timeout if timeout is not None else self.capped())
        out = {key: [] for key, _, _, _ in targets}
        for (key, name, _), (ok, _) in zip(items, res):
            if ok:
                out[key].append(name)
        return out, len(items)

    def bounded(self, n):
        """The timeout of a badge run of `n` checks of intermediate outputs (plus its warm-up), whose
        failure costs only the track `every`: `INTERMEDIATE_SLACK_S` plus two `v_cap` per check, within
        the stream's cap. (The final output's checks are bounded by the stream's cap alone.)"""
        return min(self.capped(), INTERMEDIATE_SLACK_S + 2 * (n + 1) * self.p.v_cap_ms / 1e3)

    def warm_caches(self):
        """Before every request, untimed and with no entry process alive: read every regular file under
        the setup directory and the prover binary in full, so that every page of the files a request
        can see that outlive it is in the page cache and their cache state carries no information
        from one request to the next (a request could otherwise evict chosen pages and the next one
        probe which are cached). No link is followed; the setup directory is bounded by `setup_cap`
        and 2^20 entries (checked after `setup`, read-only since). Returns (seconds, bytes read)."""
        t0, total, buf = time.monotonic(), 0, bytearray(1 << 20)
        files = [os.path.join(self.run.bin_dir, "prover")]
        for root, _, names in os.walk(self.run.setup_dir, followlinks=False):
            files += [os.path.join(root, n) for n in names]
        for f in files:
            try:
                fd = os.open(f, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
            except OSError:
                continue
            try:
                if stat.S_ISREG(os.fstat(fd).st_mode):
                    while (k := os.readv(fd, [buf])) > 0:
                        total += k
            except OSError:
                pass
            finally:
                os.close(fd)
        return time.monotonic() - t0, total

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
            self.stop(svc, rec)
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
        Every failure is the entry's: the request's own errors (`request`), the stream's cap reached
        during it, a directory the runner cannot prepare or remove, and a filesystem left fuller
        than before the request (bytes or inodes of the request directories' filesystem, after
        cleanup). Before it the page cache of the setup and the binary is warmed (`warm_caches`); the
        request's directory and its staging directory are removed after it."""
        root = self.req_root or os.path.join(self.work, "requests")
        os.makedirs(root, exist_ok=True)
        before = fs_free(root)
        work = os.path.join(root, tag)
        try:
            fresh_dir(work)
            with open(os.path.join(work, "vk.hex"), "w") as f:
                f.write(svc.vk.hex() + "\n")
        except OSError as e:          # only a previous request can have left the filesystem so
            raise Fail(f"{tag}: the request directory cannot be prepared ({e.strerror or e}); "
                       "the filesystem is in the state the prover's requests left it")
        dl = self.deadline[0] if self.deadline else None
        warm_s, warm_bytes = self.warm_caches()
        r = request(self.run, kind, work, svc.sock_dir, inputs, self.p.step_s, self.p.file_cap, deadline=dl,
                    ready_s=self.p.ready_s, work_cap=self.p.work_cap)
        r.warm_s, r.warm_bytes = warm_s, warm_bytes
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
                raise Fail(f"{tag}: {self.deadline[1]} ({r.status})" + self.diag(svc, r.log))
            raise Fail(f"{tag}: {r.status}" + self.diag(svc, r.log))
        return r

    def inputs(self, i, seeds, stmts, prev, key=None):
        """Step `i`'s request: (`first` or `step`, name → bytes). Every step gets its leaf,
        `leaf.json` (`n` and the step's fresh seed `s_i`); a step `i ≥ 2` also `prev.stmt` (`c_{i-1}`)
        and `prev.bin` (`prev`, the service run's output of step `i - 1`); a timed request also
        `oracle.key` (the service's PRF key `k`, 64 lowercase hex characters and a newline). All are
        staged and appear in /work together when the clock runs."""
        ins = {} if i == 1 else {"prev.stmt": (stmts[i - 2].hex() + "\n").encode(), "prev.bin": prev}
        ins["leaf.json"] = leaf_json(self.p.n, seeds[i - 1])
        if key is not None:
            ins["oracle.key"] = (key + "\n").encode()
        return ("first" if i == 1 else "step"), ins

    def stored(self, step):
        return open(os.path.join(self.store, step["file"]), "rb").read()

    def stream_run(self):
        """The stream (AGENTS.md §6) under one service lifetime: the service run (`service_run`),
        then the timed passes (`timed`), all within `stream_s`, which is the entry's REJECT if
        reached. `M` steps, a fresh process each, `PROVER first` then `PROVER step`; step `i` proves
        `c_i` from one fresh leaf of `n` hashes (`rfh.digest.stream_statements`)."""
        p, name = self.p, "stream"
        p.check_shape()
        M = p.M
        seeds = draws.starts(M)               # fresh CSPRNG draws per evaluation, one per step
        self.log(f"[{name}] computing {M} leaf digests (n = {p.n} hashes each)")
        ld = digest.leaf_digests(seeds, p.n, self.service_bin)  # all before the first request
        stmts, first = digest.stream_statements(ld)
        self.req_root = request_root()
        svc = self.service(name)
        rec = {"vk": svc.vk.hex(), "service": {k: v for k, v in svc.info.items() if k != "simd"}, "shape": p.shape(),
               "seeds": [s.hex() for s in seeds], "leaf_digests": [d.hex() for d in ld],
               "statements": [c.hex() for c in stmts], "steps": [],
               "truncated": False, "timed_runs": p.timed_runs,
               "request_dir": "tmpfs (/dev/shm)" if self.req_root else "the work directory"}
        self.deadline = (time.monotonic() + p.stream_s, f"the stream's cap stream_s = {p.stream_s} s was reached")
        try:
            self.service_run(svc, rec, seeds, stmts, first)
            self.timed(svc, rec, seeds, stmts)
            self.alive(svc)
        except Fail as e:
            e.rec = rec        # a failed run keeps its measurements in the result
            raise
        finally:
            self.deadline = None
            self.stop(svc, rec)
            if self.req_root:
                shutil.rmtree(self.req_root, ignore_errors=True)
        try:
            self.audit_replays(rec)
        except Fail as e:
            e.rec = rec
            raise
        rec["M"] = len(rec["steps"])
        rec["last_file"], rec["last_stmt"] = rec["steps"][-1]["file"], stmts[-1].hex()
        rec["calibration"] = self.calibration()
        return rec

    def service_run(self, svc, rec, seeds, stmts, first):
        """The service run (AGENTS.md §6), untimed: the stream against the service, every output
        kept. Its times are recorded (`P_service_s`), never scored. Every output's size is at most
        `pi_cap`: its `|π|` if it parses as a signed proof that `acc` accepts, else its file size
        (`|π|` checked as it arrives, the file size of a rejected one after its check: a rejected
        file's trace is no place to keep state uncounted); a breach is the entry's REJECT.

        The intermediate outputs are checked with `acc` against the runner's statements in batches
        between steps (one warmed badge run each, one `V` measurement per output, each run bounded by
        `bounded`). Then, with no entry process alive, the **final** output on its own: it must be
        accepted against `c_M`, with `|π_M| ≤ final_pi_cap`, `V_M ≤ v_cap` (timed twice more above
        it, the minimum) and its statement canaries (`stmt-bit`, `first-child`) rejected; any breach,
        and any failure of its checks, is the entry's REJECT. Last the track `every`: re-timing of
        intermediate `V_i` above the cap and the canaries of outputs 1 and 2, skipped once the track
        is lost. A breach of the track's conditions, or a failed (crashed or timed-out) check of an
        intermediate output or of those canaries, is recorded per step and only excludes the entry
        from that track (`every_reasons`)."""
        p, steps, pending, M = self.p, rec["steps"], [], self.p.M
        v_cap = p.v_cap_ms * 1e6

        def rejected_size(s):
            if s["signed_proof"]:             # a rejected output is sized by its file
                s["pi_bytes"], s["signed_proof"] = s["file_bytes"], False
            if s["pi_bytes"] > p.pi_cap:
                raise Fail(f"service run, step {s['index']}: the output, rejected by acc, has {s['pi_bytes']} bytes, "
                           f"above pi_cap = {p.pi_cap}")

        def flush():
            """Check the pending intermediate outputs; a failed badge run costs the track `every`."""
            if not pending:
                return
            items = [it for _, it in pending]
            try:
                res = self.check(items, "the service run's intermediate outputs", self.bounded(len(items)))
            except Fail as e:
                for k, _ in pending:
                    steps[k]["check_error"] = printable(str(e), 300)
                pending.clear()
                return
            for (k, _), (ok, ns) in zip(pending, res):
                steps[k]["accepted"], steps[k]["V_ns"] = ok, ns
                if not ok:
                    rejected_size(steps[k])
            pending.clear()
        for i in range(1, M + 1):
            if (i - 1) % p.calib_every == 0:
                flush()
                self.sample(f"service run, step {i}")
            if self.left() <= 0:
                raise Fail(f"service run, step {i}: {self.deadline[1]}")
            kind, ins = self.inputs(i, seeds, stmts, self.stored(steps[-1]) if steps else None)
            r = self.one(svc, f"service{i}", kind, ins)
            rel = self.keep(f"stream/step{i}.bin", r.proof)
            steps.append(step_record(i, p.n, r, rel))
            s = steps[-1]
            self.log(f"[service run] step {i}: n={s['n']} P={r.seconds:.4f} s file={s['file_bytes']} B "
                     f"|π|={s['pi_bytes'] if s['signed_proof'] else 'not a signed proof'}")
            if s["pi_bytes"] > p.pi_cap:
                raise Fail(f"service run, step {i}: the output's {'|π|' if s['signed_proof'] else 'file size'} is "
                           f"{s['pi_bytes']} bytes, above pi_cap = {p.pi_cap}")
            if i < M:
                pending.append((i - 1, (svc.vk, stmts[i - 1], rel)))
                if len(pending) >= p.check_every:
                    flush()
        flush()
        # the final output, on its own: every failure here is the entry's REJECT
        final, item = steps[-1], (svc.vk, stmts[M - 1], steps[-1]["file"])
        ((ok, ns),) = self.check([item], "service run: the final output")
        final["accepted"], final["V_ns"] = ok, ns
        if not ok:
            raise Fail(f"service run: the final output (step {M}) is rejected by acc against c_{M}"
                       + self.diag(svc, ""))
        if final["pi_bytes"] > p.final_pi_cap:
            raise Fail(f"service run: the final output (step {M}) has |π| = {final['pi_bytes']} bytes, above "
                       f"final_pi_cap = {p.final_pi_cap}")
        final["V_ns"], final["V_runs_ns"], again = self.v_capped(item, ns, "service run: the final output (V above "
                                                                       "v_cap, timed again)")
        if not again:
            raise Fail(f"service run: the final output (step {M}), accepted by acc, is rejected when checked again")
        if final["V_ns"] > v_cap:
            raise Fail(f"service run: the final output (step {M}) takes V = {final['V_ns'] / 1e6:.3f} ms (the minimum "
                       f"of {len(final['V_runs_ns'])} checks), above v_cap = {p.v_cap_ms:g} ms")
        bad, rec["canaries"] = self.canary_check(svc.vk, [(M, final["file"], stmts[M - 1], [("first-child", first[M - 1])])],
                                                 "service run: the final output")
        final["canaries_accepted"] = bad[M]
        if bad[M]:
            raise Fail(f"service run: the final output (step {M}): statement canaries accepted by acc (a proof "
                       f"accepted for another statement): {bad[M]}")
        # the track `every`: never the run's failure; skipped once lost
        lost = lambda: bool(every_reasons(p, rec, canaries=False))  # noqa: E731
        inter = steps[:-1]
        for s in inter if all(s.get("accepted") and not s.get("check_error") for s in inter) else []:
            if s["V_ns"] > v_cap:
                k = s["index"]
                try:
                    s["V_ns"], s["V_runs_ns"], again = self.v_capped(
                        (svc.vk, stmts[k - 1], s["file"]), s["V_ns"], f"service run, step {k} (V above v_cap, timed again)",
                        self.bounded(2))
                    if not again:
                        s["recheck_rejected"] = True
                except Fail as e:
                    s["check_error"] = printable(str(e), 300)
                if s.get("check_error") or s.get("recheck_rejected") or s["V_ns"] > v_cap:
                    break                     # `every` is lost: no more re-timing
        ks = [k for k in (1, 2) if k < M]
        if ks and not lost():
            try:
                bad, n = self.canary_check(svc.vk, [(k, steps[k - 1]["file"], stmts[k - 1], [("first-child", first[k - 1])])
                                                    for k in ks], "service run: outputs 1 and 2", self.bounded(2 * len(ks)))
                rec["canaries"] += n
                for k in ks:
                    steps[k - 1]["canaries_accepted"] = bad[k]
            except Fail as e:
                for k in ks:
                    steps[k - 1]["canary_error"] = printable(str(e), 300)
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
            raise Fail(f"the service reported no replay statistics ({sorted(st)})")
        if st["mismatches"]:
            raise Fail(f"a SIGN in a timed pass differed from the service run's ({st['mismatches']} MISMATCH refusals"
                       + (f"; {printable(rec['service_mismatches'][0], 300)}" if rec.get("service_mismatches") else "") + ")")
        if st["replays"] != want * st["signatures"]:
            raise Fail(f"the timed passes made {st['replays']} signatures, not timed_runs · signatures = {want} · "
                       f"{st['signatures']}: a timed pass must make exactly the service run's SIGN requests")

    def purge_requests(self):
        """Before the timed passes nothing of the service run's requests is left where a timed
        request could reach it: each request's directory and its staging directory were removed after
        it (`one`); here the request root must be empty (what is left is removed, or the entry fails).
        The service run's outputs live only in the runner's store, which no request sees."""
        root = self.req_root or os.path.join(self.work, "requests")
        if not os.path.isdir(root):
            return
        for n in os.listdir(root):
            remove_tree(os.path.join(root, n))
        left = os.listdir(root)
        if left:
            raise Fail(f"the service run left {len(left)} entries in the request directory that the runner cannot remove")

    def timed(self, svc, rec, seeds, stmts):
        """The timed passes (AGENTS.md §6): `timed_runs` passes of steps `1 … M`, each a fresh
        sandbox as in the service run, after the service run's request directories are gone. Before
        each pass the service enters replay mode (`Service.replay`) and reveals its PRF key `k`; a
        timed request gets the same leaf, the runner's statement, the **service run's** output of
        step `i - 1` as `prev.bin`, and `oracle.key`. Each output must be byte-identical to the
        service run's output of that step, else the entry's REJECT naming the pass, the step and the
        first differing byte. `P_i` = the minimum of step `i`'s timed times."""
        p, steps = self.p, rec["steps"]
        self.purge_requests()
        for t in range(1, p.timed_runs + 1):
            self.sample(f"timed pass {t}")
            try:
                key = svc.replay()
            except ServiceError as e:
                raise Fail(f"timed pass {t}: the service did not enter replay mode ({e})")
            for i in range(1, p.M + 1):
                if self.left() <= 0:
                    raise Fail(f"timed pass {t}, step {i}: {self.deadline[1]}")
                ref = self.stored(steps[i - 1])
                kind, ins = self.inputs(i, seeds, stmts, self.stored(steps[i - 2]) if i > 1 else None, key)
                r = self.one(svc, f"timed{t}-step{i}", kind, ins)
                if r.proof != ref:
                    rel = self.keep(f"stream/timed{t}-step{i}.bin", r.proof)
                    off = next((k for k, (x, y) in enumerate(zip(r.proof, ref)) if x != y), min(len(r.proof), len(ref)))
                    raise Fail(f"timed pass {t}, step {i}: the output differs from the service run's output of the "
                               f"step, first at byte offset {off} ({len(r.proof)} bytes, the service run's {len(ref)}; "
                               f"kept as {rel}): a prover's output must be a function of its inputs, its setup and the "
                               "oracle answers")
                s = steps[i - 1]
                s.setdefault("P_timed_s", []).append(r.seconds)
                s.setdefault("timed", []).append({"startup_s": r.startup_s, "kill_s": r.kill_s, "mem_peak": r.mem_peak,
                                                  "work_bytes": r.work_bytes, "ended_by": r.ended, "warm_s": r.warm_s})
                self.log(f"[timed pass {t}] step {i}: P={r.seconds:.4f} s (identical output)")
            mism = svc.mismatches()
            if mism:
                raise Fail(f"timed pass {t}: a SIGN in a timed pass differed from the service run's "
                           f"({len(mism)} refused; the first: {printable(mism[0], 300)}): a timed pass must make exactly "
                           "the service run's SIGN requests, in its order")
        if self.left() > 30:              # a closing sample, only with 30 s of the cap to spare
            self.sample("closing")
        for s in steps:
            s["P_s"] = min(s["P_timed_s"])


FS_SLACK = 1 << 20        # bytes the request directories' filesystem may lose to other processes
INTERMEDIATE_SLACK_S = 60  # seconds a badge run of intermediate checks may take beyond 2 v_cap per check


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
    """The per-step record of the service run (the timed passes add `P_timed_s` and `P_s`, the
    checks `accepted`, `V_ns`, the canaries, the score its derived fields)."""
    size, ok = output_size(r.proof)
    return {"index": i, "n": n_i, "P_service_s": r.seconds, "startup_s": r.startup_s, "kill_s": r.kill_s,
            "mem_peak": r.mem_peak, "file": rel, "file_bytes": len(r.proof), "pi_bytes": size, "signed_proof": ok,
            "ended_by": r.ended, "work_bytes": r.work_bytes, "t_stop_ns": r.t_stop_ns,
            "warm_s": getattr(r, "warm_s", None), "warm_bytes": getattr(r, "warm_bytes", None)}


def every_reasons(p, stream, canaries=True):
    """Why the stream is not eligible for the track `every` (AGENTS.md §7), [] if it is: every
    output checked and accepted by `acc` against its statement (again when timed again), with
    `|π_i| ≤ pi_cap` and `V_i ≤ v_cap` (the minimum of its checks), and the statement canaries of
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
            out.append(f"output {i}: rejected by acc when timed again")
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


def score(p: Params, stream):
    """The score (AGENTS.md §7; seconds, lower is better), one number for both tracks:

        S        = P_total · 2^(|π_M| / size_ref)
        P_total  = Σ_i P_i,   P_i = the least of step i's timed times

    `tracks` names the score field of each track the run is in: always `final` (a run that fails a
    `final` condition is REJECTed), `every` too when `every_reasons` is empty, else
    `tracks_reason` says why not. Published diagnostics: the untimed service run's total, each
    step's share of `P_total`. Adds the derived per-step fields in place."""
    if not stream or not stream.get("steps"):
        return {}
    steps, cal = stream["steps"], stream.get("calibration") or {}
    P = sum(s["P_s"] for s in steps)
    pi_M = steps[-1]["pi_bytes"]
    f = 2 ** (pi_M / p.size_ref)
    why = every_reasons(p, stream)
    out = {"S": P * f, "P_total_s": P, "size_factor": f, "final_pi_bytes": pi_M,
           "tracks": {"final": "S", **({} if why else {"every": "S"})}}
    if why:
        out["tracks_reason"] = {"every": "; ".join(why)[:2000]}
    out.update(size_ref=p.size_ref, M=len(steps), sum_n=sum(s["n"] for s in steps),
               c_P=cal.get("c_P"), c_P_provisional=bool(cal.get("c_P_provisional")))
    if all(isinstance(s.get("P_service_s"), (int, float)) for s in steps):
        out["P_total_service_run_s"] = sum(s["P_service_s"] for s in steps)      # published, never scored
    for s in steps:
        s["share_P"] = s["P_s"] / P if P else 0.0
    return out

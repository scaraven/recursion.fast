"""The benchmark of one entry (TRUSTED RUNTIME): the IVC stream, its checks and calibration, the
re-timing, the DoS column and the score (`docs/v4/BRIEF.md` V4-A11; the normative text is the
amendment's §2–§8 as amended by its §11). One stream per evaluation, with its own service lifetime;
every request is a fresh sandboxed process; every check and every calibration sample runs while no
entry process is alive. Every step the entry controls is capped by the season file, so an entry that
is slow or hangs fails with the reason, inside its job's time limit (V4-A9).
"""
import hashlib
import json
import math
import os
import platform
import random
import shutil
import statistics
import subprocess
import tempfile
import time
import tomllib
from dataclasses import dataclass

from . import digest, draws
from .checks import Badge, BadgeError, canaries, dos_inputs
from .prover import fresh_dir, request
from .sandbox import memcap, memcap_method
from .service import Service, ServiceError


class Fail(Exception):
    """The entry fails the benchmark (the message says why)."""


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
    M_min: int
    M_mean_extra: int
    M_cap: int
    n_lo: int
    n_hi: int
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
    calib_clamp: tuple
    triv_chains: int
    triv_n: int
    v_ref_ms: float
    service_calib_s: float
    dos_proofs: int
    dos_item_factor: float
    dos_total_s: float
    dos_item_cap: str
    file_cap: int
    verify_s: float
    setup_s: float
    setup_cap: int
    build_s: float
    mem_prover: str
    mem_service: str
    mem_badge: str

    @staticmethod
    def load(path):
        t = tomllib.load(open(path, "rb"))
        g = lambda sec, k: t[sec][k]  # noqa: E731 (a KeyError names the missing parameter)
        return Params(
            name=t["name"], K=float(g("score", "K")), kappa=float(g("score", "kappa")),
            n_ref=g("score", "n_ref"), s_ref=g("score", "s_ref"), R=float(g("score", "R")),
            M_min=g("stream", "M_min"), M_mean_extra=g("stream", "M_mean_extra"), M_cap=g("stream", "M_cap"),
            n_lo=g("stream", "n_lo"), n_hi=g("stream", "n_hi"), ready_s=g("stream", "ready_s"),
            step_s=g("stream", "step_s"), stream_s=g("stream", "stream_s"), check_every=g("stream", "check_every"),
            retime_factor=float(g("stream", "retime_factor")), retime_frac=float(g("stream", "retime_frac")),
            calib_every=g("calibration", "every"), calib_idle_s=float(g("calibration", "idle_s")),
            calib_rounds=g("calibration", "rounds"), calib_ref_ns=float(g("calibration", "ref_ns")),
            calib_clamp=tuple(g("calibration", "clamp")), triv_chains=g("calibration", "triv_chains"),
            triv_n=g("calibration", "triv_n"), v_ref_ms=float(t["calibration"].get("v_ref_ms", 0.0)),
            service_calib_s=g("calibration", "service_s"),
            dos_proofs=g("dos", "proofs"), dos_item_factor=float(g("dos", "item_factor")),
            dos_total_s=g("dos", "total_s"), dos_item_cap=g("dos", "item_cap"),
            file_cap=g("caps", "file_cap"), verify_s=g("caps", "verify_s"), setup_s=g("caps", "setup_s"),
            setup_cap=g("caps", "setup_cap"), build_s=g("caps", "build_s"),
            mem_prover=g("memory", "prover"), mem_service=g("memory", "service"), mem_badge=g("memory", "badge"))


def chain_json(n, start):
    return json.dumps({"n": n, "start": start.hex()}).encode()


def machine():
    model = next((l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo") if l.startswith("model name")), None)
    mem = next((int(l.split()[1]) for l in open("/proc/meminfo") if l.startswith("MemTotal")), None)
    flags = next((l.split(":", 1)[1].split() for l in open("/proc/cpuinfo") if l.startswith("flags")), [])
    return {"cpu_model": model, "nproc": os.cpu_count(), "mem_total_kb": mem, "kernel": platform.release(),
            "simd": [f for f in ("avx2", "avx512f", "sha_ni", "pclmulqdq", "vpclmulqdq", "gfni") if f in flags],
            "memcap": memcap_method(), "image_os": os.environ.get("ImageOS"),
            "image_version": os.environ.get("ImageVersion"), "runner_name": os.environ.get("RUNNER_NAME")}


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
    """Where request directories live (R-M1): a tmpfs (`/dev/shm`), whose pages a prover writes are
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
        self.badge = Badge(badge_dir, p.mem_badge, p.verify_s, os.path.join(work, "badge-scratch"))
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
        """What a failed run said (Q13): the prover's output tail and the service's refusals."""
        out = f"; prover output (tail): {output.strip()[-1200:]!r}" if output.strip() else ""
        ref = svc.refusals(5)
        return out + (f"; service refusals: {ref}" if ref else "")

    def stop(self, svc, rec):
        rec["service_refusals"] = svc.refusals()
        try:
            rec["service_stats"] = svc.stop()
        except ServiceError as e:
            raise Fail(f"the service failed during the run ({e}); the run is aborted (V4-A4)")

    def alive(self, svc):
        if svc.proc is None or svc.proc.poll() is not None:
            raise Fail("the service died during the run (V4-A4: a restart is a new key; the run is aborted)")

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

    def verify(self, items, what, warm=False, timeout=None):
        """The badge on (vk, stmt, store-relative path) items, `verify_s` per check and 30 s to start;
        a badge failure is the entry's."""
        t = timeout if timeout is not None else self.p.verify_s * (len(items) + warm) + 30
        try:
            return self.badge.verify(items, self.store, timeout=t, warm=warm)
        except BadgeError as e:
            raise Fail(f"{what}: {e}")

    def check(self, items, what, timeout=None):
        """`acc` on items (vk, stmt, store-relative path, label): every one must be accepted, and its
        time `V_i` is the best of two measurements (§11 m-8), each batch warmed with an untimed first
        check (RF-m3). Returns [(best ns, [both ns])]."""
        bare = [(vk, c, rel) for vk, c, rel, _ in items]
        runs = []
        for k in range(2):
            res = self.verify(bare, what, warm=True, timeout=timeout)
            for (_, _, _, label), (ok, _) in zip(items, res):
                if not ok:
                    raise Fail(f"{what}: {label} rejected by acc" + (" when measured again" if k else ""))
            runs.append([ns for _, ns in res])
        return [(min(a, b), [a, b]) for a, b in zip(*runs)]

    def canary_check(self, vk, targets, what):
        """The statement canaries (C15) of every target (store path, stmt, others): the accepted file,
        checked against another statement, must be rejected."""
        items = [(vk, c, rel, f"{rel} {name}") for rel, stmt, others in targets for name, c in canaries(stmt, others)]
        res = self.verify([(vk, c, rel) for vk, c, rel, _ in items], f"{what} canaries")
        bad = [label for (_, _, _, label), (ok, _) in zip(items, res) if ok]
        if bad:
            raise Fail(f"{what}: canaries accepted (a proof accepted for another statement): {bad[:5]}")
        return len(items)

    # -- calibration -------------------------------------------------------------------------------
    def calibrate(self):
        """Before the stream: the chain checker's instance (`triv_chains` chains of `triv_n` steps,
        `2^24` compressions in season 1, fresh starts, its root computed here) and the service's
        calls/s and compressions/s (V4-A5, C-m8; published, not in the score). `T_triv` and `c_P` are
        sampled during the stream (`sample`)."""
        inst = os.path.join(self.work, "instance")
        os.makedirs(inst, exist_ok=True)
        starts = draws.starts(self.p.triv_chains)
        root = digest.tree_root(digest.leaf_digests(starts, self.p.triv_n))
        with open(os.path.join(inst, "leaves.json"), "w") as f:
            json.dump({"n": self.p.triv_n, "starts": [s.hex() for s in starts]}, f)
        self.triv = (os.path.join(inst, "leaves.json"), root)
        cal = {"triv_compressions": self.p.triv_chains * self.p.triv_n, "pinned_core": self.badge.core}
        svc = self.service("calibration")
        rec = {"keygen_ms": float(svc.info.get("keygen_ms", "nan")), "simd": svc.info.get("simd")}
        try:
            # RF-m5: the CPUs this job may use, not the machine's count
            for threads in sorted({1, len(os.sched_getaffinity(0))}):
                out = subprocess.run([self.bench_bin, "oracle.sock", "throughput", str(threads), "1024", "64",
                                      str(self.p.service_calib_s)], cwd=svc.sock_dir, capture_output=True, text=True,
                                     timeout=60).stdout
                kv = dict(x.split("=") for x in out.split())
                # RB-m6: QUERY batches of 1,024 queries of 64 bytes; a keyed query of q bytes is
                # max(1, ceil(q / 64)) compressions after the cached key block
                per = max(1, -(-int(kv["size"]) // 64))
                rec[f"threads_{threads}"] = {"query_bytes": int(kv["size"]), "batch": int(kv["batch"]),
                                             "calls_per_s": float(kv["calls_per_s"]), "compressions_per_query": per,
                                             "compressions_per_s": float(kv["calls_per_s"]) * per,
                                             "us_per_request": float(kv["us_per_request"])}
        except Fail as e:
            e.rec = rec        # RF-m7: a failed run keeps its measurements in the result
            raise
        finally:
            self.stop(svc, rec)
        cal["service"] = rec
        return cal

    def sample(self, before_step):
        """One calibration sample (§5.4, §11 m-2), with no entry process alive: an idle gap, then the
        prover-shaped workload `calib` on the job's CPUs and the chain checker on one pinned core."""
        time.sleep(self.p.calib_idle_s)
        s = {"before_step": before_step}
        if self.calib_bin:
            out = subprocess.run([self.calib_bin, str(len(os.sched_getaffinity(0))), str(self.p.calib_rounds)],
                                 capture_output=True, text=True, timeout=120).stdout
            kv = dict(x.split("=", 1) for x in out.split()[1:] if "=" in x)
            s["calib_ns"], s["clmul"] = int(kv["ns"]), kv.get("clmul")
        s["triv_ns"] = self.badge.chaincheck(self.triv[0], self.triv[1])
        self.samples.append(s)
        return s

    def calibration(self):
        """`c_P` (median of the samples over the reference time, clamped) and `T_triv` (median of the
        chain checker's samples); `v_ref = T_triv / R`, or the season's fixed `v_ref_ms` (the smoke)."""
        cs = [s["calib_ns"] for s in self.samples if "calib_ns" in s]
        lo, hi = self.p.calib_clamp
        raw = statistics.median(cs) / self.p.calib_ref_ns if cs else 1.0
        triv = statistics.median(s["triv_ns"] for s in self.samples)
        v_ref = self.p.v_ref_ms * 1e6 if self.p.v_ref_ms else triv / self.p.R
        return {"c_P": min(hi, max(lo, raw)), "c_P_raw": raw, "calib_ref_ns": self.p.calib_ref_ns,
                "T_triv_ns": triv, "R": self.p.R, "v_ref_ns": v_ref,
                "v_ref_source": "fixed by the season file" if self.p.v_ref_ms else "measured: T_triv / R",
                "samples": self.samples, "software_clmul": any(s.get("clmul") == "soft" for s in self.samples)}

    # -- the stream ----------------------------------------------------------------------------------
    def one(self, svc, tag, kind, inputs):
        """One timed request, within `ready_s`, `step_s` and the stream's cap: its `Step` record, or
        None when the stream's cap stopped it; any other failure is the entry's."""
        root = self.req_root or os.path.join(self.work, "requests")
        work = fresh_dir(os.path.join(root, tag))
        with open(os.path.join(work, "vk.hex"), "w") as f:
            f.write(svc.vk.hex() + "\n")
        dl = self.deadline[0] if self.deadline else None
        r = request(self.run, kind, work, svc.sock_dir, inputs, self.p.step_s, self.p.file_cap, deadline=dl,
                    ready_s=self.p.ready_s)
        self.alive(svc)
        try:
            os.chmod(work, 0o700)                            # a prover may have made it unreadable
        except OSError:
            pass
        shutil.rmtree(work, ignore_errors=True)              # R-M1: cleanup errors are ignored
        shutil.rmtree(work + ".stage", ignore_errors=True)
        if r.status != "ok":
            if dl is not None and time.monotonic() >= dl - 1e-3 and r.status in ("timeout", "no ready line"):
                return None
            raise Fail(f"step {tag}: {r.status}" + self.diag(svc, r.log))
        return r

    def stream_run(self):
        """The stream (§2): `M` steps, a fresh process each, `PROVER first` then `PROVER step`, under
        one service lifetime; every output checked with `acc` against the runner's own statement
        (best of two), the statement canaries of `π_1`, `π_2`, `π_M`, interleaved calibration
        samples, the re-timing (§5.3), all within `stream_s`. A stream that reaches the cap is scored
        over its completed, checked steps and flagged `truncated` (§6)."""
        p, name = self.p, "stream"
        M = draws.draw_M(p.M_min, p.M_mean_extra, p.M_cap)
        ns = draws.lengths(M + 1, p.n_lo, p.n_hi)
        starts = draws.starts(M + 1)
        self.log(f"[{name}] computing {M + 1} leaf digests (sum of lengths {sum(ns)})")
        ld = digest.leaf_digests(starts, ns)          # §11 m-7: all before the first request
        stmts = [digest.node_stmt(ld[0], ld[1])]
        for i in range(2, M + 1):
            stmts.append(digest.node_stmt(stmts[-1], ld[i]))
        self.req_root = request_root()
        svc = self.service(name)
        rec = {"vk": svc.vk.hex(), "service": svc.info, "M_drawn": M, "lengths": ns,
               "starts": [s.hex() for s in starts], "leaf_digests": [d.hex() for d in ld],
               "statements": [c.hex() for c in stmts], "steps": [], "truncated": False,
               "request_dir": "tmpfs (/dev/shm)" if self.req_root else "the work directory"}
        steps, pending = rec["steps"], []

        def flush(timeout=None):
            if pending:
                if timeout is None and self.deadline is not None:
                    # a batch never runs far past the stream's cap (each of its two badge runs
                    # within the time left plus 30 s); a batch the cap stops ends the stream
                    timeout = min(p.verify_s * (len(pending) + 1) + 30, max(30.0, self.left() + 30))
                try:
                    res = self.check([it for _, it in pending], f"{name} outputs", timeout=timeout)
                except Fail as e:
                    if "rejected" in str(e) or self.deadline is None or self.left() > 0:
                        raise
                    del steps[len(steps) - len(pending):]       # the cap stopped it: unchecked, unscored
                    pending.clear()
                    rec["truncated"] = True
                    raise _Cap()
                for (k, _), (best, both) in zip(pending, res):
                    steps[k].update(V_ns=best, V_runs_ns=both)
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
            # the completed steps' checks; after the cap, 2 × 30 s at most (a batch the cap stops
            # leaves its steps unscored)
            flush(timeout=30 if rec["truncated"] else None)
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
            if self.samples[-1]["before_step"] <= len(steps) + 1 - max(1, p.calib_every // 2):
                self.sample(len(steps) + 1)                   # a closing sample when the last is old
            last = len(steps)

            def target(k):
                return (steps[k - 1]["file"], stmts[k - 1],
                        [("next-leaf", ld[k + 1] if k < M else None), ("first-child", ld[0] if k == 1 else stmts[k - 2])])
            rec["canaries"] = self.canary_check(svc.vk, [target(k) for k in sorted({1, min(2, last), last})], name)
            if not rec["truncated"]:
                rec["retime"] = self.retime(svc, steps, stmts, inputs)
            self.alive(svc)
        except Fail as e:
            e.rec = rec        # RF-m7: a failed run keeps its measurements in the result
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
        """§5.3 as amended (R-M2, §11 m-4): fit `P ≈ a·n + b` by trimmed least squares; every step with
        `P_i > retime_factor · (a·n_i + b)`, largest ratio first, at most `retime_frac` of the steps,
        is run once more in a fresh process on the same inputs (the same `prev.bin`); its output must
        be accepted. The faster run is **kept**: its `P_i`, `V_i` and `|π_i|` are scored; the first
        output stays the child of step `i + 1`. If `stream_s` is reached the first times stand."""
        a, b, _ = fit([s["n"] for s in steps], [s["P_s"] for s in steps])
        over = sorted(((s["P_s"] / max(1e-9, a * s["n"] + b), k) for k, s in enumerate(steps)), reverse=True)
        over = [(q, k) for q, k in over if q > self.p.retime_factor]
        limit = int(self.p.retime_frac * len(steps))
        out = {"fit": {"a_s_per_compression": a, "b_s": b}, "candidates": len(over), "limit": limit, "rerun": []}
        keys = ("P_s", "V_ns", "V_runs_ns", "pi_bytes", "file_bytes", "file", "startup_s", "kill_s", "mem_peak")
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
            (best, both), = self.check([(svc.vk, stmts[i - 1], rel, f"stream step {i} (re-timed)")], "stream re-timing")
            again = step_record(i, s["n"], r, rel)
            again.update(V_ns=best, V_runs_ns=both)
            first = {key: s[key] for key in keys}
            kept = 2 if again["P_s"] < s["P_s"] else 1
            if kept == 2:
                s.update({key: again[key] for key in keys if key != "file"}, scored_file=rel)
            s["retime"] = {"ratio": q, "first": first, "second": {key: again[key] for key in keys}, "kept": kept,
                           "calib_sample": len(self.samples) - 1}      # §11 m-4: the last sample
            out["rerun"].append(i)
        return out

    # -- the DoS column -------------------------------------------------------------------------------
    def dos(self, vk, stmt, rel, v_ref_ns):
        """The DoS column (RF-M1 (2), RF-m6, V4-A9; V4-A11: on the stream's last output `π_M`):
        `dos.proofs` random and mutated signed proofs of its statement, each checked (parse plus `acc`,
        the badge's own clock, §11 m-12) within the per-item cap (`dos.item_factor · v_ref`, or
        `verify_s` where the season file says so) and all within `dos.total_s`. A breach of either
        cap, or a crash of the checker, is the entry's failure, and the slow input is kept and named.
        An accepted input is recorded, not failed (V4-A9)."""
        data = open(os.path.join(self.store, rel), "rb").read()
        files = dos_inputs(data, self.p.dos_proofs, random.SystemRandom())
        items = [(vk, stmt, self.keep(f"dos/{k}.bin", b)) for k, b in enumerate(files)]
        item_cap = self.p.dos_item_factor * v_ref_ns if self.p.dos_item_cap == "v_ref" else self.p.verify_s * 1e9
        try:
            res = self.badge.verify(items, self.store, timeout=self.p.dos_total_s)
        except BadgeError as e:
            k = len(e.partial)
            where = f"; input {k} (store/{items[k][2]}) was being checked" if k < len(items) else ""
            if e.kind == "timeout":
                raise Fail(f"DoS column: not finished within {self.p.dos_total_s} s{where}")
            if e.kind != "slow":
                raise Fail(f"DoS column: the checker crashed{where} ({e})")
            res = e.partial                    # every answer is in; the per-item cap names the slow one
        slow = [(ns, k) for k, (_, ns) in enumerate(res) if ns > item_cap]
        if slow:
            ns, k = max(slow)
            raise Fail(f"DoS column: input {k} took {ns / 1e6:.1f} ms, above the per-item cap of "
                       f"{item_cap / 1e6:.1f} ms ({len(slow)} inputs over; kept as store/{items[k][2]})")
        acc = [k for k, (ok, _) in enumerate(res) if ok]
        worst = max(range(len(res)), key=lambda k: res[k][1])
        return {"target": rel, "proofs": len(items), "accepted": len(acc), "accepted_inputs": [items[k][2] for k in acc[:5]],
                "max_ns": res[worst][1], "max_input": items[worst][2], "item_cap_ns": item_cap,
                "total_s": self.p.dos_total_s, "over_v_ref": sum(1 for _, ns in res if ns > v_ref_ns)}


def step_record(i, n_i, r, rel):
    """The per-step record of §8 (the score adds its derived fields)."""
    return {"index": i, "n": n_i, "P_s": r.seconds, "startup_s": r.startup_s, "kill_s": r.kill_s,
            "mem_peak": r.mem_peak, "file": rel, "file_bytes": len(r.proof), "pi_bytes": pi_size(r.proof),
            "ended_by": r.ended}


def pi_size(file_bytes):
    """`|π|` of a signed-proof file: its first `u64` (harness/FORMAT.md)."""
    return int.from_bytes(file_bytes[:8], "little") if len(file_bytes) >= 8 else len(file_bytes)


def fit(ns, ps):
    """The robust per-step fit (§11 m-4; `sim2.py`'s `_fit_pred`): least squares of `P` on `n` over the
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


def score_parts(p, steps, c_P, v_ref_ns, d_P=0.0, f_P=1.0, d_V=0.0, d_pi=0):
    """`(P̄, V̄)` of §4 as amended (§11 simplification 1), optionally at a perturbed point: every `P_i`
    times `f_P` minus `d_P` seconds, every `V_i` minus `d_V` seconds, every `|π_i|` minus `d_pi` bytes."""
    num = sum(s["n"] * (max(0.0, s["P_s"] * f_P - d_P) / s["n"]) ** 3 for s in steps)
    P = (p.n_ref / c_P) * (num / sum(s["n"] for s in steps)) ** (1 / 3)
    xs = [max(0.0, s["V_ns"] / 1e9 - d_V) / (v_ref_ns / 1e9) + max(0, s["pi_bytes"] - d_pi) / p.s_ref for s in steps]
    return P, p.kappa * statistics.fmean(max(x, x ** 3) for x in xs)


def score(p: Params, stream):
    """`S = P̄ + V̄` (V4-A11 §4 with §11 simplification 1; seconds per `2^18`-compression step, lower
    is better) from the one stream run, every step at its kept run:

        P̄ = (n_ref / c_P) · (Σ_i n_i (P_i/n_i)³ / Σ_i n_i)^(1/3)
        V̄ = κ · (1/M) Σ_i max(x_i, x_i³),   x_i = V_i / v_ref + |π_i| / s_ref,   κ = K · v0

    with the published diagnostics of §8: shares, `P̄` per octave, marginal values, the fit (never
    scored), the largest `x_i`, a batching indicator. Adds the derived per-step fields in place."""
    if not stream or not stream.get("steps"):
        return {}
    steps, cal = stream["steps"], stream["calibration"]
    c_P, v_ref = cal["c_P"], cal["v_ref_ns"]
    P, V = score_parts(p, steps, c_P, v_ref)
    S = P + V
    out = {"S": S, "P_bar": P, "V_bar": V, "share_P": P / S, "share_V": V / S, "K": p.K, "kappa": p.kappa,
           "n_ref": p.n_ref, "s_ref": p.s_ref, "c_P": c_P, "T_triv_ns": cal["T_triv_ns"], "v_ref_ns": v_ref,
           "M": len(steps), "sum_n": sum(s["n"] for s in steps), "truncated": bool(stream.get("truncated"))}
    tot_p3 = sum(s["n"] * (s["P_s"] / s["n"]) ** 3 for s in steps)
    for s in steps:
        xv, xp = s["V_ns"] / v_ref, s["pi_bytes"] / p.s_ref
        x = xv + xp
        s.update(P_per_n=s["P_s"] / s["n"], x=x, x_verifier=xv, x_size=xp, g_x=max(x, x ** 3),
                 share_P3=s["n"] * (s["P_s"] / s["n"]) ** 3 / tot_p3 if tot_p3 else 0.0)
    tot_g = sum(s["g_x"] for s in steps)
    for s in steps:
        s["share_V"] = s["g_x"] / tot_g if tot_g else 0.0
    a, b, (sa, sb) = fit([s["n"] for s in steps], [s["P_s"] for s in steps])
    for s in steps:
        s["fit_P_s"] = a * s["n"] + b
        s["fit_ratio"] = s["P_s"] / max(1e-9, s["fit_P_s"])
    out["fit"] = {"a_s_per_compression": a, "b_s": b, "a_ci95": [a - 1.96 * sa, a + 1.96 * sa],
                  "b_ci95": [b - 1.96 * sb, b + 1.96 * sb],
                  "estimator": "trimmed least squares (lowest 80% of residuals, from a Theil–Sen start, to a fixed point)",
                  "scored": False}
    out["P_bar_per_octave"] = {f"2^{lo}": score_parts(p, sub, c_P, v_ref)[0] for lo in range(17, 21)
                               if (sub := [s for s in steps if (1 << lo) <= s["n"] < (1 << (lo + 1))])}
    rel = lambda P2, V2: (P2 + V2) / S - 1  # noqa: E731
    out["marginal"] = {"chain_speed_1pct": rel(*score_parts(p, steps, c_P, v_ref, f_P=0.99)),
                       "overhead_0.1s_per_step": rel(*score_parts(p, steps, c_P, v_ref, d_P=0.1)),
                       "verifier_10ms": rel(*score_parts(p, steps, c_P, v_ref, d_V=0.01)),
                       "proof_100KB": rel(*score_parts(p, steps, c_P, v_ref, d_pi=100_000)),
                       "note": "relative change of S at the current point (negative: better)"}
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

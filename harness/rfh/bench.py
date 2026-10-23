"""The benchmark of one entry (TRUSTED RUNTIME): the T run, the stream, extractor liveness, the
DoS column, the `T_V` calibration, the service calibration and the score (`docs/v4/BRIEF.md`
V4-10 … V4-12, `docs/DESIGN-cost-incentive-model.md` §3). One service lifetime per timed run; every
check of a run is made before its service exits; a service that dies aborts the run.
"""
import json
import os
import platform
import random
import shutil
import statistics
import subprocess
import time
import tomllib
from dataclasses import dataclass

from . import digest
from .checks import Badge, BadgeError, canaries, dos_inputs
from .files import OutputError, read_output
from .prover import fresh_dir, request
from .sandbox import memcap, memcap_method
from .service import Service, ServiceError


class Fail(Exception):
    """The entry fails the benchmark (the message says why)."""


@dataclass
class Params:
    name: str
    K: float
    R: float
    r: int
    n: int
    tree_repeats: int
    tree_s: float
    samples: int
    canaries_per_kind: int
    M: int
    n_f: int
    stream_repeats: int
    step_s: float
    stream_s: float
    check_every: int
    live_r: int
    live_n: int
    dos_proofs: int
    proof_cap: int
    file_cap: int
    verify_s: float
    setup_s: float
    build_s: float
    mem_prover: str
    mem_service: str
    mem_badge: str
    tv_enforce: bool
    checker_runs: int
    calib_s: float

    @staticmethod
    def load(path):
        t = tomllib.load(open(path, "rb"))
        g = lambda sec, k: t[sec][k]  # noqa: E731 (a KeyError names the missing parameter)
        return Params(
            name=t["name"], K=float(t["K"]), R=float(t["R"]),
            r=g("tree", "r"), n=g("tree", "n"), tree_repeats=g("tree", "repeats"), tree_s=g("tree", "tree_s"),
            samples=g("tree", "samples"), canaries_per_kind=g("tree", "canaries_per_kind"),
            M=g("stream", "M"), n_f=g("stream", "n_f"), stream_repeats=g("stream", "repeats"),
            step_s=g("stream", "step_s"), stream_s=g("stream", "stream_s"), check_every=g("stream", "check_every"),
            live_r=g("liveness", "r"), live_n=g("liveness", "n"), dos_proofs=g("dos", "proofs"),
            proof_cap=g("caps", "proof_cap"), file_cap=g("caps", "file_cap"), verify_s=g("caps", "verify_s"),
            setup_s=g("caps", "setup_s"), build_s=g("caps", "build_s"),
            mem_prover=g("memory", "prover"), mem_service=g("memory", "service"), mem_badge=g("memory", "badge"),
            tv_enforce=bool(g("tv", "enforce")), checker_runs=g("tv", "checker_runs"), calib_s=g("tv", "service_calibration_s"))


def leaves_json(starts, n):
    return json.dumps({"n": n, "starts": [s.hex() for s in starts]}).encode()


def tree_files(r):
    """(output name, level, index) of every proof a tree run writes: leaves, inner nodes, root."""
    out = [(f"proofs/L{i}.bin", 0, i) for i in range(1 << r)]
    out += [(f"proofs/N{l}_{j}.bin", l, j) for l in range(1, r) for j in range(1 << (r - l))]
    return out + [("root.bin", r, 0)]


def machine():
    model = next((l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo") if l.startswith("model name")), None)
    mem = next((int(l.split()[1]) for l in open("/proc/meminfo") if l.startswith("MemTotal")), None)
    flags = next((l.split(":", 1)[1].split() for l in open("/proc/cpuinfo") if l.startswith("flags")), [])
    return {"cpu_model": model, "nproc": os.cpu_count(), "mem_total_kb": mem, "kernel": platform.release(),
            "simd": [f for f in ("avx2", "avx512f", "sha_ni", "pclmulqdq", "vpclmulqdq", "gfni") if f in flags],
            "memcap": memcap_method(), "image_os": os.environ.get("ImageOS"),
            "image_version": os.environ.get("ImageVersion"), "runner_name": os.environ.get("RUNNER_NAME")}


class Bench:
    def __init__(self, p: Params, run, badge_dir, service_bin, bench_bin, work, log=print):
        self.p, self.run, self.service_bin, self.bench_bin = p, run, service_bin, bench_bin
        self.work, self.log = work, log
        self.store = os.path.join(work, "store")
        os.makedirs(self.store, exist_ok=True)
        self.badge = Badge(badge_dir, p.mem_badge, p.verify_s, os.path.join(work, "badge-scratch"))
        os.makedirs(self.badge.scratch, exist_ok=True)
        self.tv_cap_ns = None
        self.tv_seen = []                    # (what, ns) of every T_V-capped check

    # -- the service ---------------------------------------------------------------------------
    def service(self, name, log=None):
        svc = Service(self.service_bin, os.path.join(self.work, "svc", name), log=log,
                      wrap=memcap(self.p.mem_service, f"rf-svc-{name}-{os.getpid()}"),
                      stderr_path=os.path.join(self.work, "svc", f"{name}.stderr"))
        os.makedirs(os.path.join(self.work, "svc"), exist_ok=True)
        return svc.start()

    def stop(self, svc, rec):
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

    def check(self, items, what, tv=True):
        """Run `acc` on items (vk, stmt, store-relative path, label); every one must be accepted, and
        within the `T_V` cap if `tv`."""
        try:
            res = self.badge.verify([(vk, c, rel) for vk, c, rel, _ in items], self.store)
        except BadgeError as e:
            raise Fail(f"{what}: {e}")
        for (_, _, _, label), (ok, ns) in zip(items, res):
            if not ok:
                raise Fail(f"{what}: {label} rejected by acc")
            if tv:
                self.tv_seen.append((label, ns))
                if self.p.tv_enforce and self.tv_cap_ns is not None and ns > self.tv_cap_ns:
                    raise Fail(f"{what}: {label} took {ns / 1e6:.3f} ms, above T_V = {self.tv_cap_ns / 1e6:.3f} ms")
        return res

    def canary_check(self, vk, targets, prefix):
        """Every canary of every target (store path, stmt, sibling stmt) must be rejected."""
        items = []
        for rel, stmt, sib in targets:
            data = open(os.path.join(self.store, rel), "rb").read()
            for name, c, b in canaries(data, stmt, sib):
                items.append((vk, c, self.keep(f"{prefix}/canary/{rel.replace('/', '_')}.{name}", b), f"{rel} {name}"))
        try:
            res = self.badge.verify([(vk, c, r) for vk, c, r, _ in items], self.store)
        except BadgeError as e:
            raise Fail(f"canaries: {e}")
        bad = [label for (_, _, _, label), (ok, _) in zip(items, res) if ok]
        if bad:
            raise Fail(f"canaries accepted: {bad[:5]}")
        return len(items)

    # -- calibration -------------------------------------------------------------------------------
    def calibrate(self, inst_dir, starts, n, root):
        """`T_triv,best` (V4-12) from the chain checker on the tree's chains, pinned to one core, and the
        service's calls/s and compressions/s (V4-A5, C-m8)."""
        runs = [self.badge.chaincheck(os.path.join(inst_dir, "leaves.json"), root) for _ in range(self.p.checker_runs)]
        best = min(runs)
        self.tv_cap_ns = best / self.p.R
        cal = {"T_triv_best_ns": best, "chaincheck_ns": runs, "R": self.p.R, "T_V_cap_ns": self.tv_cap_ns,
               "pinned_core": self.badge.core, "chain_compressions": (1 << self.p.r) * n}
        svc = self.service("calibration")
        rec = {"keygen_ms": float(svc.info.get("keygen_ms", "nan")), "simd": svc.info.get("simd")}
        try:
            for threads in sorted({1, os.cpu_count() or 1}):
                out = subprocess.run([self.bench_bin, "oracle.sock", "throughput", str(threads), "1024", "64",
                                      str(self.p.calib_s)], cwd=svc.sock_dir, capture_output=True, text=True,
                                     timeout=600).stdout
                kv = dict(x.split("=") for x in out.split())
                # a 64-byte keyed query is one compression after the cached key block
                rec[f"threads_{threads}"] = {"calls_per_s": float(kv["calls_per_s"]),
                                             "compressions_per_s": float(kv["calls_per_s"]),
                                             "us_per_request_of_1024": float(kv["us_per_request"])}
        finally:
            self.stop(svc, rec)
        cal["service"] = rec
        return cal

    # -- the T run ---------------------------------------------------------------------------------
    def tree_repeat(self, k, starts, n, levels, r, name=None, liveness_log=None):
        name = name or f"tree{k}"
        svc = self.service(name, log=liveness_log)
        rec = {"repeat": k, "vk": svc.vk.hex(), "service": svc.info}
        try:
            work = fresh_dir(os.path.join(self.work, name, "work"))
            with open(os.path.join(work, "leaves.json"), "wb") as f:
                f.write(leaves_json(starts, n))
            with open(os.path.join(work, "vk.hex"), "w") as f:
                f.write(svc.vk.hex() + "\n")
            self.log(f"[{name}] prover tree: r={r} n={n}")
            status, dt, plog = self.run.tree(work, svc.sock_dir, self.p.tree_s)
            rec.update(status=status, seconds=dt, prover_log=plog[-2000:])
            self.log(f"[{name}] {status} in {dt:.3f} s")
            self.alive(svc)
            if status != "ok":
                raise Fail(f"{name}: prover tree {status}")
            stored = {}
            for rel, lvl, j in tree_files(r):
                try:
                    stored[(lvl, j)] = self.keep(f"{name}/{rel}", read_output(work, rel, self.p.file_cap))
                except OutputError as e:
                    raise Fail(f"{name}: {e}")
            stmt = lambda lvl, j: levels[lvl][j]  # noqa: E731
            vk = svc.vk
            items = [(vk, stmt(r, 0), stored[(r, 0)], f"{name} root")]
            inner = [key for key in stored if key[0] < r]
            rnd = random.Random(os.urandom(16))
            for key in rnd.sample(inner, min(self.p.samples, len(inner))):
                items.append((vk, stmt(*key), stored[key], f"{name} sample {key}"))
            res = self.check(items, f"{name} root and samples")
            rec["root_check_ns"] = res[0][1]
            rec["sample_check_ns"] = [ns for _, ns in res[1:]]
            sib = lambda lvl, j: stmt(lvl, j ^ 1) if lvl < r else None  # noqa: E731
            kinds = [[key for key in sorted(stored) if key[0] == 0], [key for key in sorted(stored) if key[0] > 0]]
            targets = [(stored[key], stmt(*key), sib(*key)) for kind in kinds for key in kind[:self.p.canaries_per_kind]]
            rec["canaries"] = self.canary_check(vk, targets, name)
            rec["root_file"] = stored[(r, 0)]
            rec["root_bytes"] = os.path.getsize(os.path.join(self.store, stored[(r, 0)]))
            if liveness_log is not None:
                ok, msg = self.badge.liveness(liveness_log, vk, stmt(r, 0), os.path.join(self.store, stored[(r, 0)]))
                rec["liveness"] = {"ok": ok, "output": msg}
                if not ok:
                    raise Fail(f"liveness: the extractor did not produce an accepted witness: {msg[-300:]}")
            self.alive(svc)
        finally:
            self.stop(svc, rec)
        return rec

    # -- the stream ----------------------------------------------------------------------------------
    def stream_repeat(self, k):
        p, name = self.p, f"stream{k}"
        starts = [os.urandom(32) for _ in range(p.M + 1)]
        self.log(f"[{name}] computing {p.M + 1} leaf digests at n_f = {p.n_f}")
        ds = digest.leaf_digests(starts, p.n_f)
        svc = self.service(name)
        rec = {"repeat": k, "vk": svc.vk.hex(), "service": svc.info, "leaf_s": [], "merge_s": []}
        pending, t_begin = [], time.monotonic()

        def flush():
            if pending:
                self.check(pending, f"{name} outputs")
                pending.clear()
        try:
            prev = None                        # (statement, store path) of the running proof
            for i in range(p.M + 1):
                if time.monotonic() - t_begin > p.stream_s:
                    raise Fail(f"{name}: stream_s exceeded at link {i}")
                ins = {"leaf.json": json.dumps({"n": p.n_f, "start": starts[i].hex()}).encode()}
                leaf = self.one(svc, name, f"leaf{i}", "leaf", ins)
                rec["leaf_s"].append(leaf[1])
                lrel = self.keep(f"{name}/leaf{i}.bin", leaf[0])
                pending.append((svc.vk, ds[i], lrel, f"{name} leaf {i}"))
                if i == 0:
                    prev = (ds[0], lrel)
                    flush()
                    rec["canaries"] = self.canary_check(svc.vk, [(lrel, ds[0], None)], name)
                    continue
                ins = {"child1.stmt": (prev[0].hex() + "\n").encode(),
                       "child1.bin": open(os.path.join(self.store, prev[1]), "rb").read(),
                       "child2.stmt": (ds[i].hex() + "\n").encode(), "child2.bin": leaf[0]}
                node = self.one(svc, name, f"node{i}", "node", ins)
                rec["merge_s"].append(node[1])
                c = digest.node_stmt(prev[0], ds[i])
                nrel = self.keep(f"{name}/node{i}.bin", node[0])
                pending.append((svc.vk, c, nrel, f"{name} node {i}"))
                prev = (c, nrel)
                if i == 1:
                    flush()
                    rec["canaries"] += self.canary_check(svc.vk, [(nrel, c, None)], name)
                if len(pending) >= p.check_every:
                    flush()
            flush()
            self.alive(svc)
        finally:
            self.stop(svc, rec)
        rec["t_leaf"] = sum(rec["leaf_s"]) / p.M
        rec["t_merge"] = sum(rec["merge_s"]) / p.M
        rec["t_link"] = rec["t_leaf"] + rec["t_merge"]
        ms = sorted(rec["merge_s"], reverse=True)
        rec["slowest_merge"] = ms[0]
        rec["mean_slowest_half_merge"] = statistics.fmean(ms[:max(1, len(ms) // 2)])
        self.log(f"[{name}] t_leaf={rec['t_leaf']:.4f} t_merge={rec['t_merge']:.4f} t_link={rec['t_link']:.4f}")
        return rec

    def one(self, svc, name, tag, kind, inputs):
        work = fresh_dir(os.path.join(self.work, name, tag))
        with open(os.path.join(work, "vk.hex"), "w") as f:
            f.write(svc.vk.hex() + "\n")
        status, dt, proof, err = request(self.run, kind, work, svc.sock_dir, inputs, self.p.step_s, self.p.file_cap)
        self.alive(svc)
        if status != "ok":
            raise Fail(f"{name} {tag}: {status}; stderr: {err[-300:]}")
        shutil.rmtree(work, ignore_errors=True)
        return proof, dt

    # -- the DoS column -------------------------------------------------------------------------------
    def dos(self, vk, root, root_rel):
        data = open(os.path.join(self.store, root_rel), "rb").read()
        files = dos_inputs(data, self.p.dos_proofs, random.Random(os.urandom(16)))
        items = [(vk, root, self.keep(f"dos/{k}.bin", b)) for k, b in enumerate(files)]
        try:
            res = self.badge.verify(items, self.store)
        except BadgeError as e:
            raise Fail(f"DoS column: {e}")
        acc = [k for k, (ok, _) in enumerate(res) if ok]
        if acc:
            raise Fail(f"DoS column: {len(acc)} random proofs accepted")
        return {"proofs": len(items), "max_ns": max(ns for _, ns in res), "median_ns": statistics.median(ns for _, ns in res)}


def score(p: Params, tree_recs, stream_recs):
    """`S = T_tree + K · t_link` (V4-10) and the published components (cost model §3.6)."""
    out = {"K": p.K}
    if tree_recs:
        out["T_tree"] = statistics.median(r["seconds"] for r in tree_recs)
        out["T_tree_repeats"] = [r["seconds"] for r in tree_recs]
    if stream_recs:
        for k in ("t_leaf", "t_merge", "t_link"):
            out[k] = statistics.median(r[k] for r in stream_recs)
            out[f"{k}_repeats"] = [r[k] for r in stream_recs]
        out["slowest_merge"] = max(r["slowest_merge"] for r in stream_recs)
    if tree_recs and stream_recs:
        out["S"] = out["T_tree"] + p.K * out["t_link"]
        out["o_est"] = out["t_link"] - out["T_tree"] * p.n_f / ((1 << p.r) * p.n)
    return out

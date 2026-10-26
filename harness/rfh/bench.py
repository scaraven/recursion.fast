"""The benchmark of one entry (TRUSTED RUNTIME): the T run, the stream, the DoS column, the `T_V`
calibration, the service calibration and the score (`docs/v4/BRIEF.md` V4-10 … V4-12, V4-A9,
`docs/DESIGN-cost-incentive-model.md` §3). One run of the tree and one of the stream, each with its
own service lifetime; every check of a run is made before its service exits; a service that dies
aborts the run. Every step the entry controls is capped by the season file, so an entry that is
slow or hangs fails with the reason, inside its job's time limit (V4-A9).
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
    tree_s: float
    M: int
    n_f: int
    step_s: float
    stream_s: float
    check_every: int
    canaries_per_kind: int
    dos_proofs: int
    dos_item_factor: float
    dos_total_s: float
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
            r=g("tree", "r"), n=g("tree", "n"), tree_s=g("tree", "tree_s"),
            M=g("stream", "M"), n_f=g("stream", "n_f"), step_s=g("stream", "step_s"),
            stream_s=g("stream", "stream_s"), check_every=g("stream", "check_every"),
            canaries_per_kind=g("canaries", "per_kind"), dos_proofs=g("dos", "proofs"),
            dos_item_factor=float(g("dos", "item_factor")), dos_total_s=g("dos", "total_s"),
            proof_cap=g("caps", "proof_cap"), file_cap=g("caps", "file_cap"), verify_s=g("caps", "verify_s"),
            setup_s=g("caps", "setup_s"), build_s=g("caps", "build_s"),
            mem_prover=g("memory", "prover"), mem_service=g("memory", "service"), mem_badge=g("memory", "badge"),
            tv_enforce=bool(g("tv", "enforce")), checker_runs=g("tv", "checker_runs"), calib_s=g("tv", "service_calibration_s"))


def leaves_json(starts, n):
    return json.dumps({"n": n, "starts": [s.hex() for s in starts]}).encode()


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
        self.tv_seen = []                    # (what, best ns) of every T_V-capped check
        self.tv_remeasured = 0               # checks measured again because a sample was above the cap
        self.deadline = None                 # (monotonic time, reason) of the running cap (`stream_s`)

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

    def left(self, what):
        """Seconds left before the running cap (None without one); reaching it is the entry's failure."""
        if self.deadline is None:
            return None
        t = self.deadline[0] - time.monotonic()
        if t <= 0:
            raise Fail(f"{what}: {self.deadline[1]}")
        return t

    def verify(self, items, what, warm=False):
        """The badge on (vk, stmt, store-relative path) items, `verify_s` per check and 30 s to start,
        within the running cap; a badge failure is the entry's."""
        timeout = self.p.verify_s * (len(items) + warm) + 30
        left = self.left(what)
        try:
            return self.badge.verify(items, self.store, timeout=timeout if left is None else min(timeout, left), warm=warm)
        except BadgeError as e:
            capped = left is not None and e.kind == "timeout" and left < timeout
            raise Fail(f"{what}: {e}" + (f" ({self.deadline[1]})" if capped else ""))

    def check(self, items, what, tv=True):
        """Run `acc` on items (vk, stmt, store-relative path, label); every one must be accepted, and
        within the `T_V` cap if `tv`. `T_V` is enforced with the cap's own statistic (RB-M1): the cap
        is the best of `checker_runs` chain-checker runs over `R`, so a check above the cap is
        measured again, up to `checker_runs` times in all, and only its best time is compared."""
        res = self.verify([(vk, c, rel) for vk, c, rel, _ in items], what, warm=tv)
        for (_, _, _, label), (ok, _) in zip(items, res):
            if not ok:
                raise Fail(f"{what}: {label} rejected by acc")
        if not tv:
            return res
        best = [ns for _, ns in res]
        enforce = self.p.tv_enforce and self.tv_cap_ns is not None
        for _ in range(self.p.checker_runs - 1):
            over = [k for k, ns in enumerate(best) if enforce and ns > self.tv_cap_ns]
            if not over:
                break
            again = self.verify([items[k][:3] for k in over], what, warm=True)
            for k, (ok, ns) in zip(over, again):
                if not ok:
                    raise Fail(f"{what}: {items[k][3]} rejected by acc when measured again")
                best[k] = min(best[k], ns)
            self.tv_remeasured += len(over)
        for (_, _, _, label), ns in zip(items, best):
            self.tv_seen.append((label, ns))
            if enforce and ns > self.tv_cap_ns:
                raise Fail(f"{what}: {label} took {ns / 1e6:.3f} ms (best of {self.p.checker_runs}), "
                           f"above T_V = {self.tv_cap_ns / 1e6:.3f} ms")
        return [(ok, ns) for (ok, _), ns in zip(res, best)]

    def canary_check(self, vk, targets, what):
        """The statement canaries (C15) of every target (store path, stmt, sibling stmt): the accepted
        file, checked against another statement, must be rejected."""
        items = [(vk, c, rel, f"{rel} {name}") for rel, stmt, sib in targets for name, c in canaries(stmt, sib)]
        res = self.verify([(vk, c, rel) for vk, c, rel, _ in items], f"{what} canaries")
        bad = [label for (_, _, _, label), (ok, _) in zip(items, res) if ok]
        if bad:
            raise Fail(f"{what}: canaries accepted (a proof accepted for another statement): {bad[:5]}")
        return len(items)

    # -- calibration -------------------------------------------------------------------------------
    def calibrate(self, inst_dir, n, root):
        """`T_triv,best` (V4-12) from the chain checker on the tree's chains, pinned to one core, and the
        service's calls/s and compressions/s (V4-A5, C-m8; published, not enforced)."""
        runs = [self.badge.chaincheck(os.path.join(inst_dir, "leaves.json"), root) for _ in range(self.p.checker_runs)]
        best = min(runs)
        self.tv_cap_ns = best / self.p.R
        cal = {"T_triv_best_ns": best, "chaincheck_ns": runs, "R": self.p.R, "T_V_cap_ns": self.tv_cap_ns,
               "pinned_core": self.badge.core, "chain_compressions": (1 << self.p.r) * n}
        svc = self.service("calibration")
        rec = {"keygen_ms": float(svc.info.get("keygen_ms", "nan")), "simd": svc.info.get("simd")}
        try:
            # RF-m5: the CPUs this job may use, not the machine's count
            for threads in sorted({1, len(os.sched_getaffinity(0))}):
                out = subprocess.run([self.bench_bin, "oracle.sock", "throughput", str(threads), "1024", "64",
                                      str(self.p.calib_s)], cwd=svc.sock_dir, capture_output=True, text=True,
                                     timeout=60).stdout
                kv = dict(x.split("=") for x in out.split())
                # RB-m6: the probe is QUERY batches of 1,024 queries of 64 bytes; a keyed query of q
                # bytes is max(1, ceil(q / 64)) compressions after the cached key block
                per = max(1, -(-int(kv["size"]) // 64))
                rec[f"threads_{threads}"] = {"query_bytes": int(kv["size"]), "batch": int(kv["batch"]),
                                             "calls_per_s": float(kv["calls_per_s"]),
                                             "compressions_per_query": per,
                                             "compressions_per_s": float(kv["calls_per_s"]) * per,
                                             "us_per_request": float(kv["us_per_request"])}
        except Fail as e:
            e.rec = rec        # RF-m7: a failed run keeps its measurements in the result
            raise
        finally:
            self.stop(svc, rec)
        cal["service"] = rec
        return cal

    # -- the T run ---------------------------------------------------------------------------------
    def tree_run(self, starts, n, root):
        """The T run: `prover tree` with a fresh service, timed. Only `root.bin` is read; it must be
        accepted within `T_V`, and its statement canary rejected. Inner proofs, if the prover writes
        them, are never read (V4-A9: the root's certificate covers its children, and the stream
        prices recursion)."""
        name = "tree"
        svc = self.service(name)
        rec = {"vk": svc.vk.hex(), "service": svc.info}
        try:
            work = fresh_dir(os.path.join(self.work, name, "work"))
            with open(os.path.join(work, "leaves.json"), "wb") as f:
                f.write(leaves_json(starts, n))
            with open(os.path.join(work, "vk.hex"), "w") as f:
                f.write(svc.vk.hex() + "\n")
            self.log(f"[{name}] prover tree: r={self.p.r} n={n}")
            status, dt, plog = self.run.tree(work, svc.sock_dir, self.p.tree_s)
            rec.update(status=status, seconds=dt, prover_log=plog[-4000:])
            self.log(f"[{name}] {status} in {dt:.3f} s")
            self.alive(svc)
            if status != "ok":
                raise Fail(f"{name}: prover tree {status}" + self.diag(svc, plog))
            try:
                rel = self.keep(f"{name}/root.bin", read_output(work, "root.bin", self.p.file_cap))
            except OutputError as e:
                raise Fail(f"{name}: {e}")
            res = self.check([(svc.vk, root, rel, f"{name} root")], name)
            rec["root_check_ns"] = res[0][1]
            rec["canaries"] = self.canary_check(svc.vk, [(rel, root, None)], name)
            rec["root_file"] = rel
            rec["root_bytes"] = os.path.getsize(os.path.join(self.store, rel))
            self.alive(svc)
        except Fail as e:
            e.rec = rec        # RF-m7: a failed run keeps its measurements in the result
            raise
        finally:
            self.stop(svc, rec)
        return rec

    # -- the stream ----------------------------------------------------------------------------------
    def stream_run(self):
        """The stream (cost model §3.3): `M + 1` leaves and `M` merges, a fresh process each, with a
        fresh service; every output checked with `acc` within `T_V`, and the statement canaries of
        the first `canaries.per_kind` leaves and nodes. From the first request on, everything, the
        checks included, runs within `stream_s`."""
        p, name = self.p, "stream"
        starts = [os.urandom(32) for _ in range(p.M + 1)]
        self.log(f"[{name}] computing {p.M + 1} leaf digests at n_f = {p.n_f}")
        ds = digest.leaf_digests(starts, p.n_f)
        svc = self.service(name)
        rec = {"vk": svc.vk.hex(), "service": svc.info, "leaf_digests": [d.hex() for d in ds],
               "leaf_s": [], "merge_s": []}
        pending, targets = [], []

        def flush():
            if pending:
                self.check(pending, f"{name} outputs")
                pending.clear()
        self.deadline = (time.monotonic() + p.stream_s, f"the stream's cap stream_s = {p.stream_s} s was reached")
        try:
            prev = None                        # (statement, store path) of the running proof
            for i in range(p.M + 1):
                ins = {"leaf.json": json.dumps({"n": p.n_f, "start": starts[i].hex()}).encode()}
                leaf = self.one(svc, name, f"leaf{i}", "leaf", ins)
                rec["leaf_s"].append(leaf[1])
                lrel = self.keep(f"{name}/leaf{i}.bin", leaf[0])
                pending.append((svc.vk, ds[i], lrel, f"{name} leaf {i}"))
                if i < p.canaries_per_kind:    # its sibling: the other child of the merge that takes it
                    targets.append((lrel, ds[i], prev[0] if prev else (ds[1] if p.M else None)))
                if i == 0:
                    prev = (ds[0], lrel)
                    flush()
                    continue
                ins = {"child1.stmt": (prev[0].hex() + "\n").encode(),
                       "child1.bin": open(os.path.join(self.store, prev[1]), "rb").read(),
                       "child2.stmt": (ds[i].hex() + "\n").encode(), "child2.bin": leaf[0]}
                node = self.one(svc, name, f"node{i}", "node", ins)
                rec["merge_s"].append(node[1])
                c = digest.node_stmt(prev[0], ds[i])
                nrel = self.keep(f"{name}/node{i}.bin", node[0])
                pending.append((svc.vk, c, nrel, f"{name} node {i}"))
                if i <= p.canaries_per_kind:   # its sibling: the next leaf, which the next merge takes
                    targets.append((nrel, c, ds[i + 1] if i < p.M else None))
                prev = (c, nrel)
                if i == 1 or len(pending) >= p.check_every:
                    flush()
            flush()
            rec["canaries"] = self.canary_check(svc.vk, targets, name)
            self.alive(svc)
        except Fail as e:
            e.rec = rec        # RF-m7: a failed run keeps its measurements in the result
            raise
        finally:
            self.deadline = None
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
        """One timed request, within `step_s` and the stream's cap."""
        work = fresh_dir(os.path.join(self.work, name, tag))
        with open(os.path.join(work, "vk.hex"), "w") as f:
            f.write(svc.vk.hex() + "\n")
        self.left(f"{name} {tag}")
        status, dt, proof, err = request(self.run, kind, work, svc.sock_dir, inputs, self.p.step_s, self.p.file_cap,
                                         deadline=self.deadline[0] if self.deadline else None)
        self.alive(svc)
        if status != "ok":
            capped = self.deadline is not None and time.monotonic() >= self.deadline[0]
            raise Fail(f"{name} {tag}: {status}" + (f" ({self.deadline[1]})" if capped else "") + self.diag(svc, err))
        shutil.rmtree(work, ignore_errors=True)
        shutil.rmtree(work + ".stage", ignore_errors=True)
        return proof, dt

    # -- the DoS column -------------------------------------------------------------------------------
    def dos(self, vk, root, root_rel):
        """The DoS column (RF-M1 (2), RF-m6, V4-A9): `dos.proofs` random and mutated proofs of the
        root's statement, each checked within the per-item cap (`dos.item_factor · T_V` where `T_V`
        is enforced, else `verify_s`) and all within `dos.total_s`. A breach of either cap, or a
        crash of the checker, is the entry's failure, and the slow input is kept in the store and
        named. An accepted input is recorded, not failed: it mutates a true statement's proof, and
        accepting it is malleability, which no rule forbids (V4-A9)."""
        data = open(os.path.join(self.store, root_rel), "rb").read()
        files = dos_inputs(data, self.p.dos_proofs, random.Random(os.urandom(16)))
        items = [(vk, root, self.keep(f"dos/{k}.bin", b)) for k, b in enumerate(files)]
        enforced = self.p.tv_enforce and self.tv_cap_ns is not None
        item_cap = self.p.dos_item_factor * self.tv_cap_ns if enforced else self.p.verify_s * 1e9
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
        return {"proofs": len(items), "accepted": len(acc), "accepted_inputs": [items[k][2] for k in acc[:5]],
                "max_ns": res[worst][1], "max_input": items[worst][2], "item_cap_ns": item_cap,
                "total_s": self.p.dos_total_s,
                "over_T_V": sum(1 for _, ns in res if self.tv_cap_ns and ns > self.tv_cap_ns)}


def score(p: Params, tree, stream):
    """`S = T_tree + K · t_link` (V4-10) from the one tree run and the one stream run (V4-A9), and the
    published components (cost model §3.6)."""
    out = {"K": p.K}
    if tree:
        out["T_tree"] = tree["seconds"]
    if stream:
        for k in ("t_leaf", "t_merge", "t_link", "slowest_merge"):
            out[k] = stream[k]
    if tree and stream:
        out["S"] = out["T_tree"] + p.K * out["t_link"]
        out["o_est"] = out["t_link"] - out["T_tree"] * p.n_f / ((1 << p.r) * p.n)
    return out

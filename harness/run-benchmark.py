#!/usr/bin/env python3
"""The benchmark half of an evaluation (TRUSTED RUNTIME).

  python3 -I harness/run-benchmark.py --season harness/season.toml --entry ENTRY --badge BADGE_DIR \
      --service rf-oracle --bench rf-bench --work WORK --out RESULT.json \
      [--parts calibrate,tree,dos,stream] [--provisional]

ENTRY holds `prover/*.s`. BADGE_DIR holds the entry's built `verify` and the organiser's
`chaincheck` (`evaluate.py` builds them). The order: machine and toolchain record; prover build in
the sandbox; `prover setup`; a fresh tree instance from `os.urandom`; `T_triv,best` and the service
calibration; the tree run (its own service; the root, its statement canary, `T_V`); the DoS column
on its root; the stream run (its own service; every output, the statement canaries, `T_V`); the
score. One run of each, no repeats (V4-A9). The first failure ends the run with `benchmark: fail`
and its reason. A run split over two jobs (`--parts`) writes partial results that `aggregate.py`
combines.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
import traceback

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rfh import digest  # noqa: E402
from rfh.bench import Bench, Fail, Params, leaves_json, machine, score  # noqa: E402
from rfh.prover import Run, build  # noqa: E402

ALL_PARTS = ["calibrate", "tree", "dos", "stream"]


def sha256(path):
    try:
        return hashlib.sha256(open(path, "rb").read()).hexdigest()
    except OSError:
        return None


def harness_commit():
    if os.environ.get("RF_HARNESS_COMMIT"):
        return os.environ["RF_HARNESS_COMMIT"]
    try:
        return subprocess.run(["git", "-C", os.path.dirname(os.path.abspath(__file__)), "rev-parse", "HEAD"],
                              capture_output=True, text=True, timeout=30).stdout.strip() or None
    except OSError:
        return None


def main():
    ap = argparse.ArgumentParser()
    for a in ("--season", "--entry", "--badge", "--service", "--bench", "--work", "--out"):
        ap.add_argument(a, required=True)
    ap.add_argument("--parts", default=",".join(ALL_PARTS))
    ap.add_argument("--provisional", action="store_true")
    a = ap.parse_args()
    p = Params.load(a.season)
    parts = a.parts.split(",")
    work = os.path.abspath(a.work)
    os.makedirs(work, exist_ok=False)
    logf = open(os.path.join(work, "run.log"), "a")

    def log(msg):
        line = f"{time.strftime('%H:%M:%S')} {msg}"
        print(line, flush=True)
        logf.write(line + "\n")
        logf.flush()

    res = {"schema": "recursion.fast/v4/result-1", "season": p.name, "season_sha256": sha256(a.season),
           "params": {k: v for k, v in vars(p).items()}, "parts": parts, "provisional": a.provisional,
           "comparable": not a.provisional, "machine": machine(),
           "harness": {"commit": harness_commit(), "service_sha256": sha256(a.service),
                       "bench_sha256": sha256(a.bench),
                       "badge_sha256": {b: sha256(os.path.join(a.badge, b)) for b in ("verify", "chaincheck")}},
           "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "benchmark": "pass", "reasons": []}
    log(f"recursion.fast v4 benchmark, season {p.name}, parts {parts}, machine {res['machine']['cpu_model']}")
    try:
        ok, info = build(os.path.join(a.entry, "prover"), os.path.join(work, "prover"), p.mem_prover, p.build_s)
        res["prover"] = info
        if not ok:
            raise Fail(f"prover build: {info.get('error')}")
        log(f"prover built: {info['binary_sha256']} ({info['binary_bytes']} bytes)")
        run = Run(os.path.join(work, "prover", "bin"), os.path.join(work, "setup"), p.mem_prover)
        ok, dt, slog = run.setup(p.setup_s)
        res["setup"] = {"ok": ok, "seconds": dt, "log": slog[-2000:]}
        if not ok:
            raise Fail("prover setup failed")
        if p.tv_enforce and ("tree" in parts or "stream" in parts) and "calibrate" not in parts:
            raise RuntimeError("T_V is enforced but no calibration runs in this job (RB-m4): add the part `calibrate`")
        bench = Bench(p, run, os.path.abspath(a.badge), os.path.abspath(a.service), os.path.abspath(a.bench), work, log)
        # the tree instance: fresh secret starts, held by the runner
        starts = [os.urandom(32) for _ in range(1 << p.r)]
        log(f"tree instance: {1 << p.r} chains of {p.n}")
        levels = digest.tree_levels(digest.leaf_digests(starts, p.n))
        inst = os.path.join(work, "instance")
        os.makedirs(inst)
        with open(os.path.join(inst, "leaves.json"), "wb") as f:
            f.write(leaves_json(starts, p.n))
        res["instance"] = {"root": levels[-1][0].hex(), "leaf_digests": [d.hex() for d in levels[0]],
                           "starts": [s.hex() for s in starts]}
        if "calibrate" in parts:
            res["calibration"] = bench.calibrate(inst, p.n, levels[-1][0])
            log(f"T_triv,best = {res['calibration']['T_triv_best_ns'] / 1e6:.3f} ms, "
                f"T_V cap = {bench.tv_cap_ns / 1e6:.3f} ms; service {res['calibration']['service']}")
        if "tree" in parts:
            res["tree"] = bench.tree_run(starts, p.n, levels[-1][0])
        if "dos" in parts and "tree" in res:
            res["dos"] = bench.dos(bytes.fromhex(res["tree"]["vk"]), levels[-1][0], res["tree"]["root_file"])
            log(f"DoS column: {res['dos']}")
        if "stream" in parts:
            res["stream"] = bench.stream_run()
        res["T_V"] = {"cap_ns": bench.tv_cap_ns, "enforced": p.tv_enforce, "remeasured": bench.tv_remeasured,
                      "statistic": f"best of {p.checker_runs} for the cap and for a check above it",
                      "max_ns": max((ns for _, ns in bench.tv_seen), default=None),
                      "checks": len(bench.tv_seen),
                      "over_cap": sum(1 for _, ns in bench.tv_seen if bench.tv_cap_ns and ns > bench.tv_cap_ns)}
        res["score"] = score(p, res.get("tree"), res.get("stream"))
        log(f"score: {res['score']}")
    except Fail as e:
        res["benchmark"] = "fail"
        res["reasons"].append(str(e))
        if getattr(e, "rec", None) is not None:
            res["failed_run"] = e.rec
        log(f"FAIL: {e}")
    except Exception as e:  # a harness error is not the entry's failure: say so
        res["benchmark"] = "error"
        res["reasons"].append(f"harness error: {e!r}")
        res["traceback"] = traceback.format_exc()[-4000:]
        log(f"HARNESS ERROR: {e!r}")
    res["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    with open(a.out, "w") as f:
        json.dump(res, f, indent=1)
    log(f"benchmark: {res['benchmark']} -> {a.out}")
    return {"pass": 0, "fail": 1}.get(res["benchmark"], 2)


if __name__ == "__main__":
    sys.exit(main())

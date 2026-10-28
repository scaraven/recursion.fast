#!/usr/bin/env python3
"""The benchmark half of an evaluation (TRUSTED RUNTIME; V4-A11).

  python3 -I harness/run-benchmark.py --season harness/season.toml --entry ENTRY --badge BADGE_DIR \
      --service rf-oracle --bench rf-bench --work WORK --out RESULT.json \
      [--parts calibrate,stream,dos] [--provisional]

ENTRY holds `prover/*.s`. BADGE_DIR holds the entry's built `verify` and the organiser's
`chaincheck` (`evaluate.py` builds them). The order: machine and toolchain record; the calibration
workload `calib` built from `harness/tools/calib.c` with the runner's `gcc` (before any entry code
runs); prover build in the sandbox; `prover setup` (untimed, within `setup_s`, its directory within
`setup_cap`); the calibration instance and the service calibration; the stream (its own service; every
step a fresh process, every output checked, the statement canaries, interleaved `c_P` and `T_triv`
samples, the re-timing); the DoS column on its last output; the score (`rfh.bench.score`). One stream
per evaluation, no repeats (V4-A9, V4-A11). The per-step JSON lines go to WORK/stream.jsonl and into
the result. The first failure ends the run with `benchmark: fail` and its reason; a truncated stream
(its cap reached) is scored over its completed steps and flagged, never ranked.
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
from rfh.bench import Bench, Fail, Params, build_calib, machine, score  # noqa: E402
from rfh.prover import Run, build, tree_sha256  # noqa: E402

ALL_PARTS = ["calibrate", "stream", "dos"]


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
        calib_bin, res["calib"] = build_calib(os.path.join(work, "calib"))
        ok, info = build(os.path.join(a.entry, "prover"), os.path.join(work, "prover"), p.mem_prover, p.build_s)
        res["prover"] = info
        if not ok:
            raise Fail(f"prover build: {info.get('error')}")
        log(f"prover built: {info['binary_sha256']} ({info['binary_bytes']} bytes)")
        run = Run(os.path.join(work, "prover", "bin"), os.path.join(work, "setup"), p.mem_prover)
        ok, dt, slog = run.setup(p.setup_s, p.setup_cap)
        res["setup"] = {"ok": ok, "seconds": dt, "log": slog[-2000:]}
        if ok:
            res["setup"]["sha256"] = tree_sha256(run.setup_dir)
        if not ok:
            raise Fail("prover setup failed" + (": " + slog.strip().splitlines()[-1] if "setup_cap" in slog else ""))
        if "stream" in parts and "calibrate" not in parts:
            raise RuntimeError("the stream needs the part `calibrate` in the same job (its samples are interleaved)")
        bench = Bench(p, run, os.path.abspath(a.badge), os.path.abspath(a.service), os.path.abspath(a.bench), work,
                      calib_bin=calib_bin, log=log)
        if "calibrate" in parts:
            res["calibration"] = bench.calibrate()
            log(f"calibration instance: {res['calibration']['triv_compressions']} compressions; "
                f"service {res['calibration']['service']}")
        if "stream" in parts:
            res["stream"] = bench.stream_run()
            cal = res["stream"]["calibration"]
            log(f"c_P = {cal['c_P']:.4f}, T_triv = {cal['T_triv_ns'] / 1e6:.3f} ms, v_ref = {cal['v_ref_ns'] / 1e6:.3f} ms")
            res["score"] = score(p, res["stream"])
            with open(os.path.join(work, "stream.jsonl"), "w") as f:
                for s in res["stream"]["steps"]:
                    f.write(json.dumps(s) + "\n")
            log(f"score: S = {res['score']['S']:.4f} (P̄ {res['score']['P_bar']:.4f}, V̄ {res['score']['V_bar']:.4f}), "
                f"M = {res['score']['M']}" + (", TRUNCATED" if res["stream"]["truncated"] else ""))
            if res["stream"]["truncated"]:
                res["comparable"] = False
        if "dos" in parts and "stream" in res:
            st = res["stream"]
            res["dos"] = bench.dos(bytes.fromhex(st["vk"]), bytes.fromhex(st["last_stmt"]), st["last_file"],
                                   st["calibration"]["v_ref_ns"])
            log(f"DoS column: {res['dos']}")
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

#!/usr/bin/env python3
"""Combines the benchmark results of one evaluation into its result (TRUSTED; data only).

  python3 -I harness/aggregate.py --season SEASON --cert CERT.json --out RESULT.json [--job URL] PART.json...

A run split over several jobs (`.github/workflows/evaluate.yml`, `split`) has one partial result per
job; each job calibrated `T_V` and the service on its own machine and checked its own outputs
against that calibration, so the parts are combined only by collecting the repeats: `T_tree` is the
median of all tree repeats and `t_leaf`, `t_merge`, `t_link` the medians of all stream repeats, as
in a single job (V4-10). The CPU model of every part is listed; a result whose parts ran on
different CPU models says so (`mixed_cpu`), and such a result is never used for a paired record
comparison (P3 (d)). Verdict: REJECT if the certificate was rejected or any part failed; ERROR if a
part had a harness error; otherwise ACCEPT, or PROVISIONAL for a provisional certificate (V4-15).
"""
import argparse
import hashlib
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rfh.bench import Params, score  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--season", required=True)
    ap.add_argument("--cert", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--job", default=None)
    ap.add_argument("parts", nargs="*")
    a = ap.parse_args()
    p = Params.load(a.season)
    cert = json.load(open(a.cert))
    parts = [json.load(open(f)) for f in sorted(a.parts)]
    res = {"schema": "recursion.fast/v4/result-1", "season": p.name,
           "season_sha256": hashlib.sha256(open(a.season, "rb").read()).hexdigest(), "job": a.job,
           "certificate": {k: cert.get(k) for k in ("status", "reasons", "provisional_reasons", "kernels",
                                                     "second_kernel", "kernel_runs", "gate", "badge_sha256", "claim", "built_modules")},
           "parts": [], "reasons": list(cert.get("reasons", []))}
    trees, streams = [], []
    for r in parts:
        res["parts"].append({k: r.get(k) for k in ("parts", "machine", "harness", "prover", "calibration", "T_V", "dos",
                                                    "liveness", "benchmark", "reasons", "started", "finished",
                                                    "instance", "comparable", "provisional")})
        trees += r.get("tree", [])
        streams += r.get("stream", [])
        res["reasons"] += r.get("reasons", [])
    res["tree"], res["stream"] = trees, streams
    models = sorted({(r.get("machine") or {}).get("cpu_model") or "?" for r in parts})
    res["cpu_models"], res["mixed_cpu"] = models, len(models) > 1
    status = [r.get("benchmark") for r in parts]
    if cert.get("status") == "reject":
        verdict = "REJECT"
    elif "error" in status or not parts:
        verdict = "ERROR" if parts else "REJECT"
        if not parts:
            res["reasons"].append("no benchmark result")
    elif any(s != "pass" for s in status):
        verdict = "REJECT"
    else:
        verdict = "ACCEPT" if cert.get("status") == "ok" else "PROVISIONAL"
    res["verdict"] = verdict
    res["comparable"] = verdict == "ACCEPT" and not res["mixed_cpu"]
    if verdict in ("ACCEPT", "PROVISIONAL"):
        res["score"] = score(p, trees, streams)
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"VERDICT: {verdict} ({len(parts)} part(s), CPU {models})")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Combines the benchmark results of one evaluation into its result (TRUSTED; data only).

  python3 -I harness/aggregate.py --print-matrix split|single          the benchmark jobs' parts
  python3 -I harness/aggregate.py --plan split|single --season SEASON --cert CERT.json --out RESULT.json
                                  [--job URL] PART.json...

**The plan** (RF-M1). This file is the one definition of the benchmark jobs: `evaluate.yml` builds
its matrix from `--print-matrix`, and the aggregation requires **exactly** that multiset of parts.
Each part is identified by the `parts` its result JSON records. A missing, extra, duplicated or
mismatched part, or parts that disagree on the season or the harness commit, make the verdict
ERROR and the result not comparable. So a job lost to the 6 h limit or to a runner failure can
never yield an ACCEPT from the jobs that remain, and in particular the DoS column and liveness
(job 0 only) are always in an ACCEPT.

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
import collections
import hashlib
import json
import os
import sys

ALL_PARTS = "calibrate,tree,dos,stream,liveness"
# Every job calibrates on its own machine; job 0 alone runs the DoS column and liveness.
PLANS = {"split": ["calibrate,tree,dos,liveness", "calibrate,tree", "calibrate,tree",
                   "calibrate,stream", "calibrate,stream", "calibrate,stream"],
         "single": ["all"]}

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rfh.bench import Params, score  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--print-matrix", choices=sorted(PLANS))
    ap.add_argument("--plan", choices=sorted(PLANS))
    ap.add_argument("--season")
    ap.add_argument("--cert")
    ap.add_argument("--out")
    ap.add_argument("--job", default=None)
    ap.add_argument("parts", nargs="*")
    a = ap.parse_args()
    if a.print_matrix:
        print(json.dumps(PLANS[a.print_matrix]))
        return 0
    if not (a.plan and a.season and a.cert and a.out):
        ap.error("--plan, --season, --cert and --out are required")
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
    # RF-M1: exactly the planned parts, one result each, from one season and one harness commit
    want = collections.Counter(ALL_PARTS if p == "all" else p for p in PLANS[a.plan])
    got = collections.Counter(",".join(r.get("parts") or []) for r in parts)
    plan_errors = []
    if got != want:
        plan_errors.append(f"benchmark parts do not match the plan `{a.plan}`: missing {sorted((want - got).elements())}, "
                           f"unexpected {sorted((got - want).elements())}")
    commits = {(r.get("harness") or {}).get("commit") for r in parts}
    seasons = {r.get("season_sha256") for r in parts}
    if len(commits) > 1 or len(seasons) > 1:
        plan_errors.append(f"parts from different harness commits {sorted(map(str, commits))} or seasons")
    res["plan"], res["harness_commit"] = a.plan, (commits.pop() if len(commits) == 1 else None)
    res["reasons"] += plan_errors
    models = sorted({(r.get("machine") or {}).get("cpu_model") or "?" for r in parts})
    res["cpu_models"], res["mixed_cpu"] = models, len(models) > 1
    status = [r.get("benchmark") for r in parts]
    if cert.get("status") == "reject":
        verdict = "REJECT"
    elif cert.get("status") not in ("ok", "provisional"):
        verdict = "ERROR"                     # the certificate job itself failed (harness error)
    elif any(st == "fail" for st in status):
        verdict = "REJECT"                    # a part the entry failed decides, whatever is missing
    elif "error" in status or plan_errors:
        verdict = "ERROR"
    elif any(s != "pass" for s in status):
        verdict = "REJECT"
    else:
        verdict = "ACCEPT" if cert.get("status") == "ok" else "PROVISIONAL"
    res["verdict"] = verdict
    res["comparable"] = verdict == "ACCEPT" and not res["mixed_cpu"] and not plan_errors
    if verdict in ("ACCEPT", "PROVISIONAL"):
        res["score"] = score(p, trees, streams)
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"VERDICT: {verdict} ({len(parts)} part(s), CPU {models})")
    return 0


if __name__ == "__main__":
    sys.exit(main())

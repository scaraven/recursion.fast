#!/usr/bin/env python3
"""Combines the benchmark results of one evaluation into its result (TRUSTED; data only), and ranks
entries provisionally.

  python3 -I harness/aggregate.py --print-matrix single                 the benchmark jobs' parts
  python3 -I harness/aggregate.py --plan single --season SEASON --cert CERT.json --out RESULT.json
                                  [--job URL] PART.json...
  python3 -I harness/aggregate.py --rank --out RANKING.json RESULT.json...

**The plan** (RF-M1). This file is the one definition of the benchmark jobs: `evaluate.yml` builds
its matrix from `--print-matrix`, and the aggregation requires **exactly** that multiset of parts.
Each part is identified by the `parts` its result JSON records. A missing, extra, duplicated or
mismatched part, or parts that disagree on the season or the harness commit, make the verdict
ERROR and the result not comparable, so a job lost to its time limit or to a runner failure never
yields an ACCEPT. Since V4-A11 the benchmark is **one job**: the calibration, the one stream (with
its interleaved samples and its re-timing) and the DoS column on the stream's last output (`split`
is kept as a name for callers and is the same one job). The score is recomputed here from the
stream's per-step records with `rfh.bench.score`, the definition the runner used. Verdict: REJECT
if the certificate was rejected or the part failed; ERROR if it had a harness error or the plan does
not match; otherwise ACCEPT, or PROVISIONAL for a provisional certificate (V4-15). A **truncated**
stream (its cap reached, §6) is ACCEPTed with its score but never comparable (`comparable: false`).

**The provisional ranking** (V4-A11 §11 R-M1, review M-4; until the paired record of §7 exists):
`--rank` groups results by the entry (its name in the submissions repository, `entry.name`; the
binary's hash would let a no-op edit start a fresh group) and ranks an entry, once it has at least
three evaluations, by the median score of its last three (by `finished`), each REJECT,
PROVISIONAL, truncated or otherwise not comparable run counting as infinite; it publishes each
entry's counts of evaluations, failures and unscored runs. ERROR results (the organiser's) are not
counted.
"""
import argparse
import collections
import hashlib
import json
import os
import statistics
import sys

ALL_PARTS = "calibrate,stream,dos"
# V4-A11: one benchmark job; `split` is the same one job (the name callers pass)
PLANS = {"split": ["all"], "single": ["all"]}

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
    ap.add_argument("--rank", action="store_true")
    ap.add_argument("parts", nargs="*")
    a = ap.parse_args()
    if a.print_matrix:
        print(json.dumps(PLANS[a.print_matrix]))
        return 0
    if a.rank:
        if not a.out:
            ap.error("--rank needs --out")
        json.dump(rank([json.load(open(f)) for f in a.parts]), open(a.out, "w"), indent=1)
        return 0
    if not (a.plan and a.season and a.cert and a.out):
        ap.error("--plan, --season, --cert and --out are required")
    p = Params.load(a.season)
    cert = json.load(open(a.cert))
    parts = [json.load(open(f)) for f in sorted(a.parts)]
    res = {"schema": "recursion.fast/v4/result-1", "season": p.name,
           "season_sha256": hashlib.sha256(open(a.season, "rb").read()).hexdigest(), "job": a.job,
           "certificate": {k: cert.get(k) for k in ("status", "reasons", "provisional_reasons", "kernels",
                                                     "second_kernel", "kernel_runs", "gate", "badge_sha256", "claim",
                                                     "built_modules", "environment")},
           "parts": [], "reasons": list(cert.get("reasons", []))}
    res["stream"] = None
    for r in parts:
        res["parts"].append({k: r.get(k) for k in ("parts", "machine", "harness", "prover", "calib", "calibration", "dos",
                                                    "benchmark", "reasons", "started", "finished", "comparable",
                                                    "provisional")})
        res["stream"] = r.get("stream") or res["stream"]     # one run; the plan check rejects a second
        res["reasons"] += r.get("reasons", [])
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
    truncated = bool((res["stream"] or {}).get("truncated"))
    res["truncated"] = truncated
    res["comparable"] = verdict == "ACCEPT" and not res["mixed_cpu"] and not plan_errors and not truncated
    res["prover_sha256"] = next(((r.get("prover") or {}).get("binary_sha256") for r in parts if r.get("prover")), None)
    res["entry"] = next((r.get("entry") for r in parts if r.get("entry")), None)
    if verdict in ("ACCEPT", "PROVISIONAL") and res["stream"]:
        res["score"] = score(p, res["stream"])
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"VERDICT: {verdict} ({len(parts)} part(s), CPU {models})")
    return 0


def entry_key(r):
    """The entry a result belongs to: its name in the submissions repository (`entry.name`, which the
    evaluation workflow sets from the entry's root), else the hash of its prover sources. Not the
    binary's hash: a no-op edit gives a fresh binary, and a fresh group would reset the window."""
    e = r.get("entry") or {}
    return e.get("name") or e.get("prover_sources_sha256")


def rank(results):
    """The provisional ranking (R-M1, review M-4): per entry, the median of its last three
    evaluations' scores, each REJECT, PROVISIONAL, truncated or otherwise not comparable run counting
    as infinite (none of them can help); an entry is ranked only once it has at least three counted
    evaluations. ERROR results (the organiser's) are not counted."""
    by = collections.defaultdict(list)
    for r in results:
        if r.get("verdict") == "ERROR" or not entry_key(r):
            continue
        by[entry_key(r)].append(r)
    rows = []
    inf = float("inf")
    for key, rs in by.items():
        rs.sort(key=lambda r: r.get("finished") or "")
        vals = [r["score"]["S"] if r.get("verdict") == "ACCEPT" and r.get("comparable")
                and (r.get("score") or {}).get("S") is not None else inf for r in rs[-3:]]
        med = statistics.median(vals) if len(rs) >= 3 else None
        rows.append({"entry": key, "evaluations": len(rs),
                     "failures": sum(r.get("verdict") == "REJECT" for r in rs),
                     "not_scored": sum(r.get("verdict") == "ACCEPT" and not r.get("comparable") for r in rs),
                     "last_three": [v if v != inf else "failed or not scored" for v in vals],
                     "median_S": "unranked (fewer than 3 evaluations)" if med is None
                     else (med if med != inf else "failed")})
    rows.sort(key=lambda x: (not isinstance(x["median_S"], float), x["median_S"] if isinstance(x["median_S"], float) else 0))
    return {"schema": "recursion.fast/v4/ranking-2",
            "rule": "per entry (its name in the submissions repository), the median of its last three evaluations, "
                    "a REJECT, PROVISIONAL, truncated or not comparable run counting as infinite; ranked from three "
                    "evaluations (R-M1, review M-4); provisional until the paired record (§7)", "entries": rows}


if __name__ == "__main__":
    sys.exit(main())

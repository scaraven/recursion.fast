#!/usr/bin/env python3
"""Combines the benchmark results of one evaluation into its result (TRUSTED; data only), and ranks
entries provisionally.

  python3 -I harness/aggregate.py --print-matrix single                 the benchmark jobs' parts
  python3 -I harness/aggregate.py --plan single --season SEASON --cert CERT.json --out RESULT.json
                                  [--job URL] PART.json...
  python3 -I harness/aggregate.py --rank --out RANKING.json RESULT.json...
  python3 -I harness/aggregate.py --check-machine --season SEASON        this machine's fingerprint
                                  problem (one line, empty if none; the setup job's first step)
  python3 -I harness/aggregate.py --organiser-error KIND --reason TEXT --season SEASON --out RESULT.json
                                  --harness-commit SHA [--job URL]      the ERROR result of a run that
                                  stopped on the organiser's side before any benchmark

**Organiser errors** are named (`organiser_error` in the result): `fingerprint` (AGENTS.md §6, the machine), `lengths`
(the stream did not use the season's chain lengths, or the season file's `[stream] lengths` is
malformed), `drift` (AGENTS.md §6, calibration), `setup` (the setup jobs did not complete), `cache` (an organiser
cache was missing). They never count against the author in the bot's fair order; `harness` (the
certificate job ended without a certificate) and an unnamed ERROR are not exempt.

**The plan**. This file is the one definition of the benchmark jobs: `evaluate.yml` builds
its matrix from `--print-matrix`, and the aggregation requires **exactly** that multiset of parts.
Each part is identified by the `parts` its result JSON records. A missing, extra, duplicated or
mismatched part, or parts that disagree on the season or the harness commit, make the verdict
ERROR and the result not comparable, so a job lost to its time limit or to a runner failure never
yields an ACCEPT. The benchmark is **one job**: the calibration, the one stream (with
its interleaved samples and its re-timing) and the DoS column on the stream's last output (`split`
is kept as a name for callers and is the same one job). The score is recomputed here from the
stream's per-step records with `rfh.bench.score`, the definition the runner used. Verdict: REJECT
if the certificate was rejected or the part failed; ERROR if it had a harness error or the plan does
not match; otherwise ACCEPT, or PROVISIONAL for a provisional certificate. The result is
**comparable** iff it is ACCEPT and its stream was not truncated (its cap reached, AGENTS.md §8; a
truncated stream is ACCEPTed with its score). A benchmark whose machine fingerprint
(`machine.fingerprint`, `rfh.bench.fingerprint`) is missing, unreadable or not the season's
`[machine] fingerprint` is an organiser ERROR, whatever the entry did (`"any"`: the smoke's, any
machine); the reason says which. Likewise a stream whose chain lengths (`stream.lengths`) are not
the season's fixed `[stream] lengths` is an organiser ERROR (`lengths`): its score is not comparable
with any other evaluation's. A season file whose `[stream] lengths` is malformed (not `M + 1`
integers in `[n_lo, n_hi]`) is named the same way in every mode: `--check-machine` prints it as the
organiser's problem (so the setup job stops the evaluation), and `--organiser-error` and `--plan`
then write an ERROR result named `lengths`, whatever kind the workflow passed, since a malformed
list is the cause of anything else that stopped the run.
The result also records the runner the benchmark ran on (`runner`: name, environment, labels), which
`verify-record.sh` checks (AGENTS.md §8).

**The provisional ranking**:
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
# one benchmark job; `split` is the same one job (the name callers pass)
PLANS = {"split": ["all"], "single": ["all"]}
ORGANISER_ERRORS = ("fingerprint", "lengths", "drift", "setup", "cache", "harness")

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rfh.bench import Params, fingerprint, fingerprint_problem, score  # noqa: E402


def load_season(path):
    """(Params, None) for a well-formed season file, or (Params unchecked, the defect) when its
    `[stream] lengths` is malformed; any other defect of the file raises as before."""
    try:
        return Params.load(path), None
    except ValueError as e:
        if "[stream]" not in str(e):
            raise
        return Params.load(path, check=False), str(e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--print-matrix", choices=sorted(PLANS))
    ap.add_argument("--plan", choices=sorted(PLANS))
    ap.add_argument("--season")
    ap.add_argument("--cert")
    ap.add_argument("--out")
    ap.add_argument("--job", default=None)
    ap.add_argument("--rank", action="store_true")
    ap.add_argument("--check-machine", action="store_true")
    ap.add_argument("--organiser-error", choices=sorted(ORGANISER_ERRORS))
    ap.add_argument("--reason", default="")
    ap.add_argument("--harness-commit", default=None)
    ap.add_argument("parts", nargs="*")
    a = ap.parse_args()
    if a.check_machine:
        p, defect = load_season(a.season)
        if defect:
            print(f"the season file's [stream] lengths is malformed ({defect})")
            return 0
        fp = fingerprint()
        why = fingerprint_problem(fp["status"], fp["hash"], p.fingerprint)
        if why:
            print(f"the machine fingerprint is {why} ("
                  + (f"fingerprint {fp['hash']}, the season expects {p.fingerprint}" if why == "mismatched" else fp["reason"])
                  + ")")
        return 0
    if a.organiser_error:
        if not (a.season and a.out):
            ap.error("--organiser-error needs --season and --out")
        p, defect = load_season(a.season)
        kind, reason = a.organiser_error, a.reason
        if defect:
            kind = "lengths"
            if defect not in reason:          # the setup job's check already names it
                reason = f"the season file's [stream] lengths is malformed ({defect}); {reason}"
        res = {"schema": "recursion.fast/v4/result-1", "season": p.name,
               "season_sha256": hashlib.sha256(open(a.season, "rb").read()).hexdigest(), "job": a.job,
               "harness_commit": a.harness_commit, "verdict": "ERROR", "comparable": False, "truncated": False,
               "organiser_error": kind, "parts": [], "stream": None,
               "reasons": [f"organiser ERROR ({kind}): {reason}"[:600]]}
        json.dump(res, open(a.out, "w"), indent=1)
        print(f"VERDICT: ERROR (organiser: {kind})")
        return 0
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
    p, defect = load_season(a.season)
    season_sha = hashlib.sha256(open(a.season, "rb").read()).hexdigest()
    res = combine(p, a.plan, season_sha, a.job, json.load(open(a.cert)), [json.load(open(f)) for f in sorted(a.parts)],
                  lengths_defect=defect)
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"VERDICT: {res['verdict']} ({len(res['parts'])} part(s), comparable {res['comparable']}, "
          f"fingerprint {'matches' if res['machine']['matches'] else 'does not match'})")
    return 0


def combine(p, plan, season_sha, job, cert, parts, lengths_defect=None):
    """One entry's result from its certificate and its benchmark parts: the plan check, the verdict, the score.
    `lengths_defect`: why the season file's `[stream] lengths` is malformed, if it is."""
    res = {"schema": "recursion.fast/v4/result-1", "season": p.name, "season_sha256": season_sha, "job": job,
           "certificate": {k: cert.get(k) for k in ("status", "reasons", "provisional_reasons", "kernels",
                                                     "second_kernel", "kernel_runs", "gate", "badge_sha256", "claim",
                                                     "built_modules", "environment", "record_cache", "entry_build")},
           "parts": [], "reasons": list(cert.get("reasons", []))}
    res["stream"] = None
    for r in parts:
        res["parts"].append({k: r.get(k) for k in ("parts", "machine", "harness", "prover", "calib", "calibration", "dos",
                                                    "benchmark", "reasons", "started", "finished", "comparable",
                                                    "provisional")})
        res["stream"] = r.get("stream") or res["stream"]     # one run; the plan check rejects a second
        res["reasons"] += r.get("reasons", [])
    # exactly the planned parts, one result each, from one season and one harness commit
    want = collections.Counter(ALL_PARTS if p == "all" else p for p in PLANS[plan])
    got = collections.Counter(",".join(r.get("parts") or []) for r in parts)
    plan_errors = []
    if got != want:
        plan_errors.append(f"benchmark parts do not match the plan `{plan}`: missing {sorted((want - got).elements())}, "
                           f"unexpected {sorted((got - want).elements())}")
    commits = {(r.get("harness") or {}).get("commit") for r in parts}
    seasons = {r.get("season_sha256") for r in parts}
    if len(commits) > 1 or len(seasons) > 1:
        plan_errors.append(f"parts from different harness commits {sorted(map(str, commits))} or seasons")
    res["plan"], res["harness_commit"] = plan, (commits.pop() if len(commits) == 1 else None)
    res["reasons"] += plan_errors
    m = next(((r.get("machine") or {}) for r in parts), {})
    fps = {(r.get("machine") or {}).get("fingerprint") for r in parts}
    fp = fps.pop() if len(fps) == 1 else None
    fp_why = fingerprint_problem(m.get("fingerprint_status"), fp, p.fingerprint) if parts else None
    res["machine"] = {"fingerprint": fp, "expected": p.fingerprint, "matches": bool(parts) and fp_why is None,
                      "host_kernel": m.get("host_kernel")}
    res["runner"] = {"name": m.get("runner_name"), "environment": m.get("runner_environment"),
                     "labels": m.get("runner_labels") or []}
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
    if fp_why and cert.get("status") in ("ok", "provisional"):
        # not the season's machine is the organiser's condition, never the entry's verdict
        verdict = "ERROR"
        why = (f"fingerprint {fp}, the season expects {p.fingerprint}" if fp_why == "mismatched"
               else m.get("fingerprint_reason") or "no fingerprint recorded")
        msg = f"organiser ERROR: the machine fingerprint is {fp_why} ({why})"
        if not any("machine fingerprint" in str(x) for x in res["reasons"]):
            res["reasons"].append(msg)
    # the season's fixed chain lengths: a stream that used others is not comparable with any evaluation
    got_ns = res["stream"].get("lengths") if isinstance(res["stream"], dict) else None
    cert_ok = cert.get("status") in ("ok", "provisional")
    len_why = cert_ok and (lengths_defect is not None or (res["stream"] is not None and got_ns != p.lengths))
    if len_why and lengths_defect is not None:
        verdict = "ERROR"
        res["reasons"].append(f"organiser ERROR: the season file's [stream] lengths is malformed ({lengths_defect})")
    elif len_why:
        verdict = "ERROR"
        if isinstance(got_ns, list):
            first = next((k for k, (x, y) in enumerate(zip(got_ns, p.lengths)) if x != y), min(len(got_ns), len(p.lengths)))
            what = f"{len(got_ns)} values recorded, {len(p.lengths)} expected, the first difference at index {first}"
        else:
            what = "no list recorded"
        res["reasons"].append(f"organiser ERROR: the stream's chain lengths are not the season's [stream] lengths ({what})")
    res["verdict"] = verdict
    if verdict == "ERROR":      # the named organiser error, if one is known (the bot exempts some)
        kinds = [x.get("organiser_error") for x in [cert] + list(parts) if x.get("organiser_error") in ORGANISER_ERRORS]
        res["organiser_error"] = "fingerprint" if fp_why else "lengths" if len_why else (kinds[0] if kinds else None)
    truncated = bool((res["stream"] or {}).get("truncated"))
    res["truncated"] = truncated
    res["comparable"] = verdict == "ACCEPT" and not plan_errors and not truncated
    res["prover_sha256"] = next(((r.get("prover") or {}).get("binary_sha256") for r in parts if r.get("prover")), None)
    res["entry"] = next((r.get("entry") for r in parts if r.get("entry")), None)
    if verdict in ("ACCEPT", "PROVISIONAL") and res["stream"]:
        res["score"] = score(p, res["stream"])
    return res


def entry_key(r):
    """The entry a result belongs to: its name in the submissions repository (`entry.name`, which the
    evaluation workflow sets from the entry's root), else the hash of its prover sources. Not the
    binary's hash: a no-op edit gives a fresh binary, and a fresh group would reset the window."""
    e = r.get("entry") or {}
    return e.get("name") or e.get("prover_sources_sha256")


def rank(results):
    """The provisional ranking: per entry, the median of its last three
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
                    "evaluations", "entries": rows}


if __name__ == "__main__":
    sys.exit(main())

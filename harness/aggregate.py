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

`--plan … --allow-test-overrides` (tests only; the evaluation workflow never passes it) aggregates a
part that ran under a test-only override as if it had not, recording the overrides in
`test_overrides`: the smoke on a machine without a systemd user manager, or with its stand-in badge.

**Organiser errors** are named (`organiser_error` in the result): `fingerprint` (AGENTS.md §6, the machine, or
no systemd user manager for the sandboxes' memory scopes, `run-benchmark.py`; also a part that ran under
a test-only override, `TEST_OVERRIDES`: `machine.memcap_override`, `machine.badge_host_root` or
`machine.memcap = prlimit`, review LR5 L2), `lengths`
(the stream's shape, `M` and the leaf size `n`, is not the season's, or the season
file's `[stream]` shape is malformed; the name is kept from the chain-length list of earlier
seasons), `drift` (AGENTS.md §6, calibration), `setup` (the setup jobs did not complete), `cache` (an organiser
cache was missing), `malformed` (a passed run's stream record is missing, has a step without exactly
`timed_runs` timed times, or is not of the shape `rfh.bench.check_record` requires: steps 1 … M, each
verifier time the median of its three judged runs, the final step accepted within its caps; so no
score can be computed from it: `rfh.bench.MalformedStream`). They never count
against the author in the bot's fair order; `harness` (the
certificate job ended without a certificate) and an unnamed ERROR count against the author after the entry's first one.

**The plan**. This file is the one definition of the benchmark jobs: `evaluate.yml` builds
its matrix from `--print-matrix`, and the aggregation requires **exactly** that multiset of parts.
Each part is identified by the `parts` its result JSON records. A missing, extra, duplicated or
mismatched part, or parts that disagree on the season or the harness commit, make the verdict
ERROR and the result not comparable, so a job lost to its time limit or to a runner failure never
yields an ACCEPT. The benchmark is **one job**: the calibration and the one stream (with
its interleaved samples and its timed passes; `split` is kept as a name for callers and is the same
one job). The score (AGENTS.md §7: `P_total` the median of the timed passes' totals, `S = P_total ·
|π_M|` for `final`, `S_every = P_total · max_i |π_i|` for `every`, seconds · bytes) and
the tracks the run is in (`final`, and `every` when its conditions hold) are recomputed here from the
stream's per-step records with `rfh.bench.score`, the definition the runner used, before the verdict
and comparability are set, after `rfh.bench.check_record` checked the record's shape; whatever score a
part recorded is replaced, and a stream record it cannot be computed from is an organiser ERROR
(`malformed`). Verdict: REJECT
if the certificate was rejected or the part failed; ERROR if it had a harness error or the plan does
not match; otherwise ACCEPT, or PROVISIONAL for a provisional certificate. A REJECT carries where it
was rejected (`reject_stage`, `rfh.bench.REJECT_STAGES`): `certificate` for a rejected certificate,
else the failed part's own (`prover`, `request`, `check`, `timed-pass`, `stream-cap`); the bot
re-runs a REJECT without the record build cache only at `certificate` and `check`. The result is
**comparable** iff it is ACCEPT (a stream that reaches its cap is the entry's REJECT; the `truncated`
flag is kept, always false since season rules v6). A benchmark whose machine fingerprint
(`machine.fingerprint`, `rfh.bench.fingerprint`) is missing, unreadable or not the season's
`[machine] fingerprint` is an organiser ERROR, whatever the entry did (`"any"`: the smoke's, any
machine); the reason says which. Likewise a stream whose shape (`stream.shape`: `M`, `n`)
is not the season's is an organiser ERROR (`lengths`): its score is not comparable with any other
evaluation's. A season file whose `[stream]` shape is malformed (`M`, `n` not positive
integers, `n` above `leafCap = 2^20` blocks, `timed_runs` not an odd positive integer) is named
the same way in every mode: `--check-machine` prints it as the organiser's problem (so the setup job
stops the evaluation), and `--organiser-error` and `--plan` then write an ERROR result named
`lengths`, whatever kind the workflow passed, since a malformed shape is the cause of anything else
that stopped the run.
The result also records the runner the benchmark ran on (`runner`: name, environment, labels), which
`verify-record.sh` checks (AGENTS.md §8), and the measured entry (`entry`: with `--entry-name`,
`--entry-sha`, `--entry-tree`, `--pr-ref`, which the attest job passes, its `name`
(`<repo>:submissions/<root>`), `sha` (the entry commit), `tree` (the root's git tree id at it) and
`pr_ref`, beside the parts' `prover_sources_sha256`). A part
counts as passed only with its runner's final record (`stage: done`): a checkpoint left by a runner
that died (`benchmark: incomplete`), or any other value, is the runner's failure, an ERROR.

**The provisional ranking**:
`--rank` groups results by the entry (its name in the submissions repository, `entry.name`; the
binary's hash would let a no-op edit start a fresh group) and ranks an entry, once it has at least
three evaluations, by the median score of its last three (by `finished`), each REJECT,
PROVISIONAL or otherwise not comparable run counting as infinite, once per track, each run's score
of the track read through its `score.tracks` (`median_S` for `final`, from `S`, which orders the
rows, `median_S_every` for `every`, from `S_every`, where a run outside the track counts as infinite
too); it publishes
each entry's counts of evaluations, failures and unscored runs. ERROR results (the organiser's) are not
counted.
"""
import argparse
import collections
import hashlib
import json
import os
import statistics
import sys

ALL_PARTS = "calibrate,stream"
# one benchmark job; `split` is the same one job (the name callers pass)
PLANS = {"split": ["all"], "single": ["all"]}
ORGANISER_ERRORS = ("fingerprint", "lengths", "drift", "setup", "cache", "harness", "malformed")


def test_overrides(machine):
    """The test-only overrides a part's `machine` record shows (each weakens the sandbox: the memory
    caps' prlimit fallback, where every sandbox shares the runner's cgroup, `RF_ALLOW_PRLIMIT=1`;
    the host's /usr in the badge's sandbox, `RF_TEST_BADGE_HOST_ROOT=1`), [] if none."""
    m = machine if isinstance(machine, dict) else {}
    out = []
    if m.get("memcap_override"):
        out.append("memcap_override")
    if m.get("memcap") == "prlimit" and "memcap_override" not in out:
        out.append("memcap = prlimit")
    if m.get("badge_host_root"):
        out.append("badge_host_root")
    return out

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rfh.bench import (REJECT_STAGES, MalformedStream, Params, check_record, fingerprint,  # noqa: E402
                       fingerprint_problem, score)


def printable_text(text, limit=4000):
    """Untrusted text as printable ASCII, at most `limit` characters (its tail): every other
    character becomes `?`, backticks `'` (as `rfh.bench.printable`, without its code span)."""
    return "".join(c if 32 <= ord(c) < 127 or c == "\n" else "?" for c in text.replace("`", "'"))[-limit:]


def load_season(path):
    """(Params, None) for a well-formed season file, or (Params unchecked, the defect) when its
    `[stream]` shape is malformed; any other defect of the file raises as before."""
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
    ap.add_argument("--allow-test-overrides", action="store_true", help="tests only: see the module's doc")
    for k in ("--entry-name", "--entry-sha", "--entry-tree", "--pr-ref"):     # the measured entry (`measured_entry`)
        ap.add_argument(k, default=None)
    ap.add_argument("parts", nargs="*")
    a = ap.parse_args()
    if a.check_machine:
        p, defect = load_season(a.season)
        if defect:
            print(f"the season file's [stream] shape is malformed ({defect})")
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
                reason = f"the season file's [stream] shape is malformed ({defect}); {reason}"
        res = {"schema": "recursion.fast/v6/result-1", "season": p.name,
               "season_sha256": hashlib.sha256(open(a.season, "rb").read()).hexdigest(), "job": a.job,
               "harness_commit": a.harness_commit, "verdict": "ERROR", "comparable": False, "truncated": False,
               "organiser_error": kind, "parts": [], "stream": None,
               "reasons": [f"organiser ERROR ({kind}): {reason}"[:600]]}
        res["entry"] = measured_entry(a, None)
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
                  shape_defect=defect, allow_test_overrides=a.allow_test_overrides)
    res["entry"] = measured_entry(a, res.get("entry"))
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"VERDICT: {res['verdict']} ({len(res['parts'])} part(s), comparable {res['comparable']}, "
          f"fingerprint {'matches' if res['machine']['matches'] else 'does not match'})")
    return 0


def measured_entry(a, entry):
    """The result's `entry`: the parts' `prover_sources_sha256` and, from the evaluation as the
    attest job passes it, the measured entry: `sha` (the entry commit), `tree` (the git tree id of
    `submissions/<root>` at it, as the certificate job fetched it), `name` (`<repo>:<root path>`,
    the parts' own name when they ran) and `pr_ref` (if any), so the attested result names what it
    measured (review R3 M2; the submissions bot compares each field present, `verify-record.sh
    --entry-sha`)."""
    out = dict(entry) if isinstance(entry, dict) else {}
    for k, v in (("name", a.entry_name), ("sha", a.entry_sha), ("tree", a.entry_tree), ("pr_ref", a.pr_ref)):
        if v:
            out[k] = v
    return out or None


def combine(p, plan, season_sha, job, cert, parts, shape_defect=None, allow_test_overrides=False):
    """One entry's result from its certificate and its benchmark parts: the plan check, the verdict, the score.
    `shape_defect`: why the season file's `[stream]` shape is malformed, if it is. A part that ran
    under a test-only override (`test_overrides`) makes the verdict an organiser ERROR
    (`fingerprint`) unless `allow_test_overrides` (tests only), which records them instead."""
    res = {"schema": "recursion.fast/v6/result-1", "season": p.name, "season_sha256": season_sha, "job": job,
           "certificate": {k: cert.get(k) for k in ("status", "reasons", "provisional_reasons", "kernels",
                                                     "second_kernel", "kernel_runs", "gate", "badge_sha256", "claim",
                                                     "built_modules", "environment", "record_cache", "entry_build")},
           "parts": [], "reasons": list(cert.get("reasons", []))}
    res["stream"] = None
    for r in parts:
        part_rec = {k: r.get(k) for k in ("parts", "machine", "harness", "prover", "calib", "calibration",
                                          "benchmark", "stage", "reasons", "started", "finished", "comparable",
                                          "provisional")}
        if isinstance(part_rec.get("prover"), dict) and isinstance(part_rec["prover"].get("log"), str):
            # the build's output (gcc, as: `.error`/`.warning` text is the entry's): printable, capped (L3)
            part_rec["prover"] = dict(part_rec["prover"], log=printable_text(part_rec["prover"]["log"]))
        res["parts"].append(part_rec)
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
    # a part is passed only with its runner's final record (`stage: done`); a checkpoint left by a
    # runner that died says `incomplete` and is the runner's failure, never a pass (review R3 H3)
    status = [("error" if r.get("benchmark") in ("pass", "incomplete") and r.get("stage") != "done" else
               r.get("benchmark") if r.get("benchmark") in ("pass", "fail") else "error") for r in parts]
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
    overrides = sorted({o for r in parts for o in test_overrides(r.get("machine"))})
    if overrides and allow_test_overrides:
        res["test_overrides"] = overrides           # tests only (`--allow-test-overrides`)
    elif overrides and not fp_why:
        # a sandbox weakened for the tests is not the season's machine state (review LR5 L2)
        fp_why = "test-overrides"
    if fp_why == "test-overrides" and cert.get("status") in ("ok", "provisional"):
        verdict = "ERROR"
        res["reasons"].append(f"organiser ERROR: the benchmark ran under test-only overrides {overrides} (the "
                              "sandbox weakened for the tests): the machine is not in the season's state")
    elif fp_why and cert.get("status") in ("ok", "provisional"):
        # not the season's machine is the organiser's condition, never the entry's verdict
        verdict = "ERROR"
        why = (f"fingerprint {fp}, the season expects {p.fingerprint}" if fp_why == "mismatched"
               else m.get("fingerprint_reason") or "no fingerprint recorded")
        msg = f"organiser ERROR: the machine fingerprint is {fp_why} ({why})"
        if not any("machine fingerprint" in str(x) for x in res["reasons"]):
            res["reasons"].append(msg)
    # the season's stream shape: a stream of another shape is not comparable with any evaluation
    got = res["stream"].get("shape") if isinstance(res["stream"], dict) else None
    cert_ok = cert.get("status") in ("ok", "provisional")
    len_why = cert_ok and (shape_defect is not None or (res["stream"] is not None and got != p.shape()))
    if len_why and shape_defect is not None:
        verdict = "ERROR"
        res["reasons"].append(f"organiser ERROR: the season file's [stream] shape is malformed ({shape_defect})")
    elif len_why:
        verdict = "ERROR"
        res["reasons"].append(f"organiser ERROR: the stream's shape {got} is not the season's {p.shape()}")
    # the score, recomputed before the verdict and comparability are final: a passed run with no
    # stream record, or one not of the season's shape (`check_record`: steps 1 … M, three judged times
    # whose median is V, the final step within its caps) or that it cannot be computed from, is the
    # runner's fault, an organiser ERROR
    sc, malformed = None, False
    if verdict in ("ACCEPT", "PROVISIONAL"):
        try:
            check_record(p, res["stream"])
            sc = score(p, res["stream"])
        except MalformedStream as e:
            verdict, malformed = "ERROR", True
            res["reasons"].append(f"organiser ERROR: the stream's record is malformed ({e})")
    res["verdict"] = verdict
    if verdict == "REJECT":     # where it was rejected (`rfh.bench.REJECT_STAGES`): the certificate's first,
        # else the failed part's as its runner recorded it (None from a runner that recorded none)
        st = ("certificate" if cert.get("status") == "reject" else
              next((r.get("reject_stage") for r in parts if r.get("benchmark") == "fail"), None))
        res["reject_stage"] = st if st in REJECT_STAGES else None      # an unknown value: none
    if verdict == "ERROR":      # the named organiser error, if one is known (the bot never counts these against the author)
        kinds = [x.get("organiser_error") for x in [cert] + list(parts) if x.get("organiser_error") in ORGANISER_ERRORS]
        res["organiser_error"] = ("fingerprint" if fp_why else "lengths" if len_why else "malformed" if malformed
                                  else (kinds[0] if kinds else None))
    truncated = bool((res["stream"] or {}).get("truncated"))
    res["truncated"] = truncated
    res["comparable"] = verdict == "ACCEPT" and not plan_errors and not truncated
    res["prover_sha256"] = next(((r.get("prover") or {}).get("binary_sha256") for r in parts if r.get("prover")), None)
    res["entry"] = next((r.get("entry") for r in parts if r.get("entry")), None)
    if sc is not None:
        res["score"] = sc
    return res


def entry_key(r):
    """The entry a result belongs to: its name in the submissions repository (`entry.name`, which the
    evaluation workflow sets from the entry's root), else the hash of its prover sources. Not the
    binary's hash: a no-op edit gives a fresh binary, and a fresh group would reset the window."""
    e = r.get("entry") or {}
    return e.get("name") or e.get("prover_sources_sha256")


def track_score(r, track):
    """A result's score in `track`, read through its `score.tracks` (`final` → `S`, `every` →
    `S_every`), or None if the run is not in the track or the field is not a number."""
    sc = r.get("score") or {}
    field = (sc.get("tracks") or {}).get(track)
    v = sc.get(field) if isinstance(field, str) else None
    return v if type(v) in (int, float) else None


def rank(results):
    """The provisional ranking: per entry and per track, the median of its last three
    evaluations' scores, each REJECT, PROVISIONAL or otherwise not comparable run counting as
    infinite (none of them can help), and so does, per track, a run outside the track; an entry is
    ranked only once it has at least three counted evaluations. ERROR results (the organiser's) are
    not counted."""
    by = collections.defaultdict(list)
    for r in results:
        if r.get("verdict") == "ERROR" or not entry_key(r):
            continue
        by[entry_key(r)].append(r)
    rows = []
    inf = float("inf")
    for key, rs in by.items():
        rs.sort(key=lambda r: r.get("finished") or "")
        row = {"entry": key, "evaluations": len(rs), "failures": sum(r.get("verdict") == "REJECT" for r in rs),
               "not_scored": sum(r.get("verdict") == "ACCEPT" and not r.get("comparable") for r in rs)}
        for track, suffix in (("final", ""), ("every", "_every")):
            vals = [track_score(r, track) if r.get("verdict") == "ACCEPT" and r.get("comparable")
                    and track_score(r, track) is not None else inf for r in rs[-3:]]
            med = statistics.median(vals) if len(rs) >= 3 else None
            row["last_three" + suffix] = [v if v != inf else "failed or not scored" for v in vals]
            row["median_S" + suffix] = ("unranked (fewer than 3 evaluations)" if med is None
                                        else (med if med != inf else "failed"))
        rows.append(row)
    rows.sort(key=lambda x: (not isinstance(x["median_S"], float), x["median_S"] if isinstance(x["median_S"], float) else 0))
    return {"schema": "recursion.fast/v6/ranking-1",
            "rule": "per entry (its name in the submissions repository) and per track (final: S, every: S_every, each "
                    "read through score.tracks), the median score of its last three evaluations, a REJECT, PROVISIONAL "
                    "or not comparable run, or one outside the track, counting as infinite; ranked from three "
                    "evaluations, ordered by the track final (median_S)",
            "entries": rows}


if __name__ == "__main__":
    sys.exit(main())

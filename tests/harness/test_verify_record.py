#!/usr/bin/env python3
"""`harness/verify-record.sh` against a stand-in `gh` (review R3 M2, L2).

  python3 tests/harness/test_verify_record.py

A stub `gh attestation verify` on PATH prints an attestation signed at the result's harness commit
on a self-hosted runner. Then: a record result is accepted and its measured entry printed; one whose
`season_sha256` is not the hash of `harness/season.toml` is refused; with `--entry-sha` the result's
`entry.sha` must be that commit (also with `--provenance-only`).
"""
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SCRIPT = os.path.join(ROOT, "harness", "verify-record.sh")
FAILS = []


def check(cond, what):
    print(("ok   " if cond else "FAIL ") + what)
    if not cond:
        FAILS.append(what)


def main():
    tmp = tempfile.mkdtemp(prefix="rf-verify-record-", dir=os.environ.get("RF_TEST_TMP"))
    commit, sha = "c" * 40, "e" * 40
    bindir = os.path.join(tmp, "bin")
    os.makedirs(bindir)
    att = [{"verificationResult": {"signature": {"certificate": {
        "buildSignerDigest": commit, "runnerEnvironment": "self-hosted",
        "buildSignerURI": "https://github.com/scaraven/recursion.fast/.github/workflows/evaluate.yml@refs/heads/main"}}}}]
    open(os.path.join(bindir, "gh"), "w").write(f"#!/bin/sh\ncat <<'EOF'\n{json.dumps(att)}\nEOF\n")
    os.chmod(os.path.join(bindir, "gh"), 0o755)
    season = os.path.join(ROOT, "harness", "season.toml")
    shape = {k: tomllib.load(open(season, "rb"))["stream"][k] for k in ("M", "n")}
    good = {"harness_commit": commit, "season_sha256": hashlib.sha256(open(season, "rb").read()).hexdigest(),
            "verdict": "ACCEPT", "comparable": True, "stream": {"shape": shape},
            "runner": {"name": "rf-bench-1", "environment": "self-hosted", "labels": ["rf-bench"]},
            "entry": {"name": "o/subs:submissions/x", "sha": sha, "tree": "d" * 40, "pr_ref": "refs/pull/7/head"}}

    def vr(result, *flags):
        f = os.path.join(tmp, f"r{len(os.listdir(tmp))}.json")
        json.dump(result, open(f, "w"))
        p = subprocess.run(["bash", SCRIPT, *flags, f], capture_output=True, text=True, timeout=60,
                           env=dict(os.environ, PATH=bindir + os.pathsep + os.environ["PATH"]))
        return p.returncode, (p.stdout + p.stderr).strip()

    code, out = vr(good)
    check(code == 0 and sha in out and "d" * 40 in out and "o/subs:submissions/x" in out, f"a record result is accepted, its entry printed: {out[-200:]}")
    code, out = vr(dict(good, season_sha256="0" * 64))
    check(code != 0 and "season_sha256" in out, f"a result of another season file is refused: {out[-160:]}")
    code, out = vr(good, "--entry-sha", sha)
    check(code == 0, f"--entry-sha of the measured commit: accepted ({out[-120:]})")
    code, out = vr(good, "--entry-sha", "f" * 40)
    check(code != 0 and "measured the entry commit" in out, f"--entry-sha of another commit: refused ({out[-160:]})")
    code, out = vr(dict(good, verdict="REJECT"), "--provenance-only", "--entry-sha", "f" * 40)
    check(code != 0 and "measured the entry commit" in out, f"--provenance-only checks --entry-sha too ({out[-160:]})")
    code, out = vr(dict(good, verdict="REJECT"), "--provenance-only", "--entry-sha", sha)
    check(code == 0 and "provenance only" in out, f"--provenance-only of any verdict, the right commit: {out[-160:]}")
    print(f"{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())

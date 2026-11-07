#!/usr/bin/env python3
"""Tests of the job policy (image/guest/rf-job-policy.py with infra/job-allowlist.json): every
allowed case passes, and the refused ones fail. Runs the policy as the hook does (a subprocess
with a simulated environment), so the exit code and the RF-HOOK line are what a runner sees.

  python3 -I infra/tests/test_job_policy.py
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
POLICY = os.path.join(HERE, "..", "image", "guest", "rf-job-policy.py")
ALLOW = os.path.join(HERE, "..", "job-allowlist.json")
R = "scaraven/recursion.fast-submissions"
WF = lambda w, ref="refs/heads/main": f"{R}/.github/workflows/{w}@{ref}"  # noqa: E731


def run(env, slot="light"):
    p = subprocess.run([sys.executable, "-I", POLICY, ALLOW, slot], env={"PATH": "/usr/bin:/bin", **env},
                       capture_output=True, text=True)
    line = next((l for l in p.stdout.splitlines() if l.startswith("RF-HOOK ")), None)
    rec = json.loads(line[8:]) if line else None
    return p.returncode, rec


def job(event, wf, ref="refs/heads/main", repo=R, wref=None):
    return {"GITHUB_EVENT_NAME": event, "GITHUB_REPOSITORY": repo,
            "GITHUB_WORKFLOW_REF": wref if wref is not None else WF(wf), "GITHUB_REF": ref,
            "GITHUB_RUN_ID": "1", "GITHUB_JOB": "j", "RUNNER_NAME": "rf-bench-x"}


# (name, slot type, environment)
ALLOWED = [
    ("bench: evaluate.yml's jobs (caller evaluate-next.yml) on schedule", "bench", job("schedule", "evaluate-next.yml")),
    ("bench: evaluate-next on workflow_dispatch", "bench", job("workflow_dispatch", "evaluate-next.yml")),
    ("light: evaluate-next (plan, attest, the bot's jobs) on schedule", "light", job("schedule", "evaluate-next.yml")),
    ("light: evaluate-next on workflow_dispatch", "light", job("workflow_dispatch", "evaluate-next.yml")),
    ("light: intake on pull_request_target", "light", job("pull_request_target", "intake.yml")),
    ("light: intake on workflow_dispatch", "light", job("workflow_dispatch", "intake.yml")),
    ("light: pages on push to main", "light", job("push", "pages.yml")),
    ("light: pages on workflow_dispatch", "light", job("workflow_dispatch", "pages.yml")),
    ("light: pin-check on push to main", "light", job("push", "pin-check.yml")),
    ("light: sync on push to main", "light", job("push", "sync.yml")),
    ("light: sync on schedule", "light", job("schedule", "sync.yml")),
    ("light: sync on workflow_dispatch", "light", job("workflow_dispatch", "sync.yml")),
]

REFUSED = [
    ("pull_request (a fork's own workflow)", "light", job("pull_request", "intake.yml")),
    ("pull_request on bench", "bench", job("pull_request", "evaluate-next.yml")),
    ("pull_request_review", "light", job("pull_request_review", "intake.yml")),
    ("pull_request_review_comment", "light", job("pull_request_review_comment", "intake.yml")),
    ("issue_comment", "light", job("issue_comment", "intake.yml")),
    ("workflow_run", "light", job("workflow_run", "evaluate-next.yml")),
    ("merge_group", "light", job("merge_group", "pages.yml")),
    ("no event", "light", {k: v for k, v in job("push", "pages.yml").items() if k != "GITHUB_EVENT_NAME"}),
    ("bench: a bot workflow (intake) on its own event", "bench", job("pull_request_target", "intake.yml")),
    ("bench: sync on schedule", "bench", job("schedule", "sync.yml")),
    ("bench: evaluate-next on pull_request_target", "bench", job("pull_request_target", "evaluate-next.yml")),
    ("light: pin-check on pull_request_target", "light", job("pull_request_target", "pin-check.yml")),
    ("light: evaluate-next on push", "light", job("push", "evaluate-next.yml")),
    ("an unknown slot type", "gpu", job("schedule", "evaluate-next.yml")),
    ("no slot type", "", job("schedule", "evaluate-next.yml")),
    ("another repository", "light", job("workflow_dispatch", "sync.yml", repo="attacker/recursion.fast-submissions")),
    ("our workflow name in another repository's path", "light",
     job("workflow_dispatch", "sync.yml", wref="attacker/x/.github/workflows/sync.yml@refs/heads/main")),
    ("a workflow not on the list", "light", job("workflow_dispatch", "evil.yml")),
    ("our workflow on another branch (dispatch)", "bench", job("workflow_dispatch", "x", wref=WF("evaluate-next.yml", "refs/heads/feature"))),
    ("our workflow on a tag", "light", job("workflow_dispatch", "x", wref=WF("sync.yml", "refs/tags/v1"))),
    ("our workflow at a commit", "light", job("workflow_dispatch", "x", wref=WF("sync.yml", "0123456789abcdef0123456789abcdef01234567"))),
    ("pull_request_target from a PR to another base branch", "light",
     job("pull_request_target", "x", wref=WF("intake.yml", "refs/heads/release"))),
    ("push to another branch", "light", job("push", "pages.yml", ref="refs/heads/feature")),
    ("push of a tag", "light", job("push", "pages.yml", ref="refs/tags/v1")),
    ("the reusable workflow called directly", "bench", job("workflow_dispatch", "x",
     wref="scaraven/recursion.fast/.github/workflows/evaluate.yml@refs/heads/main")),
    ("a workflow in a subdirectory", "light", job("workflow_dispatch", "x", wref=f"{R}/.github/workflows/sub/sync.yml@refs/heads/main")),
    ("a lookalike name", "light", job("workflow_dispatch", "x", wref=f"{R}/.github/workflows/sync.yml.evil@refs/heads/main")),
    ("an empty environment", "light", {}),
]


def main():
    fails = 0
    for name, slot, env in ALLOWED:
        rc, rec = run(env, slot)
        good = rc == 0 and rec and rec["decision"] == "allowed"
        fails += not good
        print(f"{'ok  ' if good else 'FAIL'} allowed: {name} ({rec and rec['reason']})")
    for name, slot, env in REFUSED:
        rc, rec = run(env, slot)
        good = rc != 0 and rec and rec["decision"] == "refused"
        fails += not good
        print(f"{'ok  ' if good else 'FAIL'} refused: {name} ({rec and rec['reason']})")
    # a missing allowlist refuses everything
    p = subprocess.run([sys.executable, "-I", POLICY, "/nonexistent.json", "light"], env=job("push", "pages.yml"),
                       capture_output=True, text=True)
    good = p.returncode != 0 and "refused" in p.stdout
    fails += not good
    print(f"{'ok  ' if good else 'FAIL'} refused: no allowlist file")
    print(f"{len(ALLOWED)} allowed and {len(REFUSED) + 1} refused cases, {fails} failure(s)")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())

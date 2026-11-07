#!/usr/bin/env python3
"""The job policy (root-owned in the image; run by rf-job-started.sh, the runner's job-started
hook, before any step of a job). Exit 0 lets the job run; exit 1 refuses it (the hook then powers
the VM off, so no step of a refused job runs, not even one with `if: always()`).

  rf-job-policy.py [ALLOWLIST [SLOT_TYPE]]
      ALLOWLIST: default /etc/rf/job-allowlist.json (infra/job-allowlist.json)
      SLOT_TYPE: bench or light; default the content of /run/rf/slot-type (written by rf-job from
      the VM's seed)

A job is allowed only if
  - GITHUB_REPOSITORY is "repository";
  - GITHUB_WORKFLOW_REF is "<repository>/.github/workflows/<w>@<ref>" for a workflow w listed
    under "slot_types"[SLOT_TYPE], and GITHUB_EVENT_NAME is one of w's events (never
    pull_request, pull_request_review*, issue_comment, workflow_run unless listed, and none is).
    For a job of a reusable workflow (the core's evaluate.yml), GitHub sets GITHUB_WORKFLOW_REF to
    the *calling* workflow, so evaluate-next.yml on main is what is checked; it pins evaluate.yml
    by commit SHA, so main decides which reusable workflow runs;
  - for a push, GITHUB_REF is "ref".
It prints one line `RF-HOOK {json}` with the decision and the values it judged.
"""
import json
import os
import sys

KEYS = ("GITHUB_EVENT_NAME", "GITHUB_REPOSITORY", "GITHUB_WORKFLOW_REF", "GITHUB_REF", "GITHUB_RUN_ID",
        "GITHUB_RUN_ATTEMPT", "GITHUB_JOB", "GITHUB_SHA", "GITHUB_ACTOR", "RUNNER_NAME")


def decide(env, allow, slot_type):
    """(allowed, reason) for the job whose GitHub variables are in env, on a VM of slot_type."""
    ev, repo = env.get("GITHUB_EVENT_NAME", ""), env.get("GITHUB_REPOSITORY", "")
    wref, ref = env.get("GITHUB_WORKFLOW_REF", ""), env.get("GITHUB_REF", "")
    table = allow["slot_types"].get(slot_type)
    if table is None:
        return False, f"unknown slot type {slot_type!r}"
    if repo != allow["repository"]:
        return False, f"repository {repo!r} is not {allow['repository']!r}"
    prefix, suffix = f"{allow['repository']}/.github/workflows/", f"@{allow['ref']}"
    wf = wref[len(prefix):-len(suffix)] if wref.startswith(prefix) and wref.endswith(suffix) else None
    if wf not in table:
        return False, f"workflow {wref!r} is not one of the {slot_type} slots' workflows on {allow['ref']}"
    if ev not in table[wf]:
        return False, f"event {ev!r} is not allowed for {wf} on a {slot_type} slot"
    if ev == "push" and ref != allow["ref"]:
        return False, f"push to {ref!r}, not {allow['ref']!r}"
    return True, "allowed"


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "/etc/rf/job-allowlist.json"
    if len(sys.argv) > 2:
        slot_type = sys.argv[2]
    else:
        try:
            slot_type = open("/run/rf/slot-type").read().strip()
        except OSError:
            slot_type = ""
    try:
        allow = json.load(open(path))
    except (OSError, ValueError) as e:
        ok, why = False, f"no allowlist ({e})"
    else:
        ok, why = decide(os.environ, allow, slot_type)
    rec = {"decision": "allowed" if ok else "refused", "reason": why, "slot_type": slot_type,
           **{k.lower(): os.environ.get(k, "")[:200] for k in KEYS}}
    print("RF-HOOK " + json.dumps(rec, sort_keys=True), flush=True)
    if not ok:
        print(f"::error title=recursion.fast runner::this runner runs only the competition's own workflows: {why}", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

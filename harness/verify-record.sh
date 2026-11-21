#!/usr/bin/env bash
# Checks a result's provenance, its runner and its verdict, or says why not (TRUSTED;
# AGENTS.md §8). It is a necessary condition for a record, not the record rule: the submissions bot
# applies that rule per track (`S_t < (1 - margin) · S_t,record`, the tracks `final` and `every`, against
# the track's standing record at the pin) on a result this script accepted. Needs `gh` ≥ 2.49 and
# a GitHub token able to read the attestations of the submissions repository.
#
#   harness/verify-record.sh [--entry-sha SHA] result.json                     1-6
#   harness/verify-record.sh --provenance-only [--entry-sha SHA] result.json   1-2, 6 (any verdict:
#                                                            the bot's check of every result it publishes)
#
# 1. `gh attestation verify`: the file is attested by the core's reusable workflow
#    (`--signer-workflow scaraven/recursion.fast/.github/workflows/evaluate.yml`), in the repository
#    `scaraven/recursion.fast-submissions`, on a self-hosted runner (the certificate's
#    `runnerEnvironment`), i.e. a runner registered to that repository, which only the owner's
#    server can register;
# 2. the attestation's signer digest, the commit the reusable workflow ran at (its
#    `job_workflow_ref`'s commit), equals the result's `harness_commit`: `--signer-workflow` alone
#    matches the workflow's path, not its ref;
# 3. the result records the organiser's runner (`runner`): environment `self-hosted`, a name starting
#    with `rf-`, the label `rf-bench` (the server registers its runners with exactly the one label
#    `rf-bench` or `rf-light`): a consistency check of what the server
#    wrote, not evidence (the labels prove nothing; 1 is the evidence);
# 4. the verdict is ACCEPT and the result is comparable (all planned parts present, the stream not
#    truncated; a machine that is not the season's is an ERROR, never an ACCEPT), with no test-only
#    override recorded (`test_overrides`, the tests' `aggregate.py --allow-test-overrides`);
# 5. the stream's shape (`stream.shape`: `M`, `n`) is the season's `[stream]` shape, and the
#    result's `season_sha256` is the sha256 of `season.toml` beside this script (run it from the
#    core checked out at `harness_commit`): the evaluation read that season file, no other;
# 6. it prints the measured entry (`entry`: `name`, `sha`, `tree`, `pr_ref`, which the attest job
#    wrote from the evaluation); with `--entry-sha SHA` the result's `entry.sha` must be SHA
#    (the bot passes the commit it asked to be evaluated).
# The trust anchor is the organiser's server: GitHub attests the workflow, the commit and the
# self-hosted environment (1-2), and a third party can check only those.
set -euo pipefail
ONLY=0; ESHA=
while [[ $# -gt 1 ]]; do
  case "$1" in
    --provenance-only) ONLY=1; shift ;;
    --entry-sha) ESHA=${2:?--entry-sha needs a SHA}; shift 2 ;;
    *) break ;;
  esac
done
R=${1:?usage: verify-record.sh [--provenance-only] [--entry-sha SHA] result.json}
commit=$(python3 -I -c 'import json, sys; print(json.load(open(sys.argv[1])).get("harness_commit") or "")' "$R")
[[ "$commit" =~ ^[0-9a-f]{40}$ ]] || { echo "verify-record: no full harness_commit in $R"; exit 1; }
out=$(gh attestation verify "$R" --repo scaraven/recursion.fast-submissions \
  --signer-workflow scaraven/recursion.fast/.github/workflows/evaluate.yml --format json)
SEASON="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/season.toml"
ATT=$out python3 -I - "$R" "$commit" "$ONLY" "$SEASON" "$ESHA" <<'PY'
import hashlib, json, os, sys, tomllib
path, commit, only, season, esha = sys.argv[1], sys.argv[2], sys.argv[3] == "1", sys.argv[4], sys.argv[5]
att = json.loads(os.environ["ATT"])
certs = [a["verificationResult"]["signature"]["certificate"] for a in att]
digests = {c.get("buildSignerDigest") for c in certs}
uris = {c.get("buildSignerURI") for c in certs}
if digests != {commit}:
    sys.exit(f"verify-record: the attesting workflow ran at {sorted(map(str, digests))}, the result says {commit}")
envs = {c.get("runnerEnvironment") for c in certs}
if envs != {"self-hosted"}:
    sys.exit(f"verify-record: attested on {sorted(map(str, envs))}, not the organiser's self-hosted runner")
r = json.load(open(path))
e = r.get("entry") if isinstance(r.get("entry"), dict) else {}
measured = {k: e.get(k) for k in ("name", "sha", "tree", "pr_ref")}
if esha and e.get("sha") != esha:
    sys.exit(f"verify-record: the result measured the entry commit {e.get('sha')!r}, not {esha}")
if only:
    print(f"verify-record: OK, attested by {sorted(uris)[0]}, harness {commit}, verdict {r.get('verdict')}, "
          f"comparable {r.get('comparable')}, entry {measured} (provenance only)")
    sys.exit(0)
run = r.get("runner") if isinstance(r.get("runner"), dict) else {}
name, labels = run.get("name"), run.get("labels") if isinstance(run.get("labels"), list) else []
if not (run.get("environment") == "self-hosted" and isinstance(name, str) and name.startswith("rf-")
        and labels == ["rf-bench"]):
    sys.exit(f"verify-record: the benchmark's runner {name!r} ({run.get('environment')}, labels {labels}) "
             "is not the organiser's rf-bench runner")
if r.get("verdict") != "ACCEPT" or not r.get("comparable"):
    sys.exit(f"verify-record: verdict {r.get('verdict')}, comparable {r.get('comparable')}: not a record")
if r.get("test_overrides"):
    sys.exit(f"verify-record: aggregated with the tests' --allow-test-overrides ({r['test_overrides']}): not a record")
if r.get("season_sha256") != hashlib.sha256(open(season, "rb").read()).hexdigest():
    sys.exit(f"verify-record: the result's season_sha256 {r.get('season_sha256')!r} is not the hash of {season}: "
             "not the season's evaluation")
s = tomllib.load(open(season, "rb"))["stream"]
want = {k: s.get(k) for k in ("M", "n")}
st = r.get("stream") if isinstance(r.get("stream"), dict) else {}
if st.get("shape") != want:
    sys.exit(f"verify-record: the stream's shape {st.get('shape')} is not the season's {want} (harness/season.toml): not comparable")
print(f"verify-record: OK, attested by {sorted(uris)[0]}, harness {commit}, runner {name}, verdict ACCEPT, "
      f"comparable, the season's file and stream shape, entry {measured} (the record rule is the bot's)")
PY

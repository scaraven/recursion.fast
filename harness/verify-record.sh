#!/usr/bin/env bash
# Checks a result's provenance, its runner and its verdict, or says why not (TRUSTED;
# AGENTS.md §8). It is a necessary condition for a record, not the record rule: the submissions bot
# applies that rule (`S < (1 - margin) · S_record`, against the standing record at the pin) on a
# result this script accepted. Needs `gh` ≥ 2.49 and a GitHub token able to read the attestations
# of the submissions repository.
#
#   harness/verify-record.sh result.json                     1-5
#   harness/verify-record.sh --provenance-only result.json   1-2 (any verdict: the bot's check of
#                                                            every result it publishes)
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
#    truncated; a machine that is not the season's is an ERROR, never an ACCEPT);
# 5. the stream's chain lengths (`stream.lengths`) are the season's fixed `[stream] lengths`, read
#    from `season.toml` beside this script (run it from the core checked out at `harness_commit`).
# The trust anchor is the organiser's server: GitHub attests the workflow, the commit and the
# self-hosted environment (1-2), and a third party can check only those.
set -euo pipefail
ONLY=0; [[ "${1:-}" == --provenance-only ]] && { ONLY=1; shift; }
R=${1:?usage: verify-record.sh [--provenance-only] result.json}
commit=$(python3 -I -c 'import json, sys; print(json.load(open(sys.argv[1])).get("harness_commit") or "")' "$R")
[[ "$commit" =~ ^[0-9a-f]{40}$ ]] || { echo "verify-record: no full harness_commit in $R"; exit 1; }
out=$(gh attestation verify "$R" --repo scaraven/recursion.fast-submissions \
  --signer-workflow scaraven/recursion.fast/.github/workflows/evaluate.yml --format json)
SEASON="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/season.toml"
ATT=$out python3 -I - "$R" "$commit" "$ONLY" "$SEASON" <<'PY'
import json, os, sys, tomllib
path, commit, only, season = sys.argv[1], sys.argv[2], sys.argv[3] == "1", sys.argv[4]
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
if only:
    print(f"verify-record: OK, attested by {sorted(uris)[0]}, harness {commit}, verdict {r.get('verdict')}, "
          f"comparable {r.get('comparable')} (provenance only)")
    sys.exit(0)
run = r.get("runner") if isinstance(r.get("runner"), dict) else {}
name, labels = run.get("name"), run.get("labels") if isinstance(run.get("labels"), list) else []
if not (run.get("environment") == "self-hosted" and isinstance(name, str) and name.startswith("rf-")
        and labels == ["rf-bench"]):
    sys.exit(f"verify-record: the benchmark's runner {name!r} ({run.get('environment')}, labels {labels}) "
             "is not the organiser's rf-bench runner")
if r.get("verdict") != "ACCEPT" or not r.get("comparable"):
    sys.exit(f"verify-record: verdict {r.get('verdict')}, comparable {r.get('comparable')}: not a record")
want = tomllib.load(open(season, "rb"))["stream"]["lengths"]
st = r.get("stream") if isinstance(r.get("stream"), dict) else {}
if st.get("lengths") != want:
    sys.exit(f"verify-record: the stream's chain lengths are not the season's [stream] lengths (harness/season.toml): not comparable")
print(f"verify-record: OK, attested by {sorted(uris)[0]}, harness {commit}, runner {name}, verdict ACCEPT, "
      "comparable, the season's chain lengths (the record rule is the bot's)")
PY

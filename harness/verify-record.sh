#!/usr/bin/env bash
# Accepts a result as a record, or says why not (TRUSTED; V4-A1, RF-m1). Needs `gh` ≥ 2.49 and a
# GitHub token able to read the attestations of the submissions repository.
#
#   harness/verify-record.sh result.json
#
# 1. `gh attestation verify`: the file is attested by the core's reusable workflow
#    (`--signer-workflow scaraven/recursion.fast/.github/workflows/evaluate.yml`), in a repository
#    owned by `scaraven`, on a GitHub-hosted runner (`--deny-self-hosted-runners`);
# 2. the attestation's signer digest, the commit the reusable workflow ran at (its
#    `job_workflow_ref`'s commit), equals the result's `harness_commit`: `--signer-workflow` alone
#    matches the workflow's path, not its ref;
# 3. the verdict is ACCEPT and the result is comparable (all planned parts present, one CPU model).
set -euo pipefail
R=${1:?usage: verify-record.sh result.json}
commit=$(python3 -I -c 'import json, sys; print(json.load(open(sys.argv[1])).get("harness_commit") or "")' "$R")
[[ "$commit" =~ ^[0-9a-f]{40}$ ]] || { echo "verify-record: no full harness_commit in $R"; exit 1; }
out=$(gh attestation verify "$R" --owner scaraven \
  --signer-workflow scaraven/recursion.fast/.github/workflows/evaluate.yml --deny-self-hosted-runners --format json)
ATT=$out python3 -I - "$R" "$commit" <<'PY'
import json, os, sys
path, commit = sys.argv[1], sys.argv[2]
att = json.loads(os.environ["ATT"])
digests = {a["verificationResult"]["signature"]["certificate"].get("buildSignerDigest") for a in att}
uris = {a["verificationResult"]["signature"]["certificate"].get("buildSignerURI") for a in att}
if digests != {commit}:
    sys.exit(f"verify-record: the attesting workflow ran at {sorted(map(str, digests))}, the result says {commit}")
r = json.load(open(path))
if r.get("verdict") != "ACCEPT" or not r.get("comparable"):
    sys.exit(f"verify-record: verdict {r.get('verdict')}, comparable {r.get('comparable')}: not a record")
print(f"verify-record: OK, a record: attested by {sorted(uris)[0]}, harness {commit}, verdict ACCEPT")
PY

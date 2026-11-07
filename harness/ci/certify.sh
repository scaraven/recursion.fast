#!/usr/bin/env bash
# The certificate step of `.github/workflows/evaluate.yml` (TRUSTED; CI).
# Run from the job's workspace, which holds `core/` (this repository at the resolved commit) and
# `entry/` (the fetched entry); writes `cert.json`, `cert-out/` and the step output `status`.
#   harness/ci/certify.sh [evaluate.py cert options, e.g. --nanoda, --export-build DIR]
# Environment: SEASON (relative to core/), ORG_HIT, KERNELS_HIT, ORG_KEY, KERNELS_KEY (the cache
# lookups), RECORD_KEY (the restored record build's key, or empty), RECORD_MANIFEST (the attested
# record's `entry_build.manifest_sha256`, or empty: then nothing is restored), RUNNER_TEMP,
# GITHUB_OUTPUT.
set -eo pipefail
mkdir -p cert-out
if [[ "$ORG_HIT" != true || "$KERNELS_HIT" != true ]]; then
  # a missing cache is the organiser's failure, never the entry's: a signalled ERROR with its
  # reason, aggregated and attested like any result
  msg="harness error: the organiser's environment is not in the cache ($ORG_KEY: ${ORG_HIT:-miss}, $KERNELS_KEY: ${KERNELS_HIT:-miss}); a setup job's save failed or the cache was evicted"
  echo "::error title=organiser cache missing::$msg"
  python3 -I -c 'import json, sys; json.dump({"status": "error", "organiser_error": "cache", "reasons": [sys.argv[1]]}, open("cert.json", "w"))' "$msg"
  echo "status=error" >> "$GITHUB_OUTPUT"
  cp cert.json cert-out/
  exit 0
fi
# a rejected entry is a result (exit 1, cert.json says `reject`; a harness error says
# `error`, exit 2); a crash (no cert.json) fails the job, and any unreadable status counts as `reject`
rc=0
seed=()
if [[ -n "${RECORD_KEY:-}" && -s "$RUNNER_TEMP/record-build/manifest.json" ]]; then
  seed=(--record-cache "$RUNNER_TEMP/record-build" --record-cache-key "$RECORD_KEY"
        --record-manifest-sha256 "${RECORD_MANIFEST:-}")
fi
python3 -I core/harness/evaluate.py cert --entry entry --org "$PWD/core" --work "$RUNNER_TEMP/cert" \
  --season "core/$SEASON" --out cert.json "${seed[@]}" "$@" || rc=$?
status=$(python3 -I -c 'import json; print(json.load(open("cert.json"))["status"])' 2>/dev/null || echo reject)
echo "status=$status" >> "$GITHUB_OUTPUT"
[[ -s cert.json ]] || { echo "evaluate.py cert crashed (exit $rc)"; exit 1; }
cp cert.json cert-out/ && cp -r "$RUNNER_TEMP/cert/badge" cert-out/ 2>/dev/null || true

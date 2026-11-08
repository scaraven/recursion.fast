#!/usr/bin/env bash
# elan for an evaluation job (TRUSTED; CI). On the organiser's runners (self-hosted) elan is part of
# the evaluation image: a missing one is an image fault, an organiser error, and nothing is
# downloaded there. Only on a GitHub-hosted runner (RF_RUNNER_ENVIRONMENT = runner.environment =
# github-hosted, e.g. a test run of the workflow) is the installer fetched, at a pinned commit and
# refused unless its sha256 is the one recorded here.
set -euo pipefail
E="$HOME/.elan/bin"
if ! command -v elan >/dev/null 2>&1 && [[ ! -x "$E/elan" ]]; then
  if [[ "${RF_RUNNER_ENVIRONMENT:-}" != github-hosted ]]; then
    echo "::error title=organiser image::elan is not installed on this runner (${RF_RUNNER_ENVIRONMENT:-unknown}); the evaluation image must carry it (an organiser error)"
    echo "missing=true" >> "${GITHUB_OUTPUT:-/dev/null}"     # the attest job names it a setup error
    exit 1
  fi
  commit=9605b24b08cf68b78dce0014b6fa01be1f8e2cee
  sha=a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53
  t=$(mktemp)
  curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/$commit/elan-init.sh" -o "$t"
  echo "$sha  $t" | sha256sum -c --quiet || { echo "elan.sh: elan-init.sh at $commit is not the pinned file"; exit 1; }
  sh "$t" -y --default-toolchain none
  rm -f "$t"
fi
if [[ -d "$E" ]]; then echo "$E" >> "${GITHUB_PATH:-/dev/null}"; fi

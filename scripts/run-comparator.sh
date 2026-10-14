#!/usr/bin/env bash
# Toy comparator runs through the production harness (A6-G0): positive (default kernel + nanoda, then
# the gate), negative (one rendered image word changed). The v0.3 version ran the comparator with the
# insecure fake landrun in the organiser tree after building the solution there (A6 scenario B).
set -euo pipefail
cd "$(dirname "$0")/.."
ORG=${CI_ORG:-$PWD/.lake/org}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/sol" "$T/bad"; cp audit/ToySolution.lean "$T/sol/"; cp audit/ToySolutionBad.lean "$T/bad/"
scripts/harness.sh --org "$ORG" --gate RecursionFast.Challenge.certified --computable RecursionFast.Challenge.protocol \
  audit/ToyChallenge.lean "$T/sol" audit/comparator-nanoda.json
scripts/harness.sh --org "$ORG" audit/ToyChallenge.lean "$T/bad" audit/comparator-bad.json || true

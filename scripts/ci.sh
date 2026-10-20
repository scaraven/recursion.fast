#!/usr/bin/env bash
# CI of the v3 trusted core. Runs the checks the tree supports today, in order, and stops at the
# first failure. The full harness order of DESIGN-v3 §7.6 (source rule on a submission, comparator
# in a fresh sandboxed tree, organiser package and olean manifest, gate, badge build, runner) is
# stage S3's; what S3 adds goes here.
#   1  hygiene:     no sorry/admit/native_decide/implemented_by/extern/csimp/axiom under RecursionFast/
#                   (a text lint; the gate is the binding check)
#   2  source rule: its fixtures (tests/source-rule/check.sh: every rejected form reported, the allowed pass)
#   3  build:       contract, library, controls (the kernel-evaluated controls), gate, axiomaudit
#   4  axiom audit: every RecursionFast.* declaration within propext, Classical.choice, Quot.sound
#   5  gate rule 4: its fixtures (tests/gate/check.sh: the witness-sending and backdoor submissions
#                   pass, a noncomputable `ext` is rejected; against a manifest of this tree)
#   6  line budget: Contract.lean, Contract/*.lean, Contract/Hash/Blake2s.lean ≤ 500 code lines
#
# Usage: scripts/ci.sh (no arguments).
# Logs: logs/ci/ (gitignored).
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=logs/ci; mkdir -p "$LOG"
BUDGET=500
t0=$(date +%s)
step() { echo "== $1 ($(( $(date +%s) - t0 )) s)"; }

step "1 hygiene"
scripts/check-hygiene.sh | tee "$LOG/hygiene.log"
step "2 source rule"
tests/source-rule/check.sh | tee "$LOG/source-rule.log"
step "3 build"
lake build RecursionFastContract RecursionFastLibrary RecursionFastControls gate axiomaudit \
  > "$LOG/build.log" 2>&1; tail -1 "$LOG/build.log"
step "4 axiom audit"
lake exe axiomaudit > "$LOG/axiomaudit.log" 2>&1; tail -2 "$LOG/axiomaudit.log"
step "5 gate rule 4"
tests/gate/check.sh | tee "$LOG/gate.log"
step "6 line budget"
python3 scripts/loc.py RecursionFast/Contract.lean RecursionFast/Contract/*.lean \
  RecursionFast/Contract/Hash/Blake2s.lean > "$LOG/loc.log"
code=$(awk '/^TOTAL/ {print $5}' "$LOG/loc.log")
echo "trusted code lines: $code (budget $BUDGET)"
[ "$code" -le "$BUDGET" ] || { echo "line budget exceeded"; exit 1; }
echo "CI passed ($(( $(date +%s) - t0 )) s)"

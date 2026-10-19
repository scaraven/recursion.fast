#!/usr/bin/env bash
# CI of the v3 trusted core. Runs the checks the tree supports today, in order, and stops at the
# first failure. The full harness order of DESIGN-v3 §7.6 (source rule on a submission, comparator
# in a fresh sandboxed tree, organiser package and olean manifest, gate, badge build, runner) is
# stage S3's; what S3 adds goes here.
#   1  vendor:      RecursionFast/Vendor/RiscvZkvm is byte-identical to riscv-zkvm 6810fc1
#   2  hygiene:     no sorry/admit/native_decide/implemented_by/extern/csimp/axiom under RecursionFast/
#                   (a text lint; the gate is the binding check)
#   3  source rule: its fixtures (tests/source-rule/check.sh: every rejected form reported, the allowed pass)
#   4  build:       contract, library, controls (the kernel-evaluated controls), gate, axiomaudit
#   5  axiom audit: every RecursionFast.* declaration within propext, Classical.choice, Quot.sound
#   6  line budget: Contract.lean, Contract/*.lean, Contract/Hash/Blake2s.lean ≤ 500 code lines
#
#   scripts/ci.sh [RISCV_ZKVM_CHECKOUT]     (without the argument, check-vendor.sh clones upstream)
# Logs: logs/ci/ (gitignored).
set -euo pipefail
cd "$(dirname "$0")/.."
LOG=logs/ci; mkdir -p "$LOG"
BUDGET=500
t0=$(date +%s)
step() { echo "== $1 ($(( $(date +%s) - t0 )) s)"; }

step "1 vendor"
scripts/check-vendor.sh "$@" > "$LOG/vendor.log"; tail -1 "$LOG/vendor.log"
step "2 hygiene"
scripts/check-hygiene.sh | tee "$LOG/hygiene.log"
step "3 source rule"
tests/source-rule/check.sh | tee "$LOG/source-rule.log"
step "4 build"
lake build RecursionFastContract RecursionFastLibrary RecursionFastControls gate axiomaudit \
  > "$LOG/build.log" 2>&1; tail -1 "$LOG/build.log"
step "5 axiom audit"
lake exe axiomaudit > "$LOG/axiomaudit.log" 2>&1; tail -2 "$LOG/axiomaudit.log"
step "6 line budget"
python3 scripts/loc.py RecursionFast/Contract.lean RecursionFast/Contract/*.lean \
  RecursionFast/Contract/Hash/Blake2s.lean > "$LOG/loc.log"
code=$(awk '/^TOTAL/ {print $5}' "$LOG/loc.log")
echo "trusted code lines: $code (budget $BUDGET)"
[ "$code" -le "$BUDGET" ] || { echo "line budget exceeded"; exit 1; }
echo "CI passed ($(( $(date +%s) - t0 )) s)"

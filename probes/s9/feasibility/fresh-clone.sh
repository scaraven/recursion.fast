#!/usr/bin/env bash
# S9 feasibility: reproduce the repository from a fresh clone following only CLAUDE.md/README.md.
#   fresh-clone.sh DEST LOGDIR
# Steps (each timed with /usr/bin/time -v; load average recorded before each):
#   1 git clone   2 scripts/setup-clean.sh <local Clean checkout> (offline)   3 packages symlink
#   4 default `lake build`   5 scripts/ci.sh <riscv-zkvm checkout>
set -uo pipefail
SRC=/home/devops/Verified-zkEVM/recursion.fast
DEST=$1; L=$2; mkdir -p "$L"
run() { local n=$1; shift; echo "== $(date +%T) step $n: $* (load $(cut -d' ' -f1-3 /proc/loadavg))" | tee -a "$L/steps.log"
  /usr/bin/time -v -o "$L/time-$n.txt" "$@" > "$L/out-$n.log" 2>&1; local rc=$?
  echo "   rc=$rc wall=$(grep 'Elapsed (wall' "$L/time-$n.txt" | awk '{print $NF}') user=$(grep 'User time' "$L/time-$n.txt" | awk '{print $NF}') sys=$(grep 'System time' "$L/time-$n.txt" | awk '{print $NF}') maxrss_kb=$(grep 'Maximum resident' "$L/time-$n.txt" | awk '{print $NF}')" | tee -a "$L/steps.log"
  return $rc; }
rm -rf "$DEST"
run 1-clone git clone -q "$SRC" "$DEST" || exit 1
cd "$DEST" || exit 1
git log --oneline -1 | tee -a "$L/steps.log"
run 2-setup-clean scripts/setup-clean.sh "$SRC/ext/Clean" || exit 1
run 3-packages bash -c 'mkdir -p .lake && ln -s /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages .lake/packages' || exit 1
run 4-lake-build lake build || exit 1
run 4b-lake-build-warm lake build
run 5-ci scripts/ci.sh /home/devops/Verified-zkEVM/riscv-zkvm
echo "== $(date +%T) done" | tee -a "$L/steps.log"

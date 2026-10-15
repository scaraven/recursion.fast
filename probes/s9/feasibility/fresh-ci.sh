#!/usr/bin/env bash
# S9 feasibility: after fresh-clone.sh failed at CI step 2 (RecursionFast/Bridge/ is an empty directory
# git does not track), apply the minimal workaround and run the full CI, timed.
#   fresh-ci.sh DEST LOGDIR
set -uo pipefail
DEST=$1; L=$2; cd "$DEST" || exit 1
echo "== $(date +%T) workaround: mkdir -p RecursionFast/Bridge (load $(cut -d' ' -f1-3 /proc/loadavg))" | tee -a "$L/steps.log"
mkdir -p RecursionFast/Bridge
echo "== $(date +%T) step 5b-ci: scripts/ci.sh (load $(cut -d' ' -f1-3 /proc/loadavg))" | tee -a "$L/steps.log"
/usr/bin/time -v -o "$L/time-5b-ci.txt" scripts/ci.sh /home/devops/Verified-zkEVM/riscv-zkvm > "$L/out-5b-ci.log" 2>&1; rc=$?
echo "   rc=$rc wall=$(grep 'Elapsed (wall' "$L/time-5b-ci.txt" | awk '{print $NF}') user=$(grep 'User time' "$L/time-5b-ci.txt" | awk '{print $NF}') sys=$(grep 'System time' "$L/time-5b-ci.txt" | awk '{print $NF}') maxrss_kb=$(grep 'Maximum resident' "$L/time-5b-ci.txt" | awk '{print $NF}')" | tee -a "$L/steps.log"
echo "== $(date +%T) done (load $(cut -d' ' -f1-3 /proc/loadavg))" | tee -a "$L/steps.log"

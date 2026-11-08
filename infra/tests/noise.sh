#!/bin/bash
# Run-to-run timing noise in a bench VM (rf-supervisor test bench noise.sh --tar core.tar): builds
# the harness's calibration workload (harness/tools/calib.c, `gcc -O2 -pthread` as rfh/bench.py
# does) and infra/tests/memloop.c, warms up, then times RUNS (default 30) runs of each: `calib
# $(nproc) 32` (the season's rounds, the job's CPUs) after a 2 s idle gap (the harness's idle_s),
# and `memloop 4 20` (4 threads, memory bound). Prints every run and the statistics as JSON.
set -euo pipefail
RUNS=${RUNS:-30}
cd ~
gcc -O2 -pthread -o calib core/harness/tools/calib.c
gcc -O2 -pthread -o memloop core/infra/tests/memloop.c
rf-fingerprint | python3 -I -c 'import json,sys; d=json.load(sys.stdin); print("fingerprint", json.dumps(d["frequency_policy"], sort_keys=True))'
T=$(nproc)
./calib "$T" 32 >/dev/null; ./memloop 4 20 >/dev/null
: > runs.txt
for i in $(seq "$RUNS"); do
  sleep 2
  c=$(./calib "$T" 32); m=$(./memloop 4 20)
  echo "$i $c | $m" | tee -a runs.txt
done
python3 -I - <<'PY'
import json, re, statistics as st
c, m = [], []
for line in open("runs.txt"):
    a, b = line.split("|")
    c.append(int(re.search(r"ns=(\d+)", a).group(1))); m.append(int(re.search(r"ns=(\d+)", b).group(1)))
def s(x):
    mu = st.fmean(x); sd = st.stdev(x)
    return {"n": len(x), "mean_ms": round(mu / 1e6, 3), "sd_ms": round(sd / 1e6, 3), "cv_pct": round(100 * sd / mu, 3),
            "min_ms": round(min(x) / 1e6, 3), "max_ms": round(max(x) / 1e6, 3), "max_over_min": round(max(x) / min(x), 4),
            "median_ms": round(st.median(x) / 1e6, 3)}
print("NOISE " + json.dumps({"calib": s(c), "memloop": s(m)}))
PY

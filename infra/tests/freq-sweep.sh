#!/bin/bash
# The bench cores' sustainable frequency (root, on the runner host; the slots must be stopped:
# `systemctl stop 'rf-slot@*'`). For each variant BENCH_MHZ:OTHERS_MAX_MHZ:LOAD:
# apply the policy (bench min = max = BENCH_MHZ, the other CPUs' max OTHERS_MAX_MHZ; `hw` for the
# hardware's own range, e.g. hw:hw:0 the unpinned policy with boost; rf-host-apply with a variant
# of slots.json), load the other cores (LOAD 0: none; 1: both light VMs run the calib loop of
# load.sh and the host CPUs (slots.json host_cpus) run memory writers on half of them and busy
# loops on the rest; 2: the light VMs only; 3: the host CPUs only), run noise.sh in a bench VM
# (RUNS runs) and sample the bench CPUs with turbostat (Bzy_MHz: the effective frequency while
# busy, from APERF/MPERF; PkgWatt: the package power). Prints one line per variant; the policy of
# slots.json is re-applied at the end.
#   freq-sweep.sh CORE_TAR OUT_DIR RUNS VARIANT...      e.g. F:F:0 F:F:1 F:G:1 hw:hw:1 (F, G: MHz)
set -uo pipefail
TAR=$1 OUT=$2 RUNS=$3; shift 3
RF=/opt/rf-runner
T=/var/lib/rf-runner/test
mkdir -p "$OUT"
install -o rfrunner -m 0644 "$TAR" "$T/sweep-core.tar"
trap '"$RF/host/rf-host-apply"; systemctl stop rf-sweep-load rf-sweep-light1 rf-sweep-light2 2>/dev/null' EXIT
for v in "$@"; do
  IFS=: read -r bmhz omhz load <<< "$v"
  # nothing else may run: a VM left over would load the machine
  pgrep -x qemu-system-x86 >/dev/null && { echo "freq-sweep: a VM is running; stop the slots and tests first" >&2; exit 1; }
  python3 -I - "$RF/slots.json" "$bmhz" "$omhz" "$OUT/$v.json" <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
khz = lambda v: None if v == "hw" else int(v) * 1000  # noqa: E731 - None: the hardware's limit
b, o = khz(sys.argv[2]), khz(sys.argv[3])
c["freq"].update(bench_min_khz=b, bench_max_khz=b, others_max_khz=o); json.dump(c, open(sys.argv[4], "w"))
PY
  "$RF/host/rf-host-apply" --conf "$OUT/$v.json"
  { echo "RUNS=$RUNS"; cat "$RF/tests/noise.sh"; } > "$T/sweep-noise.sh"
  dur=$((RUNS * 6 + 200))
  { echo "DUR=$dur"; cat "$RF/tests/load.sh"; } > "$T/sweep-load.sh"
  chown rfrunner: "$T/sweep-noise.sh" "$T/sweep-load.sh"
  pids=()
  if [[ $load == 1 || $load == 2 ]]; then
    RF_TEST_UNIT=rf-sweep-light1 rf-test light1 "$T/sweep-load.sh" --tar "$T/sweep-core.tar" --timeout $((dur + 300)) > "$OUT/$v.light1.log" 2>&1 & pids+=($!)
    RF_TEST_UNIT=rf-sweep-light2 rf-test light2 "$T/sweep-load.sh" --tar "$T/sweep-core.tar" --timeout $((dur + 300)) > "$OUT/$v.light2.log" 2>&1 & pids+=($!)
  fi
  if [[ $load == 1 || $load == 3 ]]; then
    hl=$(python3 -I -c 'import json,sys; h=json.load(open(sys.argv[1]))["host_cpus"]; k=len(h)//2; print(",".join(map(str,h)) + "|" + " ".join(map(str,h[:k])) + "|" + " ".join(map(str,h[k:])))' "$RF/slots.json")
    IFS='|' read -r hcpus memc busyc <<< "$hl"
    systemd-run --quiet --unit rf-sweep-load --slice=rf.slice -p AllowedCPUs="$hcpus" -p RuntimeMaxSec=$((dur + 120)) \
      /bin/sh -c "for c in $memc; do taskset -c \$c dd if=/dev/zero of=/dev/null bs=64M 2>/dev/null & done;
                  for c in $busyc; do taskset -c \$c sh -c 'while :; do :; done' & done; wait"
  fi
  [[ $load == 0 ]] || sleep 60   # the light VMs boot and build their load
  # line-buffered: turbostat is stopped with a signal at the end
  bcpus=$(python3 -I -c 'import json,sys; print(",".join(map(str, json.load(open(sys.argv[1]))["slots"]["bench"]["pin"])))' "$RF/slots.json")
  stdbuf -oL turbostat --quiet --cpu "$bcpus" --show CPU,Busy%,Bzy_MHz,PkgWatt --interval 2 > "$OUT/$v.turbostat" 2>&1 &
  ts=$!
  rf-test bench "$T/sweep-noise.sh" --tar "$T/sweep-core.tar" --timeout 1500 > "$OUT/$v.log" 2>&1
  kill $ts 2>/dev/null; wait $ts 2>/dev/null
  systemctl stop rf-sweep-load 2>/dev/null
  # stop the light VMs (killing the rf-test client would leave them running into the next variant)
  systemctl stop rf-sweep-light1 rf-sweep-light2 2>/dev/null
  for p in "${pids[@]}"; do kill "$p" 2>/dev/null; done; wait 2>/dev/null
  python3 -I - "$v" "$OUT/$v.turbostat" "$OUT/$v.log" <<'PY'
import json, re, statistics as st, sys
v, ts, lg = sys.argv[1:]
mhz, watt = [], []
for line in open(ts):
    f = line.split()
    if len(f) == 4 and f[0] == "-":
        try:
            busy, b, w = float(f[1]), float(f[2]), float(f[3])
        except ValueError:
            continue
        if busy > 5:  # an interval in which the bench CPUs worked (Bzy_MHz: the frequency while busy)
            mhz.append(b); watt.append(w)
noise = next((json.loads(l[6:]) for l in open(lg) if l.startswith("NOISE ")), None)
c, m = (noise["calib"], noise["memloop"]) if noise else ({}, {})
print(f"{v:16} Bzy_MHz median {st.median(mhz) if mhz else float('nan'):6.0f} min {min(mhz) if mhz else float('nan'):6.0f}  "
      f"PkgWatt median {st.median(watt) if watt else float('nan'):5.1f}  calib {c.get('mean_ms')} ms cv {c.get('cv_pct')}% "
      f"max/min {c.get('max_over_min')}  memloop {m.get('mean_ms')} ms cv {m.get('cv_pct')}% max/min {m.get('max_over_min')}", flush=True)
PY
done

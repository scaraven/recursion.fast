#!/bin/bash
# usage: sample.sh OUTFILE ; samples loadavg and summed RSS (MB) of all lean/lake processes every 2 s until killed
out=$1
echo "t_s loadavg1 n_lean sum_rss_mb max_rss_mb" > "$out"
t0=$(date +%s)
while true; do
  la=$(cut -d' ' -f1 /proc/loadavg)
  ps -C lean,lake -o rss= 2>/dev/null | awk -v t=$(( $(date +%s)-t0 )) -v la=$la '{s+=$1; if($1>m)m=$1; n++} END{printf "%d %s %d %.0f %.0f\n", t, la, n, s/1024, m/1024}' >> "$out"
  sleep 2
done

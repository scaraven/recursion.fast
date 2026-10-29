#!/usr/bin/env bash
# Measures the oracle service on this machine (RESULT §3): keygen time, round-trip latency, and
# QUERY throughput for 1 and N client threads over batch sizes and query sizes; SIGN throughput.
#   tests/service/measure.sh [THREADS_MAX]      (logs to stdout; the caller tees into logs/)
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
B=$ROOT/service/target/release
N=${1:-$(nproc)}
W=$(mktemp -d "${RF_TEST_TMP:-/tmp}/rf-measure-XXXXXX"); trap 'rm -rf "$W"' EXIT
echo "machine: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2) ($(nproc) vCPU)"
for t in 1 4 $N; do
  for simd in avx2 scalar; do
    env=(); [[ $simd == scalar ]] && env=(RF_ORACLE_NO_SIMD=1)
    out=$(cd "$W" && rm -f k.sock && (sleep 0.1) | env "${env[@]}" "$B/rf-oracle" --socket k.sock --threads $t | grep keygen_ms)
    echo "keygen threads=$t simd=$simd $out"
  done
done
cd "$W"; rm -f o.sock ctl; mkfifo ctl
"$B/rf-oracle" --socket o.sock < ctl > svc.out 2>&1 &
exec 3>ctl
while ! grep -q ready svc.out; do sleep 0.05; done
grep -E 'simd|keygen' svc.out
"$B/rf-bench" o.sock latency 20000
for th in 1 $N; do
  for size in 32 64 1024 65536; do
    for batch in 1 16 256 4096; do
      (( size * batch > 16000000 )) && continue
      "$B/rf-bench" o.sock throughput $th $batch $size 1
    done
  done
done
exec 3>&-
sleep 0.5; tail -1 svc.out
# SIGN: a fresh service per measurement (each lifetime has 2^16 one-time keys)
for args in "1 0 1" "1 64 1" "$N 64 0.5"; do
  rm -f s.sock ctl2; mkfifo ctl2
  "$B/rf-oracle" --socket s.sock < ctl2 > svc2.out 2>&1 &
  exec 4>ctl2
  while ! grep -q ready svc2.out; do sleep 0.05; done
  "$B/rf-bench" s.sock sign $args
  exec 4>&-; sleep 0.3; tail -1 svc2.out
done
for size in 64 65536; do "$B/rf-bench" - local 1024 $size; RF_ORACLE_NO_SIMD=1 "$B/rf-bench" - local 1024 $size; done

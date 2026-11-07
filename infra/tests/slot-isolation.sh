#!/bin/bash
# The slots cannot act for each other (root, on the runner host, with the slots running): as a
# light slot's user (rflight1), the broker refuses a bench config and the deletion of a bench
# runner; the bench's run directory, seed and flag are out of reach; its tap cannot be opened.
set -u
L=rflight1
pass=0; fail=0
ok() { echo "PASS $*"; pass=$((pass + 1)); }
bad() { echo "FAIL $*"; fail=$((fail + 1)); }
req() { runuser -u "$1" -- python3 -I -c '
import socket, sys
s = socket.socket(socket.AF_UNIX); s.connect("/run/rf-jit/jit.sock"); s.sendall(sys.argv[1].encode() + b"\n")
print(s.recv(65536).decode().strip())' "$2"; }
out=$(req $L '{"op": "jitconfig", "slot": "bench"}')
[[ $out == *'"ok": false'* && $out == *"not 'bench'"* ]] && ok "broker refuses a bench config to $L: $out" || bad "broker answered $L's bench request: ${out:0:120}"
bid=$(python3 -I -c 'import json; print(json.load(open("/var/lib/rf-runner/run/bench/state.json"))["runner_id"])')
out=$(req $L "{\"op\": \"delete\", \"id\": $bid}")
[[ $out == *'"ok": false'* ]] && ok "broker refuses $L the deletion of the bench's runner $bid: $out" || bad "broker deleted the bench's runner for $L: $out"
out=$(req rfbench '{"op": "delete", "id": 1}')
[[ $out == *'"ok": false'* ]] && ok "broker refuses an id it never issued: $out" || bad "$out"
runuser -u $L -- ls /var/lib/rf-runner/run/bench >/dev/null 2>&1 && bad "$L lists the bench's directory" || ok "$L cannot list /var/lib/rf-runner/run/bench"
runuser -u $L -- cat /var/lib/rf-runner/run/bench/vm/seed.iso >/dev/null 2>&1 && bad "$L reads the bench's seed" || ok "$L cannot read the bench's seed (its JIT config)"
runuser -u $L -- cat /var/lib/rf-runner/run/bench/vm/job.log >/dev/null 2>&1 && bad "$L reads the bench's job log" || ok "$L cannot read the bench's job log"
runuser -u $L -- touch /var/lib/rf-runner/flags/bench-busy 2>/dev/null && bad "$L writes the bench flag" || ok "$L cannot set or clear the bench's flag"
runuser -u $L -- ls /var/lib/rf-runner/run/light2 >/dev/null 2>&1 && bad "$L lists light2's directory" || ok "$L cannot list light2's directory"
q=$(pgrep -u rfbench -x qemu-system-x86 | head -1)
[[ -n $q ]] && { runuser -u $L -- kill -0 "$q" 2>/dev/null && bad "$L can signal the bench QEMU" || ok "$L cannot signal the bench QEMU (pid $q)"; } || bad "no bench QEMU running"
runuser -u $L -- python3 -I -c '
import fcntl, os, struct
fd = os.open("/dev/net/tun", os.O_RDWR)
fcntl.ioctl(fd, 0x400454ca, struct.pack("16sH", b"rf-tap-bench", 0x0002 | 0x1000))' 2>/dev/null \
  && bad "$L attaches to rf-tap-bench" || ok "$L cannot attach to the bench's tap"
for s in bench light1 light2; do
  u=$(stat -c %U /var/lib/rf-runner/run/$s); m=$(stat -c %a /var/lib/rf-runner/run/$s)
  [[ $u == rf$s && $m == 700 ]] && ok "run/$s is rf$s's, 0700" || bad "run/$s is $u $m"
  o=$(cat /sys/class/net/rf-tap-$s/owner); [[ $o == $(id -u rf$s) ]] && ok "rf-tap-$s belongs to rf$s" || bad "rf-tap-$s owner $o"
  p=$(pgrep -u rf$s -x qemu-system-x86 | head -1); [[ -n $p ]] && ok "the $s QEMU runs as rf$s (pid $p)" || bad "no $s QEMU running as rf$s"
done
echo "RESULT: $pass passed, $fail failed"

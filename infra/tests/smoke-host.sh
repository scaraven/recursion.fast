#!/bin/bash
# The smoke test of one slot, with the host-side checks (root, on the runner host; the slot must be
# stopped or drained): runs tests/smoke.sh in a VM of SLOT and checks, from the host, that the
# VM's forged packets were dropped (the "spoofed source" counter grew by at least 10) and that the
# proxy refused the hosts that are not on the allowlist (TCP_DENIED in squid's access log).
#   smoke-host.sh SLOT > log
set -uo pipefail
SLOT=$1
RF=/opt/rf-runner
T=/var/lib/rf-runner/test
spoof() { nft list chain inet rf_filter prerouting | sed -n 's/.*counter packets \([0-9]*\) .*spoofed source.*/\1/p'; }
before=$(spoof)
ip=$(ip -4 -o addr show scope global | awk '{print $4}' | cut -d/ -f1 | head -1)
{ echo "HOST_IP=$ip"; cat "$RF/tests/smoke.sh"; } > "$T/smoke-run.sh"; chown rfrunner: "$T/smoke-run.sh"
start=$(date +%s)
rf-test "$SLOT" "$T/smoke-run.sh" --timeout 1200
after=$(spoof)
echo "== host side"
d=$((after - before))
[[ $d -ge 10 ]] && echo "PASS spoofed packets dropped on the host (counter +$d)" || echo "FAIL spoofed packets: counter +$d (want >= 10)"
net=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["slots"][sys.argv[2]]["net"])' "$RF/slots.json" "$SLOT")
denied=$(awk -v s="$start" -v ip="$net.2" '$1 >= s && $3 == ip && $4 ~ /DENIED/ {print $7}' /var/log/squid/access.log | sort -u | tr '\n' ' ')
[[ $denied == *example.com* ]] && echo "PASS the proxy denied: $denied" || echo "FAIL no TCP_DENIED for example.com in squid's log ($denied)"

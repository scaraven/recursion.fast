# The host's backstop (rf-test SLOT refusal-backstop.sh): a guest that reports a refusal but does
# not power itself off (here: the RF-HOOK line written by hand, no hook) is killed by the host
# within seconds; the marker after it must never appear.
echo 'RF-HOOK {"decision": "refused", "reason": "backstop test: no poweroff in the guest"}' > /dev/ttyS1
sleep 30
echo "MARKER: the guest kept running after its refusal"

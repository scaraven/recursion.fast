# The host's no-record rule (rf-test SLOT no-record.sh, with RF_CONF naming a slots.json whose
# policy_record_s is short): the script plays the runner's "Running job:" line on the runner's
# port (fd 3) and then neither runs the hook nor writes any record, as a VM whose hook did not
# run or could not report. The host must end the VM after policy_record_s, before the marker.
printf '%s: Running job: build\n' "$(date -u '+%F %TZ')" >&3
sleep 120
echo "MARKER: the job ran on without a policy record"

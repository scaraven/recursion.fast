#!/bin/bash
# The runner's job-started hook (ACTIONS_RUNNER_HOOK_JOB_STARTED in the runner's root-owned .env;
# root-owned, read-only, in the image). It runs before any step of a job. The policy is
# rf-job-policy.py with /etc/rf/job-allowlist.json (infra/job-allowlist.json) and this VM's slot
# type (/run/rf/slot-type). The decision goes to the job's log and to the host (the VM's job
# serial port, writable by the group `runner`; the supervisor copies it into its append-only job
# log). On a refusal the VM is powered off at once: a non-zero exit alone would still let steps
# with `if: always()` and the actions' pre steps run (runner v2.338.2, JobExtension.cs), so no
# step of a refused job may ever start. The host's supervisor also kills a VM whose hook refused.
# How this runs: the runner (v2.338.2) starts a job hook as `bash -e <path>` (JobHookProvider ->
# ScriptHandler: shell "bash" for a .sh file, IsActionStep false, arguments "-e {0}", the job's
# workspace as its directory). -e would end this script at the first failing command substitution,
# before the record and the poweroff, so every option a caller can set is undone first; the script
# works the same under `bash`, `bash -e`, `bash --noprofile --norc -e -o pipefail` and `sh` (which
# re-executes it under bash). Tested in tests/test_hook.sh under each of these.
[ -n "${BASH_VERSION:-}" ] || exec /bin/bash "$0" "$@"
set +e +u +o pipefail +o errtrace +o functrace
trap - ERR DEBUG RETURN
line=$(/usr/bin/python3 -I /usr/local/libexec/rf-job-policy.py /etc/rf/job-allowlist.json)
rc=$?
# the decision, as the host reads it: the first RF-HOOK line, parsed as JSON. The job runs only if
# that record says "allowed" and the policy exited 0; otherwise this is a refusal, and the record the
# host gets is a refusal too (the policy's own, which the host parses the same way, or one written
# here when it printed none or its exit disagreed with an allowed record), so that host and guest
# always agree
first=$(grep -m1 '^RF-HOOK ' <<< "$line")
decision=$(/usr/bin/python3 -I -c '
import json, sys
try:
    r = json.loads(sys.argv[1][len("RF-HOOK "):])
    print("allowed" if isinstance(r, dict) and r.get("decision") == "allowed" else "refused")
except ValueError:
    print("refused")' "$first" 2>/dev/null)
if [[ -z $first ]]; then
  first=$(printf 'RF-HOOK {"decision": "refused", "reason": "the job policy exited %s without a record"}' "$rc")
  line=$(printf '%s\n%s' "$line" "$first")
  rc=1
elif [[ $decision != allowed ]]; then
  rc=1      # the policy's own record goes to the host, which parses it the same way: a refusal
elif [[ $rc != 0 ]]; then
  first=$(printf 'RF-HOOK {"decision": "refused", "reason": "the job policy exited %s with an allowed record"}' "$rc")
  line=$(printf '%s\n%s' "$line" "$first")
  rc=1
fi
echo "$line"
# the one record for the host; a failed write is said in the job's log (the host then ends the VM:
# no record within its bound)
printf '%s\n' "$first" > /dev/ttyS1 \
  || echo "rf-job-started: cannot report the decision on ttyS1; the host will end this VM"
if [[ $rc != 0 ]]; then
  echo "recursion.fast runner: job refused; powering this VM off"
  sudo -n /usr/bin/systemctl poweroff --force --force 2>/dev/null \
    || echo o | sudo -n /usr/bin/tee /proc/sysrq-trigger >/dev/null 2>&1
  while :; do sleep 60; done   # never return: the VM is going down (and the host kills it)
fi
exit 0

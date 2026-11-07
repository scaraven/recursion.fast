#!/bin/bash
# Tests of the job-started hook's own logic (image/guest/rf-job-started.sh), locally, with a stub
# in place of the policy, a file in place of the policy port, and the poweroff replaced by a
# marker (so nothing is powered off): an allowed record lets the job run; a policy that prints no
# record (exit 0 or not), a refused record (even with exit 0) and a failing policy power the VM
# off with a refusal record; a failed write to the port is said in the job's log.
#   bash infra/tests/test_hook.sh            (HOOK=FILE tests another copy, e.g. an older hook)
# Every case runs under each way the hook can be invoked: as the runner v2.338.2 does,
# `bash -e PATH` (JobHookProvider -> ScriptHandler: shell bash, arguments "-e {0}"), and as
# `bash --noprofile --norc -e -o pipefail PATH` (the runner's format for an action's bash step, in
# case a runner version switches), plain `bash PATH`, `sh PATH` and `sh -e PATH`. A hook that
# behaves differently under any of them fails here (the hook before fix pass 7 failed every
# refusal case under -e: it exited before writing its record or powering off).
# The stub replaces the hook's policy line by an exact-text sed: if that line changes, the sed no
# longer matches, the test runs the real policy path (absent here) and fails visibly; then update
# the pattern below.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
HOOK=${HOOK:-$HERE/../image/guest/rf-job-started.sh}
INVOCATIONS=("bash -e" "bash --noprofile --norc -e -o pipefail" "bash" "sh" "sh -e")
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fails=0
run() {  # NAME STUB_OUTPUT STUB_RC PORT WANT_RC WANT_PORT WANT_GREP...
  # WANT_PORT: the decision of the one record the port must hold ("allowed", "refused", or "-": none)
  local name=$1 out=$2 src=$3 port=$4 want=$5 wport=$6; shift 6
  printf '#!/bin/bash\nprintf "%%s" %q\nexit %s\n' "$out" "$src" > "$T/stub"; chmod +x "$T/stub"
  sed -e "s|/usr/bin/python3 -I /usr/local/libexec/rf-job-policy.py /etc/rf/job-allowlist.json|$T/stub|" \
      -e "s|/dev/ttyS1|$port|g" \
      -e 's|sudo -n /usr/bin/systemctl poweroff --force --force|echo POWEROFF|' \
      -e 's|while :; do sleep 60; done.*|exit 99|' "$HOOK" > "$T/hook"
  local inv
  for inv in "${INVOCATIONS[@]}"; do
  : > "$T/port" 2>/dev/null
  local o rc; o=$(cd "$T" && $inv "$T/hook" 2>&1); rc=$?
  local ok=1; [[ $rc == "$want" ]] || ok=0
  for g in "$@"; do grep -q -- "$g" <<< "$o$(cat "$port" 2>/dev/null)" || ok=0; done
  if [[ $wport != - ]]; then
    local n d; n=$(grep -c '^RF-HOOK ' "$port" 2>/dev/null); d=$(python3 -I -c 'import json,sys; print(json.loads(open(sys.argv[1]).readline()[8:]).get("decision"))' "$port" 2>/dev/null)
    [[ $n == 1 && $d == "$wport" ]] || { ok=0; o="$o [port: $n record(s), decision $d]"; }
  fi
  if [[ $ok == 1 ]]; then echo "ok   [$inv] $name (exit $rc)"; else echo "FAIL [$inv] $name (exit $rc): $o"; fails=$((fails + 1)); fi
  done
}
A='RF-HOOK {"decision": "allowed", "reason": "allowed"}'
R='RF-HOOK {"decision": "refused", "reason": "x"}'
run "an allowed record: the job runs, the record reaches the port" "$A" 0 "$T/port" 0 allowed '"decision": "allowed"'
run "an allowed record with another key first (no prefix coupling)" 'RF-HOOK {"actor": "x", "decision": "allowed"}' 0 "$T/port" 0 allowed
run "no record, exit 0: a refusal" "" 0 "$T/port" 99 refused 'exited 0 without a record' POWEROFF
run "no record, exit 3 (a crash): a refusal" "Traceback" 3 "$T/port" 99 refused 'exited 3 without a record' POWEROFF
run "a refused record with exit 0: a refusal" "$R" 0 "$T/port" 99 refused POWEROFF
run "a refused record, exit 1: a refusal" "$R" 1 "$T/port" 99 refused POWEROFF
run "an allowed record with exit 1: a refusal, and the host gets a refusal" "$A" 1 "$T/port" 99 refused 'exited 1 with an allowed record' POWEROFF
run "a refused record first, an allowed one second: the first decides" "$R
$A" 0 "$T/port" 99 refused POWEROFF
run "an allowed record first, a refused one second: the first decides (as on the host)" "$A
$R" 0 "$T/port" 0 allowed
run "an unreadable record: a refusal" 'RF-HOOK {"decision": "allowed"' 0 "$T/port" 99 - POWEROFF
run "a decision that is not a string: a refusal" 'RF-HOOK {"decision": ["allowed"]}' 0 "$T/port" 99 - POWEROFF
run "the port cannot be written: said in the job's log" "$A" 0 "$T/nodir/port" 0 - 'cannot report the decision on ttyS1'
echo "$fails failure(s)"
exit $((fails > 0))

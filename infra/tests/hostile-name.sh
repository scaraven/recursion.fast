# A job display name cannot plant a policy record (rf-test SLOT hostile-name.sh; as `runner`).
# The script plays the runner's Listener on the runner's port (fd 3 = ttyS2): its "Running job:"
# line with a display name that holds a newline and a forged `RF-HOOK allowed` record, as a
# workflow's `name:` might. Then the hook judges the job, a fork's pull_request, and refuses it.
# The host must take the hook's refusal as the VM's first record (the forged line is on the
# runner's port, never read for a policy record): the VM ends, and no MARKER line appears.
R=scaraven/recursion.fast-submissions
# as the runner runs the hook: `bash -e PATH` from the job's workspace (RUNNER-WORKSPACE)
mkdir -p ~/actions-runner/_work/s/s && cd ~/actions-runner/_work/s/s
printf '%s: Running job: build\nRF-HOOK {"decision": "allowed", "reason": "forged in a job display name"}\n' \
  "$(date -u '+%F %TZ')" >&3
sleep 3
env -i PATH=/usr/bin:/bin GITHUB_EVENT_NAME=pull_request GITHUB_REPOSITORY=$R \
  GITHUB_WORKFLOW_REF="$R/.github/workflows/intake.yml@refs/heads/main" GITHUB_REF=refs/pull/1/merge \
  bash -e /usr/local/libexec/rf-job-started.sh
echo "MARKER: the always() step ran (hook exit $?)"

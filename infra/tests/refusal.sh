# A refused job never runs a step (rf-test SLOT refusal.sh; as `runner` in the guest). It does what
# the runner does for a job: run the job-started hook (here judging a fork's `pull_request` job),
# then, as a step with `if: always()` would, print a marker and write a marker file. The hook
# must power the VM off before the marker: the output must show the RF-HOOK refusal and no
# "MARKER" line, and the host must report that the VM ended after the refusal.
R=scaraven/recursion.fast-submissions
# as the runner runs the hook: `bash -e PATH` from the job's workspace (RUNNER-WORKSPACE)
mkdir -p ~/actions-runner/_work/s/s && cd ~/actions-runner/_work/s/s
echo "refusal test: the hook judges a pull_request job from a fork"
env -i PATH=/usr/bin:/bin GITHUB_EVENT_NAME=pull_request GITHUB_REPOSITORY=$R \
  GITHUB_WORKFLOW_REF="$R/.github/workflows/intake.yml@refs/heads/main" GITHUB_REF=refs/pull/1/merge \
  bash -e /usr/local/libexec/rf-job-started.sh
# the `if: always()` step
echo "MARKER: the always() step ran (hook exit $?)"
touch ~/marker && echo "MARKER: file written"

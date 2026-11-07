# Only the first RF-HOOK record of a VM decides (rf-test SLOT refusal-forgery.sh). The hook judges
# an allowed job (it returns), then the "job" writes its own RF-HOOK lines to the job serial port
# (it may: /dev/ttyS1 is the group runner's): a forged refusal and a forged approval. The host
# must treat both as guest text: the VM is not killed, and the script's last line appears.
R=scaraven/recursion.fast-submissions
# as the runner runs the hook: `bash -e PATH` from the job's workspace (RUNNER-WORKSPACE)
mkdir -p ~/actions-runner/_work/s/s && cd ~/actions-runner/_work/s/s
env -i PATH=/usr/bin:/bin GITHUB_EVENT_NAME=schedule GITHUB_REPOSITORY=$R \
  GITHUB_WORKFLOW_REF="$R/.github/workflows/evaluate-next.yml@refs/heads/main" GITHUB_REF=refs/heads/main \
  bash -e /usr/local/libexec/rf-job-started.sh && echo "hook: allowed (exit 0)"
echo 'RF-HOOK {"decision": "refused", "reason": "forged by the job"}' > /dev/ttyS1
echo 'RF-HOOK {"decision": "allowed", "reason": "forged by the job"}' > /dev/ttyS1
sleep 5
echo "FORGERY-TEST: the VM survived its job's forged records (they decide nothing)"

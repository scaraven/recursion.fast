#!/usr/bin/env bash
# Prepares a GitHub-hosted ubuntu-24.04 runner for the sandbox (TRUSTED; CI only, uses sudo; never
# run it on the development VM). It changes three system settings of the throw-away runner:
#   1. Ubuntu 24.04 restricts unprivileged user namespaces through AppArmor
#      (kernel.apparmor_restrict_unprivileged_userns = 1), which stops bubblewrap: the sysctl is set
#      to 0 for this job (C-m7 (f), V4-A6). The sandbox itself then refuses further user namespaces
#      inside (`--disable-userns`), so only the harness creates them.
#   2. bubblewrap is installed if missing.
#   3. lingering is enabled for the job's user, so that a systemd user manager exists and the sandbox
#      can cap memory with transient scopes (`systemd-run --user --scope -p MemoryMax=…`); without
#      it the sandbox falls back to an address-space limit and the result records `memcap: prlimit`.
# It prints the runner's facts (image, CPU, memory, kernel) for the log.
set -euo pipefail
echo "image: ${ImageOS:-?} ${ImageVersion:-?}; $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2); $(nproc) vCPU; $(free -g | awk '/Mem:/ {print $2}') GiB; kernel $(uname -r)"
if [[ -e /proc/sys/kernel/apparmor_restrict_unprivileged_userns ]]; then
  sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
fi
command -v bwrap >/dev/null || { sudo apt-get update -qq && sudo apt-get install -y -qq bubblewrap; }
sudo loginctl enable-linger "$(id -un)"
uid=$(id -u)
for _ in $(seq 1 50); do [[ -S /run/user/$uid/bus ]] && break; sleep 0.2; done
{
  echo "XDG_RUNTIME_DIR=/run/user/$uid"
  echo "DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/$uid/bus"
} >> "${GITHUB_ENV:-/dev/null}"
export XDG_RUNTIME_DIR=/run/user/$uid DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/$uid/bus
bwrap --unshare-user --unshare-pid --unshare-net --ro-bind / / -- true && echo "bwrap: user namespaces work"
if systemd-run --user --scope --quiet -p MemoryMax=64M true; then echo "memory cap: systemd user scopes"
else echo "memory cap: prlimit fallback (no systemd user manager)"; fi
cat /sys/fs/cgroup/user.slice/user-$uid.slice/user@$uid.service/cgroup.controllers 2>/dev/null || true

#!/bin/bash
# Provisions the golden image (runs as root inside the build VM, once; infra/image/build.sh passes
# it with versions.env, the toolchain names, rf-job, rf-job.service and rf-fingerprint through the
# build seed). Contents: security updates; git, curl, python3, gcc/binutils/build-essential,
# bubblewrap, zstd, jq, dbus-user-session (systemd user scopes for the sandbox's memory cap);
# the GitHub Actions runner, gh, elan + the Lean toolchain, rustup + the service's Rust toolchain,
# all at pinned versions with checked sha256; the user `runner` (passwordless sudo, as on
# GitHub-hosted runners: the workflows' runner-setup.sh uses it); no SSH server, no credentials,
# no background timers that could run during a job. Ends with RF-PROVISION-OK on the console.
set -euxo pipefail
# output: cloud-init sends runcmd output to the console (the build log)
B=/var/lib/rf-build
source "$B/versions.env"
export DEBIAN_FRONTEND=noninteractive
# the build VM, like every VM, reaches the internet only through the host's proxy (PROXY, from build.sh)
export http_proxy=$PROXY https_proxy=$PROXY HTTP_PROXY=$PROXY HTTPS_PROXY=$PROXY
printf 'Acquire::http::Proxy "%s";\nAcquire::https::Proxy "%s";\n' "$PROXY" "$PROXY" > /etc/apt/apt.conf.d/95rf-build-proxy
fetch() {  # URL SHA256 OUT
  curl -fsSL --retry 5 -o "$3" "$1"
  echo "$2  $3" | sha256sum -c -
}

apt-get update
apt-get -y -o Dpkg::Options::=--force-confold full-upgrade
apt-get -y install --no-install-recommends \
  git curl ca-certificates python3 gcc g++ binutils build-essential make bubblewrap zstd jq unzip \
  xz-utils tar util-linux dbus-user-session sudo
apt-get -y purge snapd openssh-server unattended-upgrades || true
apt-get -y autoremove --purge
fetch "https://github.com/cli/cli/releases/download/v$GH_VERSION/gh_${GH_VERSION}_linux_amd64.deb" "$GH_SHA256" /tmp/gh.deb
apt-get -y install /tmp/gh.deb

# the job user, as on GitHub-hosted runners
id runner >/dev/null 2>&1 || useradd -m -u 1001 -s /bin/bash runner
echo 'runner ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/runner && chmod 0440 /etc/sudoers.d/runner
mkdir -p /var/lib/systemd/linger && touch /var/lib/systemd/linger/runner

# the GitHub Actions runner
R=/home/runner/actions-runner
fetch "https://github.com/actions/runner/releases/download/v$RUNNER_VERSION/actions-runner-linux-x64-$RUNNER_VERSION.tar.gz" "$RUNNER_SHA256" /tmp/runner.tgz
mkdir -p "$R" && tar -xzf /tmp/runner.tgz -C "$R"
"$R/bin/installdependencies.sh"
P=/home/runner/.elan/bin:/home/runner/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
echo "$P" > "$R/.path"
# RF_MACHINE_FINGERPRINT: the machine fingerprint's file, written by rf-job at boot (the harness
# hashes its canonical JSON)
# ACTIONS_RUNNER_HOOK_JOB_STARTED: the job policy (rf-job-started.sh), run before any step of a job
printf 'LANG=C.UTF-8\nImageOS=ubuntu24\nImageVersion=rf-golden\nRF_MACHINE_FINGERPRINT=/run/rf/fingerprint.json\nACTIONS_RUNNER_HOOK_JOB_STARTED=/usr/local/libexec/rf-job-started.sh\n' > "$R/.env"
chown -R runner:runner "$R"
# the files that name the job-started hook and the PATH are root's: the job user cannot change them
chown root:runner "$R/.env" "$R/.path" && chmod 0644 "$R/.env" "$R/.path"

# elan and the Lean toolchain; rustup and the service's Rust toolchain (as `runner`)
fetch "https://github.com/leanprover/elan/releases/download/v$ELAN_VERSION/elan-x86_64-unknown-linux-gnu.tar.gz" "$ELAN_SHA256" /tmp/elan.tgz
fetch "https://static.rust-lang.org/rustup/archive/$RUSTUP_VERSION/x86_64-unknown-linux-gnu/rustup-init" "$RUSTUP_SHA256" /tmp/rustup-init
chmod 0755 /tmp/rustup-init && chmod 0644 /tmp/elan.tgz
runuser -u runner -- env -i HOME=/home/runner PATH=/usr/bin:/bin https_proxy="$PROXY" http_proxy="$PROXY" bash -euxc "
  cd /tmp && tar -xzf elan.tgz -C /home/runner && /home/runner/elan-init -y --no-modify-path --default-toolchain '$LEAN_TOOLCHAIN'
  rm -f /home/runner/elan-init
  /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain '$RUST_TOOLCHAIN'
  export PATH=$P
  lean --version && lake --version && cargo --version && rustc --version"
cat >> /home/runner/.profile <<'PROF'
PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
PROF

# the guest's job and the fingerprint
install -m 0755 "$B/rf-job" /usr/local/sbin/rf-job
install -m 0644 "$B/rf-job.service" /etc/systemd/system/rf-job.service
install -m 0755 "$B/rf-fingerprint" /usr/local/bin/rf-fingerprint
# the job policy: root's, read-only to everyone else (infra/job-allowlist.json)
install -d -m 0755 /usr/local/libexec /etc/rf
install -o root -g root -m 0555 "$B/rf-job-started.sh" "$B/rf-job-policy.py" /usr/local/libexec/
install -o root -g root -m 0444 "$B/job-allowlist.json" /etc/rf/job-allowlist.json
systemctl enable rf-job.service

# nothing listens, nothing runs in the background during a job
systemctl mask ssh.service ssh.socket 2>/dev/null || true
for t in apt-daily.timer apt-daily-upgrade.timer motd-news.timer man-db.timer fstrim.timer e2scrub_all.timer \
         fwupd-refresh.timer dpkg-db-backup.timer logrotate.timer update-notifier-download.timer \
         update-notifier-motd.timer sysstat-collect.timer sysstat-summary.timer ua-timer.timer; do
  systemctl disable --now "$t" 2>/dev/null || true; systemctl mask "$t" 2>/dev/null || true
done
systemctl mask unattended-upgrades.service apt-news.service esm-cache.service 2>/dev/null || true

# a record of what is in the image
{ echo "built $(date -u +%FT%TZ)"; cat "$B/versions.env" | grep -v '^#'; echo "LEAN_TOOLCHAIN=$LEAN_TOOLCHAIN"; echo "RUST_TOOLCHAIN=$RUST_TOOLCHAIN"
  uname -r; dpkg-query -W -f '${Package} ${Version}\n'
  # the guest's own files, so that an image's guard can be audited from its manifest
  echo "guest files (sha256):"
  sha256sum /usr/local/sbin/rf-job /usr/local/libexec/rf-job-started.sh /usr/local/libexec/rf-job-policy.py \
    /usr/local/bin/rf-fingerprint /etc/rf/job-allowlist.json /etc/systemd/system/rf-job.service \
    /home/runner/actions-runner/.env /home/runner/actions-runner/.path; } > /etc/rf-image-manifest

# clean: no build proxy, no machine id, no cloud-init instance, no logs, no caches (each VM gets its
# own proxy address from its seed: rf-job)
rm -f /etc/apt/apt.conf.d/95rf-build-proxy
apt-get clean
rm -rf /tmp/* /var/tmp/* "$B" /var/lib/apt/lists/* /root/.cache
cloud-init clean --logs --machine-id --seed
journalctl --rotate && journalctl --vacuum-time=1s || true
fstrim -av || true
sync
echo RF-MANIFEST-BEGIN; cat /etc/rf-image-manifest; echo RF-MANIFEST-END
echo RF-PROVISION-OK
systemctl poweroff

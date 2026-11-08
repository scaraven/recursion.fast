#!/usr/bin/env bash
# Builds the golden runner image (root, on the runner host; installed at /opt/rf-runner/image/).
#
#   /opt/rf-runner/image/build.sh            build, then make it current
#   /opt/rf-runner/image/build.sh --no-switch    build only
#
# 1. The pinned Ubuntu 24.04 cloud image (versions.env), downloaded once and checked by sha256.
# 2. A copy grown to "disk_gb" (slots.json "build"), booted once under KVM as `rfrunner` on the
#    build tap (the same egress filter as the slots), with a cloud-init seed that runs
#    provision.sh (versions.env, the toolchain named by the repository's lean-toolchain and
#    service/rust-toolchain.toml, rf-job, rf-fingerprint); the VM powers itself off.
# 3. Success = RF-PROVISION-OK on its console. The disk is compacted to
#    /var/lib/rf-runner/images/golden-<sha256[:16]>.qcow2 (read-only), with its full sha256 (the
#    "harness image id" in the machine fingerprint) in .sha256 and the package manifest in
#    .manifest; `current.qcow2` is switched to it atomically. Running VMs keep the image they
#    booted from (their overlays name it); the three newest images are kept.
# Log: the build VM's console in /var/lib/rf-runner/build/<stamp>/console.log.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
RF=$(dirname "$HERE")
LIB=/var/lib/rf-runner
SWITCH=1; [[ "${1:-}" == --no-switch ]] && SWITCH=0
[[ $(id -u) == 0 ]] || { echo "build.sh: run as root" >&2; exit 1; }
source "$HERE/versions.env"
LEAN_TOOLCHAIN=$(tr -d '[:space:]' < "$HERE/lean-toolchain")
RUST_TOOLCHAIN=$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$HERE/rust-toolchain.toml")
[[ -n "$LEAN_TOOLCHAIN" && -n "$RUST_TOOLCHAIN" ]] || { echo "build.sh: toolchains not found" >&2; exit 1; }
cfg() { python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); print(eval(sys.argv[2], {}, {"c": c}))' "$RF/slots.json" "$1"; }
TAP=$(cfg 'c["build"]["tap"]'); NET=$(cfg 'c["build"]["net"]'); MAC=$(cfg 'c["build"]["mac"]')
VCPUS=$(cfg 'c["build"]["vcpus"]'); MEM=$(cfg 'c["build"]["mem_mb"]'); DISK=$(cfg 'c["build"]["disk_gb"]')
HOSTCPUS=$(cfg '",".join(map(str, c["host_cpus"]))'); PROXY="http://$NET.1:$(cfg 'c["proxy_port"]')"
ip link show "$TAP" >/dev/null || { echo "build.sh: no $TAP (is rf-host.service active?)" >&2; exit 1; }

# 1. the base image
install -d -m 0700 -o root -g root "$LIB/cache"
install -d -m 0750 -o root -g rfrunner "$LIB/images"
install -d -m 0700 -o rfrunner -g rfrunner "$LIB/build"
BASE="$LIB/cache/base-${BASE_SHA256:0:16}.img"
if [[ ! -f "$BASE" ]] || ! echo "$BASE_SHA256  $BASE" | sha256sum -c --quiet -; then
  curl -fsSL --retry 5 -o "$BASE.part" "$BASE_URL"
  echo "$BASE_SHA256  $BASE.part" | sha256sum -c -
  mv "$BASE.part" "$BASE"
fi

# 2. the build VM
W="$LIB/build/$(date -u +%Y%m%dT%H%M%SZ)"
rm -rf "$LIB"/build/*/disk.qcow2 "$LIB"/build/*/seed.iso   # earlier failed builds
mkdir -p "$W/seed"
qemu-img convert -O qcow2 "$BASE" "$W/disk.qcow2"
qemu-img resize -q "$W/disk.qcow2" "${DISK}G"
b64() { base64 -w0 "$1"; }
{
  echo "#cloud-config"
  echo "users: []"

  echo "write_files:"
  wf() { printf '  - path: /var/lib/rf-build/%s\n    permissions: "%s"\n    encoding: b64\n    content: %s\n' "$1" "$2" "$3"; }
  wf provision.sh 0755 "$(b64 "$HERE/provision.sh")"
  wf versions.env 0644 "$(printf '%s\nLEAN_TOOLCHAIN=%s\nRUST_TOOLCHAIN=%s\nPROXY=%s\n' "$(cat "$HERE/versions.env")" "$LEAN_TOOLCHAIN" "$RUST_TOOLCHAIN" "$PROXY" | base64 -w0)"
  wf rf-job 0755 "$(b64 "$HERE/guest/rf-job")"
  wf rf-job.service 0644 "$(b64 "$HERE/guest/rf-job.service")"
  wf rf-fingerprint 0755 "$(b64 "$RF/fingerprint.sh")"
  wf rf-job-started.sh 0755 "$(b64 "$HERE/guest/rf-job-started.sh")"
  wf rf-job-policy.py 0755 "$(b64 "$HERE/guest/rf-job-policy.py")"
  wf job-allowlist.json 0644 "$(b64 "$RF/job-allowlist.json")"
  echo "runcmd:"
  echo "  - [bash, /var/lib/rf-build/provision.sh]"
} > "$W/seed/user-data"
printf 'instance-id: rf-build-%s\nlocal-hostname: rf-build\n' "$(basename "$W")" > "$W/seed/meta-data"
cat > "$W/seed/network-config" <<EOF
{"version": 2, "ethernets": {"eth0": {"match": {"macaddress": "$MAC"}, "set-name": "eth0", "dhcp4": false,
 "addresses": ["$NET.2/30"], "routes": [{"to": "default", "via": "$NET.1"}]}}}
EOF
genisoimage -quiet -output "$W/seed.iso" -volid cidata -joliet -rock -graft-points \
  user-data="$W/seed/user-data" meta-data="$W/seed/meta-data" network-config="$W/seed/network-config"
chown -R rfrunner:rfrunner "$W"
echo "build.sh: provisioning in $W (console: $W/console.log)"
rc=0
runuser -u rfrunner -- timeout 5400 taskset -c "$HOSTCPUS" qemu-system-x86_64 -name rf-build -machine q35,accel=kvm,mem-merge=off \
  -sandbox on,obsolete=deny,elevateprivileges=deny,spawn=deny,resourcecontrol=deny \
  -cpu host -smp "$VCPUS" -m "${MEM}M" -nodefaults -display none -no-user-config -no-reboot \
  -drive "file=$W/disk.qcow2,if=virtio,format=qcow2,discard=unmap" \
  -drive "file=$W/seed.iso,if=virtio,format=raw,readonly=on" \
  -netdev "tap,id=n0,ifname=$TAP,script=no,downscript=no" -device "virtio-net-pci,netdev=n0,mac=$MAC" \
  -device virtio-rng-pci -serial "file:$W/console.log" || rc=$?
grep -q RF-PROVISION-OK "$W/console.log" || { echo "build.sh: provisioning failed (qemu $rc); see $W/console.log" >&2; exit 1; }

# 3. the golden image
qemu-img convert -O qcow2 "$W/disk.qcow2" "$W/golden.qcow2"
SHA=$(sha256sum "$W/golden.qcow2" | cut -d' ' -f1)
NAME="golden-${SHA:0:16}.qcow2"
tr -d '\r' < "$W/console.log" | sed 's/^.*cloud-init\[[0-9]*\]: //' | sed -n '/^RF-MANIFEST-BEGIN/,/^RF-MANIFEST-END/p' \
  | grep -v '^+ ' | sed '1d;$d' > "$LIB/images/$NAME.manifest"
mv "$W/golden.qcow2" "$LIB/images/$NAME"
echo "$SHA  $NAME" > "$LIB/images/$NAME.sha256"
# root's, read-only to the slots (group rfrunner), immutable: a process that escapes a VM (uid
# rfrunner) cannot change what later VMs boot from
chown root:rfrunner "$LIB/images/$NAME"*
chmod 0440 "$LIB/images/$NAME" "$LIB/images/$NAME.sha256" "$LIB/images/$NAME.manifest"
chattr +i "$LIB/images/$NAME" "$LIB/images/$NAME.sha256" "$LIB/images/$NAME.manifest"
rm -f "$W/disk.qcow2" "$W/seed.iso" && rm -rf "$W/seed"
# keep the logs of the three newest builds
ls -1dt "$LIB"/build/*/ | tail -n +4 | xargs -r rm -rf
if [[ $SWITCH == 1 ]]; then
  ln -sfn "$NAME" "$LIB/images/.current.tmp" && mv -T "$LIB/images/.current.tmp" "$LIB/images/current.qcow2"
  # keep the three newest images (and the current one)
  cur=$(readlink "$LIB/images/current.qcow2")
  ls -1t "$LIB/images"/golden-*.qcow2 | tail -n +4 | while read -r old; do
    [[ $(basename "$old") == "$cur" ]] || { chattr -i "$old" "$old.sha256" "$old.manifest" 2>/dev/null; rm -f "$old" "$old.sha256" "$old.manifest"; }
  done
fi
echo "image id: $SHA"
echo "image: $LIB/images/$NAME"

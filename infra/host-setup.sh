#!/usr/bin/env bash
# Sets up the runner host (root; idempotent). Run from a copy of the repository on the host:
#
#   rsync -a --delete infra lean-toolchain service/rust-toolchain.toml root@HOST:/root/rf-src/   (see README)
#   bash /root/rf-src/infra/host-setup.sh                 install / update everything, arm the firewall
#   /opt/rf-runner/host-setup.sh --confirm-firewall       from a NEW ssh session, within 180 s
#   /opt/rf-runner/host-setup.sh --enable-slots           start the supervisor (needs the token)
#
# What it does:
#   1. security updates now (unattended-upgrade) and daily (unattended-upgrades, no automatic
#      reboot: a new kernel takes effect at a planned reboot); the microcode packages held (the
#      microcode is in the machine fingerprint);
#      the packages: qemu-system-x86, qemu-utils, cloud-image-utils, genisoimage, nftables,
#      linux-tools (cpupower, turbostat), squid (the VMs' allowlisting proxy);
#   2. the service accounts `rfrunner` (the slots and their QEMUs; group kvm) and `rfjit` (the token
#      broker, the only reader of the token), /etc/rf-runner (root, 0700; its files are left alone:
#      the token is the owner's), /var/lib/rf-runner (root; rfrunner may write only run/, state/,
#      test/, build/; the golden images are root's, read-only to rfrunner and immutable), the
#      append-only host job log state/jobs.log;
#   3. /opt/rf-runner: slots.json, the host scripts, the supervisor, the image builder, the
#      fingerprint, this script, README.md; the repository's lean-toolchain and
#      rust-toolchain.toml for the image;
#   4. the systemd units: rf-firewall (host/rf.nft), rf-host (taps, CPU isolation, frequency
#      policy), squid (host/proxy/), rf-jit (the token broker), rf.slice,
#      rf-slot@{bench,light1,light2} with each slot's AllowedCPUs and resource caps; the slots and
#      the broker stay disabled unless --enable-slots;
#   5. the firewall, safely: a changed rule set is loaded with a revert timer armed first (the
#      tables are deleted again after 180 s unless confirmed from a new SSH session), so a mistake
#      cannot lock anyone out; rf-firewall.service is enabled only on confirmation.
set -euo pipefail
[[ $(id -u) == 0 ]] || { echo "host-setup: run as root" >&2; exit 1; }
RF=/opt/rf-runner
LIB=/var/lib/rf-runner
GRACE=${RF_FW_GRACE:-180}
SLOTS=(bench light1 light2)

confirm_firewall() {
  if systemctl is-active --quiet rf-fw-revert.timer; then systemctl stop rf-fw-revert.timer; fi
  nft list table inet rf_filter >/dev/null || { echo "host-setup: the rule set is not loaded (reverted?)" >&2; exit 1; }
  systemctl enable rf-firewall.service
  systemctl start rf-firewall.service   # marks it active; reloading the same file is a no-op in effect
  sha256sum "$RF/host/rf.nft" | cut -d' ' -f1 > "$LIB/firewall.confirmed"
  echo "host-setup: firewall confirmed and enabled at boot"
}

enable_slots() {
  [[ -s /etc/rf-runner/github-token ]] || { echo "host-setup: no /etc/rf-runner/github-token; slots stay disabled" >&2; exit 1; }
  [[ -e $LIB/images/current.qcow2 ]] || { echo "host-setup: no golden image; run $RF/image/build.sh" >&2; exit 1; }
  [[ -f $LIB/firewall.confirmed ]] || { echo "host-setup: the firewall is not confirmed" >&2; exit 1; }
  systemctl enable --now rf-jit.service
  for s in "${SLOTS[@]}"; do systemctl enable --now "rf-slot@$s.service"; done
}

case "${1:-}" in
  --confirm-firewall) confirm_firewall; exit 0 ;;
  --enable-slots) enable_slots; exit 0 ;;
  "") ;;
  *) echo "usage: host-setup.sh [--confirm-firewall | --enable-slots]" >&2; exit 2 ;;
esac

SRC=$(cd "$(dirname "$0")" && pwd)          # .../infra
TOP=$(dirname "$SRC")                       # holds lean-toolchain and rust-toolchain.toml (or service/)
LEANTC=$TOP/lean-toolchain
RUSTTC=$TOP/rust-toolchain.toml; [[ -f $RUSTTC ]] || RUSTTC=$TOP/service/rust-toolchain.toml
[[ -f $LEANTC && -f $RUSTTC ]] || { echo "host-setup: lean-toolchain or rust-toolchain.toml missing beside infra/" >&2; exit 1; }
# the host-only values first, before anything on the host changes
python3 -I - /etc/rf-runner/host.local.json "$SRC/slots.json" <<'PY' || exit 1
import json, sys
try:
    c = json.load(open(sys.argv[1]))
except (OSError, ValueError) as e:
    sys.exit(f"host-setup: /etc/rf-runner/host.local.json: {e}: write it first from host.local.json.example (README)")
f = c.get("freq")
keys = ("governor", "epp", "bench_min_khz", "bench_max_khz", "others_max_khz", "sustained_mhz")
if not isinstance(f, dict) or any(k not in f for k in keys):
    sys.exit(f"host-setup: host.local.json: \"freq\" must hold {', '.join(keys)} (host.local.json.example)")
if "resctrl" not in c or not (c["resctrl"] is None or isinstance(c["resctrl"], dict)):
    sys.exit("host-setup: host.local.json: \"resctrl\" must be an object or null (host.local.json.example)")
s = json.load(open(sys.argv[2]))
for k in ("policy_record_s", "boot_limit_s", "idle_limit_s", "free_floor_gb"):
    v = s.get(k)
    if isinstance(v, bool) or not isinstance(v, (int, float)) or v <= 0:
        sys.exit(f"host-setup: slots.json: {k} must be a positive number, not {v!r}")
for name, sl in s.get("slots", {}).items():
    for k in ("hard_limit_s", "disk_limit_gb", "mem_mb"):
        v = sl.get(k)
        if isinstance(v, bool) or not isinstance(v, (int, float)) or v <= 0:
            sys.exit(f"host-setup: slots.json: slots.{name}.{k} must be a positive number, not {v!r}")
PY

echo "== 1. updates and packages"
export DEBIAN_FRONTEND=noninteractive
apt-get update -q
apt-get install -y -q unattended-upgrades
unattended-upgrade -v || true
apt-get install -y -q --no-install-recommends qemu-system-x86 qemu-utils cloud-image-utils genisoimage nftables \
  python3 squid linux-tools-common "linux-tools-$(uname -r)" || apt-get install -y -q --no-install-recommends \
  qemu-system-x86 qemu-utils cloud-image-utils genisoimage nftables python3 squid linux-tools-common
cat > /etc/apt/apt.conf.d/20auto-upgrades <<'EOF'
APT::Periodic::Update-Package-Lists "1";
APT::Periodic::Unattended-Upgrade "1";
EOF
cat > /etc/apt/apt.conf.d/52rf-runner <<'EOF'
// recursion.fast runner host: security updates daily; a kernel update waits for a planned reboot
Unattended-Upgrade::Automatic-Reboot "false";
EOF
systemctl enable --now unattended-upgrades.service >/dev/null
# the CPU microcode is part of the machine fingerprint: it changes only deliberately (README)
apt-mark hold amd64-microcode intel-microcode >/dev/null
# so are QEMU and the kernel (a new QEMU or kernel can change timings under a running season): their
# security updates are an owner step between seasons (README, "Holding QEMU and the kernel")
for p in qemu-system-x86 qemu-system-common qemu-system-data qemu-system-modules-spice qemu-utils \
         qemu-block-extra linux-generic linux-image-generic linux-headers-generic; do
  if dpkg-query -W -f='${Status}' "$p" 2>/dev/null | grep -q 'install ok installed'; then apt-mark hold "$p" >/dev/null; fi
done

echo "== 2. account and directories"
getent passwd rfrunner >/dev/null || useradd --system --home-dir "$LIB" --no-create-home --shell /usr/sbin/nologin rfrunner
usermod -aG kvm rfrunner
getent passwd rfjit >/dev/null || useradd --system --home-dir /var/lib/rf-jit --no-create-home --shell /usr/sbin/nologin rfjit
# one user per slot (its supervisor, its QEMU, its tap, its run directory; the broker maps its uid
# to the slot); group rfrunner: read the images, append to the job log; kvm: /dev/kvm
for s in "${SLOTS[@]}"; do
  getent passwd "rf$s" >/dev/null || useradd --system --user-group --home-dir "$LIB/run/$s" --no-create-home --shell /usr/sbin/nologin "rf$s"
  usermod -aG kvm,rfrunner "rf$s"
done
install -d -m 0700 -o root -g root /etc/rf-runner
chmod 0700 /etc/rf-runner && chown root:root /etc/rf-runner
[[ ! -e /etc/rf-runner/github-token ]] || { chown root:root /etc/rf-runner/github-token; chmod 0600 /etc/rf-runner/github-token; }
install -d -m 0750 -o root -g rfrunner "$LIB" "$LIB/images"
install -d -m 0700 -o root -g root "$LIB/cache"
install -d -m 0750 -o root -g rfrunner "$LIB/run" "$LIB/state"
install -d -m 0750 -o rfrunner -g rfrunner "$LIB/test"
for s in "${SLOTS[@]}"; do
  # a directory of the single-user layout (rfrunner's) is emptied before it changes hands
  if [[ -d $LIB/run/$s && $(stat -c %U "$LIB/run/$s") != "rf$s" ]]; then find "$LIB/run/$s" -mindepth 1 -delete; fi
  install -d -m 0700 -o "rf$s" -g "rf$s" "$LIB/run/$s"; chown "rf$s:rf$s" "$LIB/run/$s"; chmod 0700 "$LIB/run/$s"
done
# the bench's "a job is running" flag: written by rfbench, read by the light slots and the timers
install -d -m 0755 -o rfbench -g rfbench "$LIB/flags"
# leftovers of the single-user layout (run/SLOT.lock, run/test-*, state/SLOT.json, run/bench-busy)
rm -rf "$LIB"/run/*.lock "$LIB"/run/test-* "$LIB"/run/bench-busy "$LIB"/state/*.json "$LIB"/state/*.json.tmp
chown root:rfrunner "$LIB/run" "$LIB/state" && chmod 0750 "$LIB/run" "$LIB/state"
install -d -m 0700 -o rfrunner -g rfrunner "$LIB/build"
chown root:rfrunner "$LIB" "$LIB/images" && chmod 0750 "$LIB" "$LIB/images"
for f in "$LIB"/images/golden-*; do
  [[ -e $f ]] || continue
  chattr -i "$f"; chown root:rfrunner "$f"; chmod 0440 "$f"; chattr +i "$f"
done
[[ ! -L $LIB/images/current.qcow2 ]] || chown -h root:rfrunner "$LIB/images/current.qcow2"
# the job logs: one per slot, run/SLOT/jobs.log, the slot user's, append-only (chattr +a: it can add
# lines, never rewrite, rename or delete them); no other slot can write it. (An append-only file's
# owner and mode cannot change, so the attribute is lifted for the change.) The shared
# state/jobs.log of earlier versions is kept read-only as history.
for s in "${SLOTS[@]}"; do
  f=$LIB/run/$s/jobs.log
  [[ ! -e $f ]] || chattr -a "$f"
  touch "$f" && chown "rf$s:rf$s" "$f" && chmod 0600 "$f" && chattr +a "$f"
done
if [[ -e $LIB/state/jobs.log ]]; then
  chattr -a "$LIB/state/jobs.log"; chown root:rfrunner "$LIB/state/jobs.log"; chmod 0440 "$LIB/state/jobs.log"; chattr +a "$LIB/state/jobs.log"
fi

echo "== 3. files in $RF"
install -d -m 0755 "$RF" "$RF/host" "$RF/supervisor" "$RF/image" "$RF/image/guest" "$RF/tests"
install -m 0644 "$SRC/README.md" "$SRC/job-allowlist.json" "$SRC/host.local.json.example" "$RF/"
# slots.json as installed: the repository's layout plus the host-only values of
# /etc/rf-runner/host.local.json ("freq", "resctrl": they are measured on this host, so they are not in
# the repository; template: host.local.json.example)
chmod 0600 /etc/rf-runner/host.local.json
python3 -I - "$SRC/slots.json" /etc/rf-runner/host.local.json "$RF/slots.json" <<'PY'
import json, os, sys
c, local = json.load(open(sys.argv[1])), json.load(open(sys.argv[2]))
for k, v in local.items():
    if not k.startswith("_") and not k.endswith("_example"):
        c[k] = v
missing = [k for k in ("freq", "resctrl") if k not in c]
if missing:
    sys.exit(f"host-setup: host.local.json lacks {missing}")
tmp = sys.argv[3] + ".tmp"
with open(tmp, "w") as f:
    json.dump(c, f, indent=2)
os.chmod(tmp, 0o644)
os.replace(tmp, sys.argv[3])
PY
install -m 0755 "$SRC/host-setup.sh" "$SRC/fingerprint.sh" "$RF/"
install -m 0644 "$SRC/host/rf.nft" "$SRC/host/"*.service "$RF/host/"
install -m 0755 "$SRC/host/rf-host-apply" "$RF/host/"
before=$(cat "$RF/supervisor/rf-jit" "$RF/supervisor/rf-supervisor" 2>/dev/null | sha256sum)
install -m 0755 "$SRC/supervisor/rf-supervisor" "$SRC/supervisor/rf-status" "$SRC/supervisor/rf-test" "$SRC/supervisor/rf-jit" "$RF/supervisor/"
if [[ $before != "$(cat "$RF/supervisor/rf-jit" "$RF/supervisor/rf-supervisor" | sha256sum)" ]] && systemctl is-active --quiet rf-jit; then
  echo "host-setup: the broker or the supervisor changed: drain, then systemctl restart rf-jit (it restarts the slots)"
fi
install -m 0644 "$SRC/supervisor/"*.service "$SRC/supervisor/rf.slice" "$RF/supervisor/"
install -m 0755 "$SRC/image/build.sh" "$SRC/image/provision.sh" "$RF/image/"
install -m 0644 "$SRC/image/versions.env" "$RF/image/"
install -m 0755 "$SRC/image/guest/rf-job" "$SRC/image/guest/rf-job-started.sh" "$SRC/image/guest/rf-job-policy.py" "$RF/image/guest/"
install -m 0644 "$SRC/image/guest/rf-job.service" "$RF/image/guest/"
install -m 0644 "$LEANTC" "$RF/image/lean-toolchain"
install -m 0644 "$RUSTTC" "$RF/image/rust-toolchain.toml"
# the tests: root's (rf-test runs some of them), executables 0755, the rest 0644
rm -rf "$RF/tests" && install -d -m 0755 "$RF/tests"
for f in "$SRC"/tests/*; do m=0644; [[ -x $f ]] && m=0755; install -o root -g root -m "$m" "$f" "$RF/tests/"; done
ln -sfn "$RF/supervisor/rf-status" /usr/local/bin/rf-status
ln -sfn "$RF/supervisor/rf-test" /usr/local/sbin/rf-test
install -d -m 0755 "$RF/host/proxy"
install -m 0644 "$SRC/host/proxy/"* "$RF/host/proxy/"
# every tap of slots.json is in the firewall's sets and the proxy's ports, and nothing else is
python3 -I - "$RF/slots.json" "$RF/host/rf.nft" "$RF/host/proxy/squid.conf" <<'PY'
import json, re, sys
c = json.load(open(sys.argv[1])); nft = open(sys.argv[2]).read(); sq = open(sys.argv[3]).read()
links = list(c["slots"].values()) + [c["build"]]
src = {f'"{s["tap"]}" . {s["mac"]} . {s["net"]}.2' for s in links}
prox = {f'"{s["tap"]}" . {s["net"]}.1' for s in links}
ports = {f'http_port {s["net"]}.1:{c["proxy_port"]}' for s in links}
got_src = set(re.findall(r'"rf-tap-[a-z0-9]+" \. [0-9a-f:]{17} \. [0-9.]+', nft))
got_prox = set(re.findall(r'"rf-tap-[a-z0-9]+" \. [0-9.]+(?= *,|\s*\n\s*\})', nft)) - {x.rsplit(" . ", 1)[0] for x in got_src}
got_ports = set(re.findall(r'^http_port \S+', sq, re.M))
bad = [n for n, w, g in (("rf.nft vm_src", src, got_src), ("rf.nft vm_proxy", prox, got_prox), ("squid http_port", ports, got_ports)) if w != g]
if bad:
    sys.exit(f"host-setup: slots.json disagrees with {', '.join(bad)}")
PY
nft -c -f "$RF/host/rf.nft"

echo "== 4. units"
cat > /etc/sysctl.d/60-rf-runner.conf <<'EOF'
# recursion.fast runner host: nothing is routed for the VMs (their only way out is the proxy on
# the host); strict reverse-path filtering on new interfaces (the taps: rf-host-apply sets it too)
net.ipv4.ip_forward = 0
net.ipv4.conf.default.rp_filter = 1
EOF
sysctl -q -p /etc/sysctl.d/60-rf-runner.conf
install -m 0644 "$RF/host/rf-firewall.service" "$RF/host/rf-host.service" "$RF/supervisor/rf-slot@.service" \
  "$RF/supervisor/rf-jit.service" "$RF/supervisor/rf.slice" /etc/systemd/system/
# the proxy: our configuration and allowlists; started after rf-host has made the taps it listens on
install -m 0644 "$RF/host/proxy/squid.conf" /etc/squid/squid.conf
for f in allowlist allowlist-regex allowlist-build; do install -m 0644 "$RF/host/proxy/$f.txt" "/etc/squid/rf-$f.txt"; done
install -d /etc/systemd/system/squid.service.d
printf '[Unit]\n# it listens on the taps rf-host makes\nAfter=rf-host.service\nRequires=rf-host.service\n' \
  > /etc/systemd/system/squid.service.d/rf.conf
squid -k parse -f /etc/squid/squid.conf 2>&1 | grep -iE "error|fatal" && { echo "host-setup: squid.conf does not parse" >&2; exit 1; }
for s in "${SLOTS[@]}"; do
  cpus=$(python3 -I -c 'import json,sys; c=json.load(open(sys.argv[1])); print(",".join(map(str, sorted(set(c["host_cpus"]) | set(c["slots"][sys.argv[2]]["pin"])))))' "$RF/slots.json" "$s")
  install -d "/etc/systemd/system/rf-slot@$s.service.d"
  # MemoryMax: the VM's memory + 2 GiB for QEMU and the supervisor; for a slot on hugepages only the
  # 2 GiB, since its guest RAM is hugetlb, which the memory controller does not count: that is
  # bounded by the pool rf-host-apply reserves (exactly the slot's memory, preallocated at start)
  mem=$(python3 -I -c 'import json,sys; s=json.load(open(sys.argv[1]))["slots"][sys.argv[2]]; print(2048 + (0 if s.get("hugepages") else s["mem_mb"]))' "$RF/slots.json" "$s")
  printf '[Service]\n# QEMU threads on the host CPUs, the vCPUs on the slot'"'"'s (slots.json)\nAllowedCPUs=%s\n# QEMU and the supervisor (+ the guest RAM unless it is on hugepages)\nMemoryMax=%sM\n' "$cpus" "$mem" \
    > "/etc/systemd/system/rf-slot@$s.service.d/cpus.conf"
done
# the host's own heavy periodic jobs wait while the bench VM runs a job (its timings would see
# their memory traffic): each is skipped then, and runs at its next activation
for u in apt-daily apt-daily-upgrade man-db fstrim e2scrub_all logrotate dpkg-db-backup \
         mdcheck_start mdcheck_continue sysstat-collect sysstat-summary; do
  install -d "/etc/systemd/system/$u.service.d"
  printf '[Service]\n# not while the bench VM runs a job (recursion.fast runner host)\nExecCondition=/bin/sh -c "! test -e /var/lib/rf-runner/flags/bench-busy"\n' \
    > "/etc/systemd/system/$u.service.d/50-rf-bench.conf"
done
systemctl daemon-reload

echo "== 5. firewall"
sha=$(sha256sum "$RF/host/rf.nft" | cut -d' ' -f1)
if [[ -f $LIB/firewall.confirmed && $(cat "$LIB/firewall.confirmed") == "$sha" ]] && nft list table inet rf_filter >/dev/null 2>&1; then
  echo "host-setup: firewall unchanged and loaded"
else
  systemctl stop rf-fw-revert.timer 2>/dev/null || true
  systemctl reset-failed rf-fw-revert.service 2>/dev/null || true
  systemd-run --quiet --unit rf-fw-revert --on-active="$GRACE" /bin/sh -c \
    'nft delete table inet rf_filter; systemctl disable rf-firewall.service; rm -f /var/lib/rf-runner/firewall.confirmed'
  nft -f "$RF/host/rf.nft"
  echo "host-setup: firewall LOADED, revert armed in ${GRACE}s. From a NEW ssh session run:"
  echo "    $RF/host-setup.sh --confirm-firewall"
fi

echo "== 6. host state and the proxy"
systemctl enable rf-host.service squid.service >/dev/null
systemctl restart rf-host.service
systemctl restart squid.service
"$RF/host/rf-host-apply" --show | python3 -I -c 'import json,sys; d=json.load(sys.stdin); print("amd_pstate", d["amd_pstate"]); [print(" ", p["affected_cpus"], p["scaling_governor"], p["energy_performance_preference"], p["scaling_min_freq"], p["scaling_max_freq"]) for p in d["policies"]]'
for s in "${SLOTS[@]}"; do
  echo "rf-slot@$s: $(systemctl is-enabled "rf-slot@$s.service" 2>/dev/null || true)/$(systemctl is-active "rf-slot@$s.service" 2>/dev/null || true)"
done
[[ -e $LIB/images/current.qcow2 ]] || echo "host-setup: no golden image yet: $RF/image/build.sh"

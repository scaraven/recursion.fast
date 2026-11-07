#!/bin/bash
# A runner VM's smoke test (rf-supervisor test SLOT smoke.sh; runs as `runner` in the guest):
# the machine (KVM, -cpu host flags, vCPUs, memory), the fingerprint, the image's tools, and the
# egress policy (the proxy only; no direct traffic; the connection cap; forged packets, which the
# host counts: smoke-host.sh). Every check prints PASS or FAIL; the last line counts them.
# HOST_IP (the host's public address) is prepended by the caller.
set -u
pass=0; fail=0
ok()   { echo "PASS $*"; pass=$((pass + 1)); }
bad()  { echo "FAIL $*"; fail=$((fail + 1)); }
want() {  # DESC ok|blocked CMD...
  local d=$1 w=$2; shift 2
  if timeout 20 "$@" >/dev/null 2>&1; then g=ok; else g=blocked; fi
  [[ $g == "$w" ]] && ok "$d ($g)" || bad "$d (got $g, want $w)"
}
tcp() { exec 3<>"/dev/tcp/$1/$2"; }
export -f tcp

echo "== machine"
echo "virt: $(systemd-detect-virt)"; [[ $(systemd-detect-virt) == kvm ]] && ok "KVM guest" || bad "not KVM"
lscpu | grep -E "^(Model name|CPU\(s\)|Thread|Core|Socket|Flags)" | cut -c1-200
for f in avx2 avx512f avx512bw avx512vl avx512ifma avx512_vbmi2 gfni vaes vpclmulqdq pclmulqdq sha_ni bmi2 adx; do
  grep -qw "$f" /proc/cpuinfo && ok "cpu flag $f" || bad "cpu flag $f missing"
done
echo "vCPUs $(nproc), memory $(awk '/MemTotal/ {print $2}' /proc/meminfo) kB, disk: $(df -h / | tail -1)"

echo "== fingerprint"
rf-fingerprint && ok "fingerprint" || bad "fingerprint"
grep -qx 'RF_MACHINE_FINGERPRINT=/run/rf/fingerprint.json' ~/actions-runner/.env && ok "runner .env sets RF_MACHINE_FINGERPRINT" || bad "runner .env lacks RF_MACHINE_FINGERPRINT"
[[ -r "${RF_MACHINE_FINGERPRINT:-/nonexistent}" ]] && python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); assert sorted(d) == ["cpu_model", "frequency_policy", "host_kernel", "image_id", "microcode", "vm_shape"], sorted(d)' "$RF_MACHINE_FINGERPRINT" \
  && ok "fingerprint file $RF_MACHINE_FINGERPRINT has exactly the six fields" || bad "no fingerprint file, or other fields"
cmp -s <(rf-fingerprint) "$RF_MACHINE_FINGERPRINT" && ok "the fingerprint file equals a fresh rf-fingerprint" || bad "fingerprint file differs from a fresh run"

echo "== tools"
for c in "git --version" "curl --version" "python3 --version" "gcc --version" "as --version" "ld --version" \
         "bwrap --version" "zstd --version" "jq --version" "gh --version" "elan --version" "lean --version" \
         "lake --version" "cargo --version" "rustc --version" "systemd-run --version" "prlimit --version"; do
  out=$($c 2>&1 | head -1) && ok "$c: $out" || bad "$c: $out"
done
ls ~/actions-runner/run.sh ~/actions-runner/bin/Runner.Listener >/dev/null && ok "actions runner $(cat ~/actions-runner/bin/Runner.Listener.deps.json 2>/dev/null | grep -o '"Runner.Listener/[0-9.]*' | head -1)" || bad "actions runner"
sudo -n true && ok "passwordless sudo" || bad "sudo"
systemctl is-active ssh.service ssh.socket >/dev/null 2>&1 && bad "an SSH server runs" || ok "no SSH server"
ss -Hltn | grep -v '127.0.0' | grep -v '\[::1\]' | grep -q . && bad "listening TCP sockets: $(ss -Hltn | tr '\n' ' ')" || ok "nothing listens on a non-loopback TCP port"
[[ -z "$(ls ~/.ssh 2>/dev/null)" && ! -e ~/actions-runner/.runner && ! -e ~/actions-runner/.credentials ]] && ok "no credentials in the image" || bad "credentials found"

echo "== job policy (the runner's job-started hook)"
grep -qx 'ACTIONS_RUNNER_HOOK_JOB_STARTED=/usr/local/libexec/rf-job-started.sh' ~/actions-runner/.env \
  && ok "the runner's .env sets the job-started hook" || bad "no job-started hook in the runner's .env"
for f in /usr/local/libexec/rf-job-started.sh /usr/local/libexec/rf-job-policy.py /etc/rf/job-allowlist.json; do
  [[ $(stat -c %U "$f" 2>/dev/null) == root && ! -w "$f" ]] && ok "$f is root's, read-only to runner" || bad "$f: owner or mode"
done
st=$(cat /run/rf/slot-type 2>/dev/null)
[[ $st == bench || $st == light ]] && ok "slot type for the job policy: $st" || bad "no slot type ($st)"
[[ $(stat -c %U ~/actions-runner/.env) == root && ! -w ~/actions-runner/.env ]] && ok "the runner's .env is root's, read-only to runner" || bad "the runner's .env is writable by runner"
[[ $(stat -c %G /dev/ttyS1) == runner ]] && ok "the hook can report on the job serial port without sudo" || bad "/dev/ttyS1 group $(stat -c %G /dev/ttyS1)"
# allowed cases go through the hook itself (it returns); refused ones through the policy only,
# because the hook powers the VM off on a refusal (tests/refusal.sh shows that)
hook() { env -i PATH=/usr/bin:/bin GITHUB_EVENT_NAME="$1" GITHUB_REPOSITORY="$2" GITHUB_WORKFLOW_REF="$3" GITHUB_REF="$4" \
           bash -e /usr/local/libexec/rf-job-started.sh >/dev/null 2>&1; }
pol() { env -i PATH=/usr/bin:/bin GITHUB_EVENT_NAME="$1" GITHUB_REPOSITORY="$2" GITHUB_WORKFLOW_REF="$3" GITHUB_REF="$4" \
           /usr/bin/python3 -I /usr/local/libexec/rf-job-policy.py /etc/rf/job-allowlist.json >/dev/null 2>&1; }
R=scaraven/recursion.fast-submissions
hook schedule $R "$R/.github/workflows/evaluate-next.yml@refs/heads/main" refs/heads/main && ok "hook allows evaluate-next.yml on schedule" || bad "hook refuses evaluate-next.yml"
if [[ $st == light ]]; then
  hook pull_request_target $R "$R/.github/workflows/intake.yml@refs/heads/main" refs/heads/main && ok "hook allows intake.yml on pull_request_target (light)" || bad "hook refuses intake.yml on light"
else
  pol pull_request_target $R "$R/.github/workflows/intake.yml@refs/heads/main" refs/heads/main && bad "policy allows intake.yml on bench" || ok "policy refuses a bot workflow on bench"
fi
pol pull_request $R "$R/.github/workflows/intake.yml@refs/heads/main" refs/pull/1/merge && bad "policy allows pull_request" || ok "policy refuses pull_request"
pol workflow_dispatch $R "$R/.github/workflows/evaluate-next.yml@refs/heads/x" refs/heads/x && bad "policy allows another branch" || ok "policy refuses a workflow on another branch"
pol workflow_dispatch attacker/x "attacker/x/.github/workflows/evaluate-next.yml@refs/heads/main" refs/heads/main && bad "policy allows another repository" || ok "policy refuses another repository"

echo "== egress: through the proxy only"
gw=$(ip -4 route show default | awk '{print $3}')
grep -q "^https_proxy=http://$gw:3128$" /etc/environment && ok "/etc/environment names the proxy $gw:3128" || bad "/etc/environment has no proxy"
grep -q "^https_proxy=http://$gw:3128$" ~/actions-runner/.env && ok "the runner's .env names the proxy" || bad "the runner's .env has no proxy"
[[ "${https_proxy:-}" == "http://$gw:3128" ]] && ok "the job's environment has https_proxy" || bad "the job's environment lacks https_proxy"
reach() { curl -sS -o /dev/null --max-time 20 "https://$1/"; }   # any HTTP answer through the proxy
export -f reach
for h in github.com api.github.com codeload.github.com objects.githubusercontent.com release-assets.githubusercontent.com \
         raw.githubusercontent.com pipelines.actions.githubusercontent.com results-receiver.actions.githubusercontent.com \
         token.actions.githubusercontent.com broker.actions.githubusercontent.com productionresultssa0.blob.core.windows.net \
         productionresultssa17.blob.core.windows.net tuf-repo.github.com fulcio.sigstore.dev rekor.sigstore.dev \
         tuf-repo-cdn.sigstore.dev fulcio.githubapp.com cache.mathlib.org lakecache.blob.core.windows.net \
         index.crates.io static.crates.io crates.io; do
  want "proxy -> $h" ok bash -c 'reach "$0"' "$h"
done
want "git ls-remote https://github.com/leanprover/lean4 (through the proxy)" ok git ls-remote --heads https://github.com/leanprover/lean4 master
want "cargo search (crates.io through the proxy)" ok cargo search serde --limit 1
want "proxy -> example.com" blocked bash -c 'reach "$0"' example.com
want "proxy -> www.google.com" blocked bash -c 'reach "$0"' www.google.com
want "proxy -> another storage account (evil.blob.core.windows.net)" blocked bash -c 'reach "$0"' evilaccount.blob.core.windows.net
want "proxy -> archive.ubuntu.com (the image build's only)" blocked bash -c 'reach "$0"' archive.ubuntu.com
want "proxy -> a raw IP (140.82.112.3, a GitHub address)" blocked curl -sSk -o /dev/null --max-time 20 https://140.82.112.3/
want "proxy -> github.com:22 (CONNECT to another port)" blocked curl -sS -o /dev/null --max-time 20 https://github.com:22/
want "proxy -> plain http://github.com (not CONNECT)" blocked curl -sSf -o /dev/null --max-time 20 http://github.com/
want "proxy -> SMTP (smtp.gmail.com:587)" blocked curl -sS -o /dev/null --max-time 20 https://smtp.gmail.com:587/
echo "== egress: nothing directly"
want "DNS in the VM (getent hosts github.com)" blocked getent hosts github.com
want "direct https://github.com (no proxy)" blocked curl -sS -o /dev/null --noproxy '*' --max-time 10 https://github.com/
want "direct https://140.82.112.3 (no proxy, no DNS)" blocked curl -sSk -o /dev/null --noproxy '*' --max-time 10 https://140.82.112.3/
want "direct SMTP 142.250.102.27:25" blocked bash -c 'tcp 142.250.102.27 25'
want "direct DNS 8.8.8.8:53" blocked bash -c 'tcp 8.8.8.8 53'
want "10.0.0.1:80" blocked curl -sS --noproxy '*' -m 5 http://10.0.0.1/
want "169.254.169.254 (metadata)" blocked curl -sS --noproxy '*' -m 5 http://169.254.169.254/
want "another slot's VM 10.77.2.2:80" blocked curl -sS --noproxy '*' -m 5 http://10.77.2.2/
want "another slot's proxy address 10.77.9.1:3128" blocked bash -c 'tcp 10.77.9.1 3128'
want "the host via the gateway $gw:22" blocked bash -c "tcp $gw 22"
want "the host via the gateway $gw:53" blocked bash -c "tcp $gw 53"
want "the host's public address ${HOST_IP:-?}:22" blocked bash -c "tcp ${HOST_IP:-0.0.0.0} 22"
echo "== limits"
held=$(python3 -I - "$gw" <<'PY'
import socket, sys, time
socks, refused = [], 0
for i in range(320):
    s = socket.socket(); s.settimeout(5)
    try:
        s.connect((sys.argv[1], 3128)); socks.append(s)
    except OSError:
        refused += 1
    time.sleep(0.03)   # under the new-connection rate
print(len(socks), refused)
PY
)
read -r n r <<< "$held"
[[ $n -le 256 && $r -ge 60 ]] && ok "at most 256 open connections to the proxy (held $n, refused $r of 320)" || bad "connection cap: held $n, refused $r of 320"
sleep 2
echo "== spoofing (counted on the host: smoke-host.sh)"
sudo python3 -I - "$gw" <<'PY'
import socket, struct, sys
gw = sys.argv[1]
def csum(b):
    s = sum(struct.unpack("!%dH" % (len(b) // 2), b)); s = (s >> 16) + (s & 0xffff); return ~(s + (s >> 16)) & 0xffff
def ip(src, dst):
    udp = struct.pack("!HHHH", 40000, 3128, 8, 0)
    h = struct.pack("!BBHHHBBH4s4s", 0x45, 0, 28, 1, 0, 64, 17, 0, socket.inet_aton(src), socket.inet_aton(dst))
    h = h[:10] + struct.pack("!H", csum(h)) + h[12:]
    return h + udp
# 1. a forged source address (IP layer)
r = socket.socket(socket.AF_INET, socket.SOCK_RAW, socket.IPPROTO_RAW)
for _ in range(5):
    r.sendto(ip("203.0.113.7", gw), (gw, 0))
# 2. a forged source MAC with the VM's own address (link layer)
own = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); own.connect((gw, 9)); me = own.getsockname()[0]
gwmac = open("/proc/net/arp").read().split(gw)[1].split()[2]
p = socket.socket(socket.AF_PACKET, socket.SOCK_RAW); p.bind(("eth0", 0))
frame = bytes.fromhex(gwmac.replace(":", "")) + bytes.fromhex("5254deadbeef") + b"\x08\x00" + ip(me, gw)
for _ in range(5):
    p.send(frame)
print("SPOOF-SENT 5 forged-IP 5 forged-MAC")
PY
echo "RESULT: $pass passed, $fail failed"

# The evaluation machine

This directory sets up the competition's own runner host. It is a dedicated server that runs the
jobs of `scaraven/recursion.fast-submissions`, including the core's reusable `evaluate.yml` that
those jobs call. Each job runs in its own throwaway KVM virtual machine. Every file here is
installed by `host-setup.sh` into `/opt/rf-runner/`, so the host can be rebuilt from this
directory alone.

## What runs on the machine

| Unit | What it does |
|---|---|
| `rf-firewall.service` | Loads `host/rf.nft` at boot (the network rules are summarised below). |
| `rf-host.service` | Runs `host/rf-host-apply` at boot. It creates one tap per slot with a bandwidth cap and strict reverse-path filtering, and keeps IPv4 forwarding and KSM off. It confines the host to its CPUs, sets the frequency policy and partitions the L3 cache and memory bandwidth (resctrl). |
| `squid.service` | The VMs' only way out: an allowlisting HTTPS proxy (`host/proxy/`). It listens only on the host's end of each tap. |
| `rf-jit.service` | The token broker (`supervisor/rf-jit`, user `rfjit`), the only process that reads the GitHub token. It hands each slot one just-in-time runner config per request, over `/run/rf-jit/jit.sock`. The slot is decided by the caller's uid, never by the request, so a slot can get and delete only its own registrations. It serves at most 8 requests at a time and at most 2 per slot, so that no slot can starve another, and it retries failed deletions. |
| `rf-slot@bench`, `rf-slot@light1`, `rf-slot@light2` | One supervisor per slot (`supervisor/rf-supervisor`), each as its own user (`rfbench`, `rflight1`, `rflight2`, which also own the slot's QEMU, its tap and its 0700 directory `run/SLOT`). It loops: get a JIT config from the broker, boot a copy-on-write VM of the golden image with it, let the VM run exactly one job, then delete the VM. |

The slots are defined in `slots.json`. On this machine, core *i* is the CPU pair *i* and *i*+8.

| Slot | Labels | vCPUs | Pinned host CPUs | Memory | Overlay cap | Hard limit |
|---|---|---|---|---|---|---|
| `bench` | `rf-bench` | 8 (4 cores × 2 threads) | cores 4–7 (CPUs 4–7, 12–15) | 16 GiB | 100 GB | 90 min |
| `light1` | `rf-light` | 1 | CPU 3 | 4 GiB | 20 GB | 1 h |
| `light2` | `rf-light` | 1 | CPU 11 | 4 GiB | 20 GB | 1 h |
| the host (system and user slices, IRQs, QEMU's own threads, squid, the broker) | | | cores 0–2 (CPUs 0–2, 8–10) | | | |

The runners carry exactly these labels and no `self-hosted` label, so a bare
`runs-on: self-hosted` matches none of them. Workflows use `runs-on: rf-bench` or
`runs-on: rf-light`.

- **CPUs.** Each vCPU thread is pinned to its own host CPU, and `-cpu host` passes every host CPU
  feature through to the guest.
- **Frequency.** The bench CPUs run at a fixed frequency (`"freq"`) that they sustain under the
  package's power limit even when the other cores are busy. The other cores are capped lower, to
  leave power headroom (see *The frequency policy* below).
- **Cache and memory bandwidth.** The non-bench CPUs get a small share of the L3's ways and a
  memory-bandwidth cap (`"resctrl"`).
- **Host-only values.** `"freq"` and `"resctrl"` are measured on this host, so they are not in the
  repository. They live in `/etc/rf-runner/host.local.json` on the host (root, 0600; template
  `host.local.json.example`), and `host-setup.sh` merges them into the installed
  `/opt/rf-runner/slots.json`.
- **Light slots pause for the bench.** While the bench VM runs a job (`flags/bench-busy`, which
  only `rfbench` can write), the light slots take no new job: a running light job finishes, and
  an idle light VM is stopped. They resume when the bench job ends. The host's own heavy periodic
  jobs (`apt-daily*`, `man-db`, `fstrim`, `logrotate`, `mdcheck_*`, `sysstat-*` and others) skip
  their runs while a bench job is running.
  - **One known loss.** A light job that GitHub assigns to an idle light VM in the sub-second
    window before the bench's `Running job:` line fails as "runner lost" when that VM is stopped.
  - **It heals on its own** for the scheduled work: `sync` and `evaluate-next` run every 30
    minutes, and `sync` also re-intakes pull requests.
  - **A lost `pages` or `pin-check` run** (push-triggered) needs a re-run or the next push; both
    are informational or idempotent.
- **Kernel work.** kthreadd and every unbound kernel thread that allows it (kswapd, kcompactd,
  khugepaged, md2_raid1, and any md check thread started later) run on the host CPUs, as do
  unbound workqueues and movable IRQs. Per-CPU kernel threads (ksoftirqd/N, kworker/N,
  migration/N, cpuhp/N) and the per-CPU timer tick cannot move without kernel parameters
  (`isolcpus`, `nohz_full`), which are not used.
- **Bench memory.** The bench VM's 16 GiB are backed by 2 MiB hugepages that `rf-host-apply`
  reserves (`"hugepages"`), so its memory layout is the same on every boot.
  - **Why:** memory traffic on any other core slows the bench by about 16% (measured), which
    neither pinning nor the cache and bandwidth partition removes.
- **Recycling and limits.** A VM that has not had a job after 24 h is replaced with a fresh one.
  A VM is killed when its job runs past the slot's hard limit, when its overlay passes its cap,
  when a serial log passes 256 MiB, or when the host has less than 40 GB free.

QEMU runs with `-sandbox on,obsolete=deny,elevateprivileges=deny,spawn=deny,resourcecontrol=deny`
and `mem-merge=off`, as its slot's user. Each slot unit is capped at the VM's memory plus 2 GiB
(`MemoryMax`), with `TasksMax=512` and `LimitNOFILE=4096`. The bench is the exception: its guest
RAM is hugetlb, which the memory controller does not count, so its `MemoryMax` is only the 2 GiB.
The guest RAM is bounded instead by the hugepage pool `rf-host-apply` reserves, exactly the VM's
16 GiB, which QEMU preallocates at start. A process that escapes one slot's QEMU lands on that
slot's user: it cannot read another slot's directory, seed or job log, signal its QEMU, open its
tap, set the bench flag, or get or delete another slot's runner (`tests/slot-isolation.sh`). The
golden images are root's, read-only to the group `rfrunner` and immutable (`chattr +i`), so an
escape cannot change what later VMs boot from.

- **Status:** `rf-status` (state in `run/SLOT/state.json`) shows the slots, their VMs' ages, the current job and the last jobs.
- **Logs:** supervisor and broker logs go to the journal: `journalctl -u 'rf-slot@*' -u rf-jit`.
- **The host's job logs:** one per slot, `/var/lib/rf-runner/run/SLOT/jobs.log`. Each belongs to
  the slot's user, sits in its 0700 directory, and is append-only (`chattr +a`), so no other slot
  can write it. The same lines (`JOB {...}`) are also in the systemd journal, which records the
  writing unit and uid: `journalctl -u rf-slot@bench | grep ' JOB '`.
  - **What a log holds:** JSON lines at each job's start, for the job policy's decision, and at
    each VM's end. Each line carries the slot, the VM's instance id, the runner's name and id, the
    image id, the sha256 of the host facts given to the VM, the job, its start and end, and the
    reason the VM ended. Compare it with a disputed result.
  - **Which policy record counts:** the guest has two ports. The runner's output, including its
    `Running job: NAME` line, goes to the third serial port (`runner.log`). `NAME` is a workflow's
    display name, so whatever it holds (a newline, a forged `RF-HOOK` line) stays on that port,
    which the host reads only for the job's phases. The policy port (ttyS1, `job.log`) carries
    `rf-job`'s own lines and the hook's record; nothing else writes there before the hook. So the
    first `RF-HOOK` record on it is the hook's decision (`tests/hostile-name.sh`).
    Anything later was written by the job itself (the policy port is the group `runner`'s), so
    it is logged as `guest-text` and decides nothing.
  - The shared `state/jobs.log` of earlier versions is kept, read-only, as history.
- **Proxy log:** `/var/log/squid/access.log`.

## Which jobs run: the job policy (the primary guard)

Every runner VM checks each job before its first step. The check is the runner's job-started
hook (`ACTIONS_RUNNER_HOOK_JOB_STARTED` in the runner's `.env`, which is root's and read-only).
The hook, `/usr/local/libexec/rf-job-started.sh`, is root's and read-only in the image.

**On a refusal it powers the VM off at once.** A failing hook alone would not stop a job: steps
with `if: always()` and the actions' `pre` steps still run after it (runner v2.338.2,
`JobExtension.cs`). The host also kills any VM whose hook reported a refusal, even if the guest
did not power off. So no step of a refused job ever starts (`tests/refusal.sh` and
`refusal-backstop.sh`).

**No record is a refusal too.**
- **In the guest:** the hook refuses whenever the policy ends without an `allowed` record (a crash,
  an exit 0 with nothing printed, or an exit code that disagrees with the record). If it cannot
  write the record to the policy port, it says so in the job's log.
- **On the host:** a VM whose runner reports `Running job:` gets `policy_record_s` (300 s,
  `slots.json`) to deliver the record. Otherwise the host ends it as refused and the slot backs
  off. The hook runs right after the runner has fetched the job's action archives through the
  proxy, which takes seconds, so 300 s is a generous bound. The cost is that an allowed job whose
  record was lost is killed, which is the safe side.
  The rule covers a hook that crashes, hangs or cannot report. It does not cover an image without
  the hook: the job could then write a first record itself. That case is guarded by the image (its
  manifest's hashes of the hook and the runner's `.env`, checked by the smoke test).
- **The tests:** `tests/test_hook.sh` (the hook's logic, run locally with a stub policy) and
  `tests/no-record.sh`.

**What happens before the hook:** the runner downloads the archives of the job's actions
(`PrepareActionsAsync`, through the proxy) and executes nothing of them.

**A refusal costs the slot a registration,** so refusals back off like failures (at most 240 s,
up to 288 s with the jitter). A hook whose policy failed without printing its record writes a
refusal record itself, so a crashing policy backs off too. A burst of refused jobs cannot use up the broker's hourly registrations. The refused
job's actor and workflow are in the journal and the job log.

The allowlist is in one place, `job-allowlist.json` (in the image as
`/etc/rf/job-allowlist.json`), with one table per slot type. A job runs only if all of these
hold:

- its repository is `scaraven/recursion.fast-submissions`;
- its workflow (`GITHUB_WORKFLOW_REF`) is one of that slot type's workflows at
  `refs/heads/main`, and its event is listed for that workflow:
  - **bench:** `evaluate-next.yml` on `schedule` or `workflow_dispatch`. Its jobs of the core's
    reusable `evaluate.yml` report the *calling* workflow here. That workflow pins `evaluate.yml`
    by commit, so main decides which reusable workflow runs;
  - **light:** the same, plus `intake.yml` (`pull_request_target`, `workflow_dispatch`),
    `pages.yml` (`push`, `workflow_dispatch`), `pin-check.yml` (`push`) and `sync.yml` (`push`,
    `schedule`, `workflow_dispatch`).
- `pull_request`, `pull_request_review*`, `issue_comment` and `workflow_run` are on no list;
- for a push, the ref is `refs/heads/main`.

The VM's slot type comes from its seed.

GitHub sets these values in its job message to the runner. A fork's workflow file cannot change
them. The decision, with the values it judged, is printed in the job's log and copied into the
host's job log (`event: job-policy`). The static lint of the workflows is advisory; this hook is
the guarantee. The allowlist is part of the image, so changing it means rebuilding the image,
which changes the fingerprint's `image_id`. Its tests are in `tests/test_job_policy.py`.

## Facts relevant to the provider's terms

- **No inbound services.** The host accepts only SSH (22), ICMP and replies to its own traffic.
  The proxy listens only on the VMs' private links. Nothing listens inside the VMs, which have no
  SSH server.
- **VMs have no direct internet.** The host routes nothing for them: forwarding is off and the
  forward chain rejects everything. VMs have no DNS. Their only way out is the proxy, which allows
  HTTPS (CONNECT to port 443) and only to the hosts in `host/proxy/allowlist*.txt`:
  - GitHub (the API, git, the Actions services, and the artifact and cache storage);
  - GitHub's and the public Sigstore;
  - Mathlib's cache;
  - crates.io.

  Everything else is refused: other hosts, other ports, plain HTTP, raw IP addresses and SMTP.
- **Capped.** Each VM may open at most 50 new connections per second (burst 500) and hold 256
  open. Each tap is capped at 500 Mbit/s towards the VM and 300 Mbit/s from it.
- **No spoofing.** A VM can send only from its own MAC and IP address. Anything else, and any
  IPv6, is dropped on arrival. The VMs cannot reach each other or the host, except the proxy port
  on their own link.
- **Entry code has no network at all.** Untrusted code runs only inside the harness's bubblewrap
  sandbox (`--unshare-net`) inside the VM.
- **One VM per job.** Each VM boots from a fresh overlay, runs one job, and its disk is deleted
  when it powers off.
- **No credentials leave the host.** The GitHub token is `/etc/rf-runner/github-token` (root,
  0600). Only the broker reads it, as a systemd credential. The supervisors, QEMU and the VMs
  never see it. A VM receives only its own single-use runner config.

## Extending the proxy allowlist

When a job fails because the proxy refused a host, look for `TCP_DENIED` in
`/var/log/squid/access.log`. Add the host to `host/proxy/allowlist.txt` (a leading dot also
covers its subdomains), or add a pattern to `allowlist-regex.txt`. Then re-run `host-setup.sh`,
which installs the files and restarts squid. Add only hosts a workflow needs. Each one widens
what a VM can reach.

## Rebuilding the machine from scratch (Ubuntu 24.04, root SSH)

```sh
# first: the host-only values (host-setup.sh checks them before it changes anything), from the
# template; measure and fill them later (*The frequency policy*)
ssh root@HOST 'install -d -m 0700 /etc/rf-runner && umask 077 && cat > /etc/rf-runner/host.local.json' < infra/host.local.json.example
# from a checkout of this repository
ssh root@HOST mkdir -p /root/rf-src/service
rsync -a --delete infra lean-toolchain root@HOST:/root/rf-src/
rsync -a service/rust-toolchain.toml root@HOST:/root/rf-src/service/
ssh root@HOST bash /root/rf-src/infra/host-setup.sh          # packages, accounts, units; loads the firewall with a 180 s revert
ssh root@HOST /opt/rf-runner/host-setup.sh --confirm-firewall   # from a NEW session, within 180 s
ssh root@HOST /opt/rf-runner/image/build.sh                  # the golden image (through the proxy)
# then put the token in place (below) and run:
ssh root@HOST /opt/rf-runner/host-setup.sh --enable-slots    # the broker and the three slots
```

`host-setup.sh` is idempotent. Re-run it after changing anything in this directory. If the
firewall rules have not changed, it does not touch them. It checks that the taps, MACs and
addresses in `slots.json`, `host/rf.nft` and `host/proxy/squid.conf` agree. If a unit changed,
restart it: `systemctl restart rf-host rf-jit 'rf-slot@*'`.

**Recommendation, not applied:** root logs in with a key only, and its password is locked. sshd
still accepts password attempts, though, and the journal shows a steady stream of them against
`root`, `ubuntu` and other names; none can succeed today. Consider adding
`PasswordAuthentication no` in `/etc/ssh/sshd_config.d/50-rf.conf`, then reloading `ssh`. The
host's name is still the provider's image file name (`Ubuntu-noble-latest-amd64-base.zst`), which
is cosmetic: `hostnamectl set-hostname` fixes it.

## The token

The token is a fine-grained personal access token, created at
<https://github.com/settings/personal-access-tokens/new>:

- Resource owner: scaraven.
- Repository access: only `recursion.fast-submissions`.
- Permission: Administration, read and write. Nothing else is needed.

To install or rotate it:

```sh
ssh root@HOST 'umask 077; cat > /etc/rf-runner/github-token' < token.txt   # or paste, then Ctrl-D
ssh root@HOST 'chmod 0600 /etc/rf-runner/github-token; systemctl restart rf-jit'
```

Restarting the broker also restarts the slots, which kills any running job, so drain first (below).
After rotating, revoke the old token on GitHub.

## Drain, stop, start

```sh
touch /var/lib/rf-runner/drain      # no new VMs; a VM waiting for a job is stopped; a running job finishes
rf-status                           # wait until every slot shows "drained"
systemctl disable --now 'rf-slot@*' rf-jit   # stop, and keep stopped across reboots
rm /var/lib/rf-runner/drain && /opt/rf-runner/host-setup.sh --enable-slots   # resume
```

If you stop a slot without draining it first, its VM and job are killed, and the broker deletes
the slot's runner registration.

## Updating the golden image

Change the pins in `image/versions.env` (each with its sha256), `provision.sh`, or the
repository's `lean-toolchain` or `service/rust-toolchain.toml`. Then sync and re-run
`host-setup.sh` (above), followed by:

```sh
/opt/rf-runner/image/build.sh       # builds through the proxy, checks, then switches current.qcow2 atomically
```

**Release gate for every image.** Before the slots take jobs on a new image, run
`/opt/rf-runner/tests/smoke-host.sh bench` and `… light1` (drain the slots first). Its
`PASS the runner's .env sets the job-started hook` and the hook checks show that the image has
the guard. Also compare the manifest's guest-file hashes with the repository's `image/guest/`
files.

- **The fingerprint gate.** The pin's `harness/season.toml` `[machine] fingerprint` must equal the
  live image's: `/opt/rf-runner/tests/fp-from-seed.py /var/lib/rf-runner/run/bench/vm/seed.iso`.
  Only `cpu_model`, `vm_shape`, `frequency_policy` (with the cache partition, `sustained_mhz` and
  the memory backing) and `image_id` are hashed. So a new image, VM shape or frequency policy
  changes it, and so does another processor. A new kernel, microcode or QEMU is only recorded
  (`host_kernel`, `microcode`, `qemu` in the results and job records): it needs no new
  fingerprint, but re-measure the noise.
- **The release order,** which nothing else enforces:
  1. the hook fix (or any guest change);
  2. the image (`build.sh`, then this gate);
  3. `season.toml`'s fingerprint for that image;
  4. the core commit;
  5. the pin (`evaluate-next.yml` and `.contract` in the submissions repository).

  Any other order pauses the queue with an organiser error.
- **One refused job per image.** Dispatch a throwaway workflow on a non-`main` branch with
  `runs-on: rf-light`. It must end failed, with the `::error title=recursion.fast runner::`
  annotation, the VM powered off at once, and a `job-policy` record with `hook_decision: refused`
  in `run/light*/jobs.log`. The smoke tests show the hook is configured; only a real job shows
  that it works under the runner.

The build VM may additionally reach the Ubuntu archive and Rust's distribution server
(`allowlist-build.txt`). Each new VM boots from the new image, while running VMs keep the image
they started from. The three newest images, and the logs of the three newest builds, are kept.

**Images are not reproducible bit for bit.** Each build installs the archive's current security
updates (`apt full-upgrade`) and the runner's dependencies, and records timestamps. Two builds
from the same pins therefore have different sha256s. The image id in the fingerprint identifies
one build, not a recipe. It changes with every rebuild, which re-baselines the season's
fingerprint. A season therefore keeps one image. GitHub stops accepting runner versions some time
after a newer release: when jobs stop being picked up, raise `RUNNER_VERSION`, rebuild and
re-baseline.

## Holding QEMU and the kernel

`host-setup.sh` holds QEMU (`qemu-system-x86` and its parts, `qemu-utils`) and the kernel's meta
packages (`linux-generic`, `linux-image-generic`, `linux-headers-generic`), as it holds the
microcode. Unattended upgrades then cannot change them under a running season; every other
security update still installs daily. The job records carry `qemu`, `host_kernel` and `microcode`
for each VM.

Their security updates are an owner step, between seasons or at once for an urgent fix:

```sh
systemctl disable --now 'rf-slot@*'            # after draining
apt-mark unhold qemu-system-x86 qemu-system-common qemu-system-data qemu-system-modules-spice qemu-utils \
  qemu-block-extra linux-generic linux-image-generic linux-headers-generic
apt-get update && apt-get upgrade && reboot
# after the reboot: /opt/rf-runner/host-setup.sh (holds them again), the release gate above
```

A new kernel or microcode changes the recorded `host_kernel`/`microcode`, not the hashed
fingerprint. A new QEMU is recorded only. Re-measure the noise (`tests/noise.sh`) after either.

## The machine fingerprint

`fingerprint.sh` is installed in the image as `rf-fingerprint`. At boot, the VM writes its output
to `/run/rf/fingerprint.json`, and the runner's environment variable `RF_MACHINE_FINGERPRINT`
points to that file. The JSON has exactly six fields:

- `cpu_model`;
- `vm_shape` (`vcpus`, and `memory` as a string such as `"16384 MiB"`);
- `frequency_policy`: a string, the canonical JSON of the pinned CPUs' driver, governor, EPP,
  minimum and maximum frequency and boost, the effective frequency measured under load (`sustained_mhz`), and the resctrl partition. The partition is hashed as the kernel's `schemata` text, so a kernel
  that formats it differently changes the fingerprint even though `host_kernel` is unhashed;
- `image_id`;
- `host_kernel`;
- `microcode`.

The host supplies these facts through the VM's read-only seed (`/run/rf/host.json`). That file
also holds the CPU signature, QEMU's version and the pinning, for diagnosis. Anything in the
seed can appear in a public job log.

The harness hashes the fields that define the machine: `cpu_model`, `vm_shape`,
`frequency_policy` and `image_id`. `host_kernel` is recorded with each result but not hashed;
`microcode` is neither hashed nor recorded in results. A season's
results are comparable only while those hashed fields keep the values the season recorded.

**Changing the microcode or the image means updating the season's fingerprint.** For this reason
`host-setup.sh` holds the microcode package (`apt-mark hold amd64-microcode`), so the microcode
changes only when you choose: `apt-mark unhold amd64-microcode`, upgrade, then reboot. The same
applies to rebuilding the image and to changing `"freq"`, `"resctrl"` or a slot's shape in
`slots.json`. Unattended security upgrades stay on but never reboot the host, so a new kernel
takes effect only at a reboot you schedule. Plan such reboots between seasons where you can.

After any such change, follow the submissions bot's README, "Owner setup", *When the image or
the machine changes*: read the new hash in a bench VM, commit it to `harness/season.toml`
`[machine] fingerprint`, move the submissions repository's pin to that commit, and resume the
queue if it paused.

## The frequency policy

The processor's package power limit is shared by every core, so a frequency the bench cores
reach on an idle machine may not hold when the other cores work. The bench's fixed frequency is therefore
chosen by measurement, with the other cores' maximum capped:

```sh
systemctl stop 'rf-slot@*'
/opt/rf-runner/tests/freq-sweep.sh /var/lib/rf-runner/test/core.tar /root/sweep 15 \
  BENCH_MHZ:OTHERS_MAX_MHZ:0 BENCH_MHZ:OTHERS_MAX_MHZ:1 ...
```

Each variant is `bench MHz : others' max MHz : load (0 or 1)`. Under load, both light VMs run
the calibration loop and the host cores run memory writers and busy loops. For each variant the
script prints the bench CPUs' effective frequency (turbostat's `Bzy_MHz`, from APERF/MPERF), the
package power and the calib and memloop timings. Choose the highest bench frequency whose loaded
`Bzy_MHz` stays at the setpoint. Put it in `/etc/rf-runner/host.local.json` `"freq"`
(`bench_min_khz` = `bench_max_khz`, `others_max_khz`, `sustained_mhz`) and re-run `host-setup.sh`.

## Testing a VM without GitHub

```sh
/opt/rf-runner/tests/smoke-host.sh bench   # in-VM checks plus the host-side spoofing and proxy checks
rf-test light1 /opt/rf-runner/tests/smoke.sh   # in-VM checks only
```

`rf-test` runs `supervisor/rf-supervisor test` as the slot's user in `rf.slice`. The guest runs the
script as `runner`, and its output comes back to your terminal. `--tar FILE` unpacks a tarball
into the guest's home first; `/opt/rf-runner/tests/noise.sh` and `harness-quick.sh` expect the
repository there as `core/`. A test takes the slot's lock, so drain or stop the slot first.

# Stage B (v4, SROM): the trusted runtime — RESULT

Status (2026-10-23): **done, except a run on GitHub.** Everything below was built and run on the
development VM: 32 vCPU, QEMU virtual CPU with AVX2 and AVX-512, 62 GB, other agents running, load
average 14–25. The workflows are written and parse, but have not run on GitHub; the orchestrator
pushes the branch to run them. Worktree `/home/devops/Verified-zkEVM/recursion.fast-v4h`, branch
`v4/harness` on `85f0985` (stage A merged); nothing is committed.

**End to end** (`tests/harness/smoke.py --org`, 11 checks pass in 5 min 38 s,
`logs/harness/smoke-e2e.log`; smoke shape `r = 2`, `n = 16`, `M = 4`):

- **Certified.** The library's witness-sending entry, with its claim, passes the certificate job
  (`harness/evaluate.py cert`):
  1. the source rule;
  2. the comparator in a fresh tree, with the Lean kernel;
  3. a rebuild bound byte for byte to the comparator-verified build;
  4. the gate;
  5. the badge build.
- **ACCEPT.** The toy prover, C compiled to x86-64 assembly and committed as `.s`, is built in the
  sandbox and benchmarked with the compiled `accF` badge (`harness/evaluate.py bench`): `T_tree`,
  `t_link`, `S`, 62 + 16 canaries rejected, the DoS column, and liveness through the compiled
  extractor interpreter.
- **REJECT**, each with the root rejected by `acc`: three deliberately broken provers, namely a
  wrong chain end, an unsigned trace, and a signature from another run's service.
- **PROVISIONAL**, not comparable: the same entry with `certified := sorry`.
- **REJECT** by the source rule, before anything is built: an entry with `#eval`.

## 1. What was built

| Component | Files | Trusted for |
|---|---|---|
| **Service** `rf-oracle` (Rust 1.99.0 pinned, std only) | `service/src/{lib,blake2s,wots,proto,main}.rs`; `service/PROTOCOL.md` (normative wire format) | `PRF_k` = keyed BLAKE2s-256; signing exactly the queried trace with a fresh one-time key; keeping `k` and the seed secret and fresh per lifetime; the liveness log being the complete query log |
| Measurement client `rf-bench` (untrusted tooling) | `service/src/bin/rf-bench.rs` | nothing (it measures; the runner uses it for the calibration column) |
| **Sandbox** | `harness/rfh/sandbox.py`, `harness/rfh/files.py`, `scripts/bwrap-landrun.sh` | that the prover, its build, the entry's Lean build and gate, and the badge cannot read the service, other processes or host files, reach the network, write outside their directory, outlive their run, or exceed their memory |
| **Runner** | `harness/rfh/{digest,signed,service,prover,checks,bench}.py`, `harness/run-benchmark.py`, `harness/aggregate.py`, `harness/season.toml`, `harness/smoke.toml`, `harness/FORMAT.md`, `harness/PROVER.md` | the instances (fresh secret starts, digests computed by the runner); the timing; asking `acc` the right questions and requiring the right answers; the score |
| **Badge mains** (Lean, rendered per entry) | `harness/badge/{Common,Verify,Liveness}.lean.in` | parsing the runner's files strictly and calling `accF` (= `acc`, `accF_eq`); running `ext` on the contract interpreter and checking the decoded witness |
| **Proof side** | `harness/evaluate.py`, `harness/render-challenge.py`, `harness/challenge/Challenge.lean.in`, `harness/org-setup.sh`; `harness/lean-tools/Gate.lean` (v3's gate, ported); stage A's `scripts/AxiomAudit.lean`, compiled there; `scripts/source-rule.py`, `scripts/olean-manifest.py` (ported) | the harness order; that the certificate checked is the organiser's statement about the built submission; no code-changing attributes, no `unsafe`/`partial`/`opaque` and no forbidden imports on the badge path |
| Calibration | `harness/lean-tools/gen_chaincheck.py` → `ChainCheck.lean` | nothing beyond its own timing (its root is compared with the runner's) |
| **CI** | `.github/workflows/ci.yml`, `.github/workflows/evaluate.yml`, `harness/ci-template/evaluate-entry.yml`, `harness/ci/{runner-setup,fetch-entry,build-kernels}.sh` | the trust anchor (V4-A1): which workflow ran, with which permissions, on which commit; the attested result |
| Toy prover (untrusted) | `harness/toy-prover/toy.c`, `harness/toy-prover/honest/prover.s` | nothing |
| Tests | `tests/service/` (service, Python WOTS reference, Lean signer, measurements); `tests/harness/` (sandbox with a hostile prover, the smoke, the stand-in badge, the witness-sending entry, the `acc` probe); `tests/gate/` (v4 fixtures); `tests/source-rule/` (v3's fixtures) | — |

### 1.1 Line counts

Source: `logs/harness/loc-runtime.log`. "Code" means non-blank, non-comment lines.

| Component | Lines | Code |
|---|---:|---:|
| service (includes 54 lines of unit tests; the AVX2 path is about 150) | 1,250 | 1,002 |
| runner | 1,244 | 959 |
| sandbox | 318 | 220 |
| badge mains | 210 | 133 |
| proof-side order | 557 | 404 |
| proof-side tools ported from v3 (source rule, olean manifest, gate) | 1,074 | 697 |
| CI scripts | 73 | 49 |
| calibration generator | 209 | 161 |
| untrusted: `rf-bench`, toy prover | 415 | 362 |

**Total trusted: about 3,660 code lines.**

| Part of the total | Code lines |
|---|---:|
| Rust service | 1,002 |
| Python, shell and Lean | about 2,660 |
| of which v3's ported proof-side tools | 697 |

The service exceeds D4's estimate of 300–400 lines. The difference is the SIMD path, the caps,
the liveness log and the lifecycle. A scalar-only service would be about 850 code lines.

## 2. Interfaces

- **Wire protocol** (`service/PROTOCOL.md`, normative for provers).
  - Messages: a 16-byte header, then a body.
  - Operations:
    - `QUERY`: a batch in, the answers out.
    - `SIGN`: the answers plus a signature; the service re-evaluates every query.
    - `VK`.
  - Caps, each refused as an error that closes the connection:
    - a query: 2^20 bytes (V4-A3);
    - a body: 2^24 bytes;
    - items: 2^18 per `QUERY`, 2^16 per `SIGN`;
    - connections: 64;
    - signatures: 2^16 per lifetime.
  - Lifecycle: `vk` and `ready` on stdout; end of stdin makes the service wipe its keys and exit.
- **Signed-proof file** (`harness/FORMAT.md`).
  - Layout: `|π| ‖ π ‖ m ‖ (|q| ‖ q ‖ a)^m ‖ idx ‖ 133 ots ‖ 16 path`, every length a `u64`
    little-endian.
  - Strict: a file must be exactly one encoding.
  - It is the contract's `signedWords` without word padding. The witness-sending node proof embeds
    its children padded; the toy prover converts between the two.
- **Prover CLI** (`harness/PROVER.md`): `prover setup|tree|leaf|node DIR`.
  - Inputs: `leaves.json`, `leaf.json`, `child{1,2}.{stmt,bin}`, `vk.hex`, and `RF_ORACLE`.
  - Outputs: `proofs/L<i>.bin`, `proofs/N<l>_<j>.bin`, `root.bin`, `proof.bin`.
  - Handshake for `leaf` and `node`:
    1. the prover prints `ready`;
    2. the clock starts;
    3. the runner writes the inputs and `go`;
    4. the prover prints `done` or exits.
  - The sandbox's view and the build command are fixed.
- **Badge CLI** (header of `harness/rfh/checks.py`):
  - `verify --batch LIST` → `accept|reject NS`, where NS is the in-process time of parsing plus
    `accF` on a pinned core;
  - `chaincheck LEAVES ROOT_HEX`;
  - `liveness LOG VK STMT ROOT_FILE`.
- **Entry layout** (`harness/evaluate.py`):
  - `claim.json`: `error`, `completeness_error`, `qV`, `fuel_base`, `fuel_per_word`;
  - `lean/*.lean`, including `lean/Solution.lean`;
  - `prover/*.s`.
- **Result JSON** (`recursion.fast/v4/result-1`):
  - the verdict, the certificate (status, kernels, gate), the season and its hash;
  - per part, the machine (CPU model, image, memory-cap method);
  - toolchain versions; prover source and binary hashes; the harness commit; service and badge
    hashes;
  - the calibration: `T_triv,best`, the `T_V` cap, the service's calls/s and compressions/s,
    keygen time;
  - per tree repeat: `vk`, time, root and sample check times, canaries, service statistics;
  - per stream repeat: `vk`, every request's time, `t_leaf`, `t_merge`, `t_link`, the slowest
    merge;
  - the DoS column, liveness, the `T_V` summary;
  - the instance (starts published after the run);
  - the score (`S`, `o_est`, every repeat).

## 3. Measurements (development VM; not a GitHub runner)

### Service

| What | Result | Log |
|---|---|---|
| keygen (2^16 one-time keys and the tree) | 185 ms on 32 threads; 0.75–1.07 s on 4; 2.7–2.9 s on 1 with AVX2; 11.6–14.5 s on 1, scalar | `logs/service/measure-32vcpu.log`, `measure-4cpu.log` |
| round trip, one 32-byte `QUERY` | median 31 µs, p99 82 µs (on 4 CPUs: 34 µs) | same |
| `QUERY`, 1 connection | 30 k calls/s (batch 1); 2.6 M (256 × 64 B); **6.6 M** (4,096 × 64 B, 423 MB/s); 7.7 M (4,096 × 32 B); 528 MB/s with 64 KiB queries | same |
| `QUERY`, 32 connections | 98.7 M calls/s (4,096 × 64 B, 6.3 GB/s); 118.5 M (4,096 × 32 B); 8.7 GB/s (256 × 1 KiB) | same |
| `QUERY`, 4 CPUs and 4 connections (CI-sized) | 25.3 M calls/s (4,096 × 64 B) | `measure-4cpu.log` |
| `SIGN` | empty trace: 92–104 µs per request on one connection; 150 k/s on 32 | both |
| hashing in process | 62 ns per block with AVX2 (8 lanes); 265–445 ns scalar | both |
| calibration column (per job) | e.g. 4.8 M calls/s on 1 connection, 101 M on 32 (1,024 × 64 B) | each result JSON |

### Checks and calibration

| What | Result | Log |
|---|---|---|
| **`acc` on a 2^16-query trace** (100 B per query, 9.18 MB file; badge `verify` on a pinned core) | accept: **135–155 ms**. Reject at `SigOk` (changed answer or signature): 102–116 ms, of which `traceDigestF` is about 72 ms (stage A) and parsing about 30 ms | `logs/harness/accprobe.log` |
| **`T_triv,best`** (chain checker, season shape, `2^24` compressions, one pinned core) | **3.097 s**, 184.6 ns per compression (runs: 3.10, 3.44, 3.18 s). So `T_V` = 310 ms at `R = 10` | `logs/harness/chaincheck-season.log` |
| sandbox overhead | trivial program: 1.4 ms plain; 55 ms in the sandbox from spawn to teardown. Timed part of a T run (from the release of `exec` to the reported exit): **8.2 ms** median, so the toy's T run fell from 64 ms to 9.2 ms. Timed handshake of a stream request: **0.43 ms** | `logs/harness/sandbox-overhead.log` |
| witness-sending root check (smoke) | 50 ms for a 33,952-byte root, dominated by the verifier's word decoder (stage A open question 1) | `smoke-e2e.log` |

### Builds and jobs

| What | Result | Log |
|---|---|---|
| organiser build (`lake build`, cold for this package) | 2 min 54 s | `logs/lean/build-org.log` |
| `org-setup.sh` | first time 177 s, of which Lake's external C libraries took 138 s; compiled objects of the organiser's closure (964 Mathlib modules) 43 s; later runs 65 s | `logs/harness/org-setup.log`, `logs/org-setup/` |
| certificate job, witness-sending entry | 2 min 33 s, of which the comparator (Lean kernel) took 68–81 s | `logs/harness/eval-cert-ws.log`, `smoke-e2e.log` |
| **nanoda** on the same entry | **not finished: 17.6 GB RSS after 10 min 51 s**, still growing when the session stopped. It does not fit a 16 GB runner. The Lean kernel accepted the same export | `logs/harness/nanoda-ws.log` |
| benchmark job, smoke shape | 9.4 s | `logs/harness/eval-bench-ws.log` |
| axiom audit (compiled) | PASS, 28 s | `logs/lean/axiomaudit.log` |
| badge executables | 140 MB each (every object of the import closure is linked) | — |

## 4. Tests

| Test | Result | Log |
|---|---|---|
| `cargo test` | 4 unit tests: RFC 7693 `"abc"`; the empty message; AVX2 = scalar on 20 lengths, keyed and unkeyed; the WOTS digits | — |
| `tests/service/test_service.py` | **89 checks pass**: see the list below | `logs/service/test_service.log` |
| `tests/service/test_lean_signer.py` | **byte-identical to stage A's compiled Lean signer**: the service's `vk` and its first two signatures (an empty trace; 3 queries). The Lean `SigOkF` accepts them | `logs/service/test_lean_signer.log` |
| `tests/harness/test_sandbox.py` | **45 checks pass** against a hostile prover: see the list below | `logs/harness/test_sandbox.log` |
| `tests/gate/check.sh` | pass: the witness-sending certificate (9,767 constants, standard axioms); the backdoor, with `V`, `P`, `ext` compiled one by one. Rejected: a noncomputable `ext` (rule 4), `@[implemented_by]` (rule 3), a `partial` verifier (rule 2) | `logs/harness/gate-fixtures.log` |
| `tests/source-rule/check.sh` | 95 rejected forms and 4 forgeries caught (v3's fixtures) | — |
| axiom audit (stage A's, compiled in `harness/lean-tools`) | PASS on all `RecursionFast.*` modules | `logs/lean/axiomaudit.log` |
| `tests/harness/smoke.py --mock` | the runner with a Python stand-in badge: honest PASS; the three broken provers rejected | `logs/harness/smoke-mock.log` |
| `tests/harness/smoke.py --org` | as in the summary at the top | `logs/harness/smoke-e2e.log` |

The 89 service checks:

- keyed BLAKE2s against `hashlib` on messages of 0 to 65,536 bytes, the empty one included, in
  mixed batches, on both SIMD paths;
- signatures byte for byte against an independent Python reading of BRIEF §4.2 and V4-A4, and the
  full `vk` against Python's tree;
- the liveness log;
- ten malformed or over-cap requests, each refused;
- a query of exactly 2^20 bytes, answered;
- 32 concurrent connections, and a 65th refused;
- fresh keys for every service, and the runner refusing a service with test keys;
- exactly 2^16 signatures, then `EXHAUSTED`;
- clean shutdown.

The 45 sandbox checks:

- These escape attempts fail:
  - seeing other processes or reading `/proc/*/mem`;
  - `ptrace`, `process_vm_readv`, `bpf`, `perf_event_open`, `userfaultfd`, `io_uring`, `keyctl`;
  - creating a user namespace;
  - reaching the network;
  - writing to any read-only path or to `/`;
  - reading host files or the outer environment.
- Garbage sent to the service leaves it answering.
- The reader refuses a symbolic link, a FIFO and a linked directory as outputs.
- A detached grandchild is killed with the run.
- The memory cap: at 64 MiB it kills a prover touching 200 MiB, not one touching 16 MiB.
- The `ready`/`done` handshake works and `step_s` is enforced.
- `.incbin` of a host file fails in the sandboxed build.

## 5. Security argument

### 5.1 What an untrusted prover can and cannot do

**The sandbox** (`bwrap`):

- **Namespaces:** new user, pid, network, ipc, uts and cgroup namespaces; no further user
  namespaces (`--disable-userns`); all capabilities dropped; a new session; an empty environment.
- **Filesystem:** an empty, read-only tmpfs root holding only:
  - the binary (read-only), its own `/work`, `/setup` (read-only) and the socket's directory
    (read-only);
  - a private `/tmp`, a minimal `/dev`, its own `/proc`, the CPU topology.
- **Seccomp:** these calls fail with EPERM: `ptrace`, `process_vm_*`, `kcmp`, `pidfd_getfd`,
  `bpf`, `perf_event_open`, `userfaultfd`, `io_uring_*`, the keyrings, every mount call,
  `unshare`/`setns`, module and kexec loading, handle-based opens. Another syscall ABI kills the
  process.
- **Memory:** a capped scope (`MemoryMax`, no swap), with `oom_score_adj = 1000`.
- **End of run:** when its first process exits or is killed, the pid namespace takes every
  descendant with it, and the scope is killed too.

**It cannot:**

- **Read the service.**
  - The keys never touch disk.
  - The service is in another pid namespace, which the prover cannot name.
  - The service is non-dumpable (`PR_SET_DUMPABLE = 0`), so a process of the same uid cannot
    attach to it or read `/proc/PID/mem`.
  - `ptrace` and `process_vm_*` fail by seccomp.
- **Reach the network**, or any socket other than the service's.
- **Read host files.** They are absent. The build sandbox shows only `/usr` and the copied `.s`
  files.
- **Write outside `/work`** (and `/tmp`, which counts against its memory).
- **Keep state between requests.** Every request gets a fresh directory, and `/setup` is read-only
  after `setup`.
- **Mislead the runner through its outputs.** They are read without following links or blocking,
  must be regular files, and are capped at 64 MiB.
- **Outlive its request.**

**It can:**

- **Use every CPU of the machine.** The service computes on the same CPUs, so it is no free
  co-processor.
- **Hurt itself.** It can exhaust its memory, hang until `step_s`, or crash the service by its own
  traffic. The service has its own 2 GB scope and the default `oom_score_adj`. If the service dies,
  the run aborts as the entry's failure (V4-A4); it is never restarted.
- **Learn the 16-bit index of each signature** (C-m2), and the size-dependent time of a query. The
  service keeps no answer table (V4-A5).
- **Write large files into `/work`**, limited by the 64 MiB read cap and the job's disk.

**Deviation (orchestrator's item (b)): namespaces instead of a separate uid.**

- What runs where:
  - the service runs as the job's user, in its own memory scope (2 GB);
  - the prover runs in another scope (11 GB);
  - BRIEF §2 and §4.3 say "own uid".
- The isolation that matters holds without a second user:
  - the pid namespace;
  - the non-dumpable service;
  - seccomp;
  - no shared memory;
  - an interface that is a socket only.
- Creating users would change the development VM, which the stage forbids.
- On CI, `sudo` would allow a service user, but the runner has no `service_user` option yet (open
  question 3).
- The two cgroups replace V4-13's single 13 GB cgroup for prover and service together:
  - a prover cannot make the OOM killer pick the service (C-m4);
  - the service's buffers do not count against the prover.

### 5.2 The Lean steps (V4-A1)

The entry's `lake build` runs inside `bwrap` twice: once through the comparator's landrun shim,
once in the gate tree. The gate and the badge build run inside it too.

- **The shim** (`scripts/bwrap-landrun.sh`, minimal mode):
  - shows only `/usr`, the toolchain, the organiser checkout and the package tree (read-only) and
    the tree's `.lake` (writable);
  - applies the same seccomp filter, with no network and an empty environment.
- **The comparator runs outside the sandbox**, as in v3, so the entry's build cannot fake its
  verdict. It runs under a 14 GB memory cap, with the Lean kernel, and with nanoda where it fits
  (it does not at 16 GB, §3).
- **Manifest and binding:**
  - the organiser's oleans are checked against the manifest before and after every step;
  - the gate tree's artifacts must equal the comparator's byte for byte.
- **The badge build:**
  - it may write compiled objects into the package tree, for modules an entry adds beyond the
    organiser's prebuilt closure;
  - no entry code runs in it: the entry's modules are loaded, not elaborated, and gate rule 3
    excludes load-time code;
  - the manifest is checked afterwards.
- **What remains is O-12** (v3): the compiled code of the entry's `V` comes from the entry's own
  elaboration. The source rule and gate rules 3 and 6–8 make it harder to abuse, but do not close
  it.

### 5.3 CI isolation (V4-A1, V4-A2)

1. **Trigger.**
   - The submissions repository runs `evaluate-entry.yml` from its default branch, by
     `pull_request_target` gated by the `evaluate` label, or by `workflow_dispatch` with a PR
     number.
   - A PR that edits the workflow changes nothing until it is merged.
2. **Select job** (read-only).
   - It requires the PR to touch exactly one `submissions/<entry>/` root.
   - It pins the labelled head SHA.
3. **Evaluation.** The core's reusable `evaluate.yml`, at a pinned commit, runs three kinds of job:
   - `certificate` (`contents: read`);
   - `benchmark` (`contents: read`; six jobs with `split`);
   - `attest` (`id-token`, `attestations`; runs no entry code).
4. **Fetching the entry.** `fetch-entry.sh`:
   - fetches the entry by SHA with plain git;
   - never checks out the fork with `actions/checkout` and never uses `allow-unsafe-pr-checkout`;
   - persists no credentials, and the jobs hold no secrets;
   - refuses links and special files.

   Untrusted bytes run only inside the sandbox.
5. **Report job.** It may write a PR comment. It reads the result JSON as data and runs no entry
   code.

**Accepting a record.** A result counts only if this passes:

```sh
gh attestation verify result.json --owner scaraven \
  --signer-workflow scaraven/recursion.fast/.github/workflows/evaluate.yml
```

The attested JSON binds:

- the verdict, `vk`, the CPU model and the runner image;
- the harness commit;
- the hashes of the service, the badge and the prover.

**What a malicious pull request still has:**

- **A sandbox escape on its own runner.** The benchmark's integrity rests on the sandbox, as v3's
  did on landrun; the separate attest job does not change that.
- **The 6-hour job.**
- **The maintainer's approval as a first-time contributor.** That approval admits it to compute;
  it is not a verdict.

**Runner set-up** (`runner-setup.sh`):

- Ubuntu 24.04 restricts user namespaces through AppArmor. The script relaxes this for the job
  (`kernel.apparmor_restrict_unprivileged_userns=0`), so bwrap works without setuid.
- It enables lingering, for systemd user scopes.
- If no user manager is reachable, the memory cap falls back to `prlimit --as`, and the result
  records `memcap: prlimit`.

### 5.4 The 6-hour limit (orchestrator's item (a))

With `split` (the default in `evaluate.yml` and the template), the benchmark is six jobs:

| Job | Runs |
|---|---|
| 1 | calibration, one tree repeat, the DoS column, liveness |
| 2, 3 | one tree repeat each |
| 4, 5, 6 | one stream repeat each |

- **Each job:**
  - builds the prover from the same `.s` files;
  - runs its own service lifetimes;
  - measures its own `T_triv,best` and service throughput;
  - checks its outputs against its own `T_V`.
- **`aggregate.py`:**
  - takes the medians over the three tree repeats and the three stream repeats;
  - lists each job's CPU model;
  - marks a result whose jobs ran on different CPU models `mixed_cpu`. Such a result is not used
    for a paired (ABBA) record comparison. A paired comparison runs incumbent and challenger in the
    same job, one part at a time.
- `split: false` runs everything in one job (the smoke shape).

## 6. Amendments V4-A1 … A7 as implemented here

- **V4-A1:** the trust anchor, permissions, fetch by SHA, entry code only in the sandbox (Lean
  build, gate and badge included), the empty environment, and the attested result (§5.3).
- **V4-A2:**
  - the certificate and benchmark jobs are separate;
  - the Lean kernel is mandatory;
  - nanoda runs with `--nanoda`, and its absence is stated in the result (`second_kernel`);
  - the measured cap: nanoda does not fit in 16 GB (§3).
- **V4-A3:**
  - the service caps queries at 2^20 bytes;
  - the badge calls `accF`, which follows the contract: the size cap, the query cap, `SigOk`, then
    `runSeq` with exact consumption.
  - RA-M2's `p.tr.length ≤ S.qV` will come with `accF`. The badge needs no change, and the `acc`
    probe's submission already declares `qV = 2^16`.
- **V4-A4:**
  - an independent seed;
  - the chain start `0x53 ‖ enc64 j ‖ byte i`;
  - the index taken by one atomic step before signing, and never reused;
  - a dead service aborts the run.

  Tested against Python and the compiled Lean signer.
- **V4-A5:**
  - no memoisation;
  - every cap refused as an error;
  - `oom_score_adj`;
  - the empty-message vector;
  - `sign` re-evaluates (documented);
  - the calibration column in every result.
- **V4-A6:**
  - the build runs in the sandbox;
  - the result records the image version, the gcc, as, ld, glibc and bwrap versions, and the
    source and binary hashes;
  - seccomp;
  - the AppArmor relaxation in the workflow.
- **V4-15 / C-m13:**
  - a provisional entry still passes the source rule, the sandbox and gate rules 2–8;
  - only an open certificate is tolerated: the comparator's failure and gate rule 1 on `sorryAx`;
  - its result says `comparable: false`.

## 7. Deviations from the BRIEF, with reasons

1. **Namespaces and two cgroups** instead of a separate uid and one 13 GB cgroup (§5.1).
2. **The badge parses the file at byte level**, instead of through the contract's `readSigned`.
   - The word path costs about 0.4 µs per byte (stage A §4), so about 0.4 s at `proofCap`, above
     `T_V`.
   - The parser is 30 trusted lines of strict reading.
3. **`T_V` is the badge's in-process time** of parsing plus `accF` on a pinned core, not the
   process's rusage.
   - On one pinned core, wall time bounds CPU time from above.
   - Excluding start-up keeps the smoke shape meaningful.
   - At the smoke shape `T_V` is reported, not enforced (`tv.enforce = false`), because the trivial
     check takes 0.1 ms there.
4. **The T run is timed** from bubblewrap's release of the held `exec` to its exit report. This
   excludes the sandbox's set-up and tear-down; v3 timed the whole process. 8 ms of overhead remain
   (§3).
5. **The Lean tools build in a standalone package.** The gate, the axiom audit and the chain
   checker build in `harness/lean-tools`, which has no dependencies.
   - Executables in the main lakefile would link, and build, every package's C libraries.
   - So no `[[lean_exe]]` was added to `lakefile.toml`.
   - The badge executables are rendered into the evaluation tree's own lakefile.
6. **The badge executables are 140 MB** and need compiled objects of the entry's whole import
   closure. `org-setup.sh` prebuilds the organiser's closure (§3). An entry that imports more
   Mathlib modules pays for compiling them in its badge build.
7. **The DoS column** draws 1,000 proofs (64 at the smoke shape):
   - random bytes;
   - random `π` with the root's trace and signature;
   - bit flips in `π`;
   - bit flips or truncations of the whole file.

   Any accept or crash rejects the entry.

## 8. Open questions

1. **The second kernel on CI.** nanoda exceeds 16 GB on the witness-sending entry: at least
   17.6 GB, not finished (v3: 52 GB on a field lemma). The options:
   - run the certificate job on a larger, self-hosted or paid runner;
   - state in the rules that CI checks with the Lean kernel only (C10, v3 §15.4).

   The user's decision.
2. **No run on GitHub yet.** Still unmeasured on a runner:
   - the AppArmor relaxation, lingering and the systemd user scopes;
   - the runner's `T_triv`, service throughput and certificate-job time;
   - the disk: the Mathlib cache, the compiled objects, two 140 MB badges.
3. **A service user on CI** would add a uid boundary to the namespace one: `sudo useradd`, with the
   socket at mode 0666 in a directory the prover can see. The runner does not have this option yet.
4. **Liveness at real sizes.** The badge builds the whole log as a Lean `List` and the tape as
   `List Word`, and `Word = BitVec 64` is a `Nat` at run time (stage A open question 2). For a
   Flock-class prover's log at `r = 1`, `n = 16` (10^6–10^7 entries) this may need gigabytes.
   Unmeasured.
5. **The service's speed decides part of every score** (C-m8). Two improvements are not built:
   - AVX-512, with 16 lanes and native rotates, where a runner has it. This would make runners
     less uniform.
   - Shared-memory rings instead of a socket (D4 §4.8). Today the round trip is 31 µs, and batches
     of 4,096 reach 6.6 M calls/s per connection.
6. **The quality of `T_triv,best`.** The chain checker interleaves 8 chains at 185 ns per
   compression, about the same as v3's unrolled sequential checker (151–164 ns). A better checker
   tightens `T_V`. Stage R's run-time golf may find one.
7. **Two directories I created in the shared package tree on 2026-10-22:** `VCVio/.lake` and
   `leansqlite/.lake`, static C libraries from one `lake build gate`. My attempt to remove them was
   denied; the orchestrator is reporting them to the user.

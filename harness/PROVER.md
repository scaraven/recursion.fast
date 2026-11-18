# The prover interface (normative)

The efficient prover of an entry is an **x86-64 Linux program submitted as GNU assembly**.
The runner builds it, runs it in a sandbox, and measures it. Everything it produces is checked by
the compiled `acc` (`harness/FORMAT.md`); nothing it says is trusted.

## 1. Build

- Sources: the entry's `prover/*.s` (AT&T or `.intel_syntax`), nothing else. Sources in any other
  language may sit beside them for readers; they are not built.
- **The reference toolchain is the evaluation VM's**, and it is part of the rule:
  - Ubuntu 24.04's GCC 13.3, GNU Binutils 2.42 (`as`, `ld`), glibc 2.39 (static);
  - every result records the exact `gcc`, `as`, `ld` and glibc version lines.

  The `.s` files must assemble with **that** `as`. Assembly emitted by a newer compiler may use
  directives it rejects: GCC 15's `.base64`, LLVM 23's `.prefalign` and DWARF-5 `.file` forms.
  `harness/tools/asm-compat.py IN.s OUT.s` (untrusted, a convenience) rewrites them; the
  committed toy prover went through it. CI assembles every committed `.s` file with the image's
  toolchain first.
- Command, inside the build sandbox, in a directory holding only copies of the `.s` files,
  within `build_s` (2 min in season 1):

  ```
  gcc -static -O2 -pthread /build/*.s -o /build/prover -lm
  ```

  with the evaluation VM's `gcc`, `as`, `ld` and static glibc. `.include` and `.incbin` see only the
  copied `.s` files and the toolchain (no other file of the machine). The result records the
  tool versions, every source's SHA-256 and the binary's SHA-256.
- The machine is an AMD Ryzen 7 PRO 8700GE (Zen 4); the benchmark VM has 4 cores / 8 threads at
  a fixed 3.65 GHz with the host CPU passed through: x86-64-v4 with AVX-512, GFNI, VAES,
  VPCLMULQDQ and SHA-NI (the full list in `AGENTS.md` §6). The machine may change between seasons:
  detect features at run time (`cpuid`) and keep a portable fallback. A `SIGILL` fails the run.

## 2. The sandbox (what the prover sees)

| path | contents |
|---|---|
| `/prover/prover` | the binary (read-only) |
| `/setup` | the setup directory (read-only after `setup`) |
| `/work` | the request's own directory, read-write, the working directory (fresh for every request) |
| `/run/rf/oracle.sock` | the oracle service's socket (`RF_ORACLE`) |
| `/tmp` | an empty tmpfs (counted in the memory cap) |
| `/dev`, `/proc` | minimal devices (`null`, `zero`, `urandom`, …); `/proc` lists only the prover's own processes, but `/proc/stat`, `/proc/cpuinfo` and `/proc/meminfo` are the machine's (global) |
| `/sys/devices/system/cpu` | the CPU topology (read-only) |

Nothing else exists: no `/usr`, no shell, no network, no other process. The environment is
`RF_ORACLE=/run/rf/oracle.sock`, `RF_SETUP=/setup`, `HOME=/work`, `TMPDIR=/tmp`, `PATH=/prover`.
Resources: every CPU of the machine (shared with the service, which computes the oracle on the same
CPUs), memory capped by a cgroup (`memory.prover` of the season, 8 GiB in season 1; the service
has its own 2 GiB), `oom_score_adj = 1000`. A seccomp filter fails (EPERM) `ptrace`,
`process_vm_*`, `bpf`, `perf_event_open`, `userfaultfd`, `io_uring_*`, key management, mounts,
namespaces and module loading. When a request ends, every process the prover started is killed.

## 3. Invocations

All paths below are relative to `/work` unless absolute. Statements and keys are 64 lowercase hex
characters plus an optional newline; `vk.hex` is the service's public key. A leaf file is
`{"n": N, "seed": "HEX"}`: the leaf of `N` parallel hashes of the 32-byte seed. The public hashes
are Ethereum's Keccak-256 (rate 136 bytes, padding `0x01 … 0x80`, not SHA3-256) of tagged inputs:
`leafItem s j = Keccak-256(0x48 ‖ s ‖ u64 j)` (41 bytes, one Keccak-f[1600] permutation),
`leafValue s n` = the XOR of `leafItem s j` over `j < n` (the zero digest for `n = 0`),
`leafStmt h n = Keccak-256(0x4C ‖ h ‖ u64 n)`, `nodeStmt c1 c2 = Keccak-256(0x4E ‖ c1 ‖ c2)`
(`RecursionFast/Contract/Relation.lean`; `u64` little-endian). A leaf's `n` hashes are independent:
they can be computed in any order, on any number of threads.

### `prover setup /setup` (optional, untimed)

Runs once per evaluation, before any instance or service exists, with `/setup` writable and no
socket. It may write tables, keys or code there, within `setup_s` (4 min in season 1) and
`setup_cap` (the directory holds at most 4 GiB in at most 2^20 entries afterwards, sparse files at
their size, and must be hashable within that and 60 s; otherwise the setup fails).
A prover with nothing to set up exits 0.

### The stream: `prover first /work`, then `prover step /work` (timed per request)

**One benchmark, pure IVC** (AGENTS.md §6). An evaluation is one stream of `M` steps (`M = 8` in
season 1, 4 in the smoke) under one service lifetime, run once against the service and then twice
more, timed, against its replay (below). Every step is a fresh process in a fresh sandbox (fresh
`/work`, fresh `/tmp`, read-only `/setup`); nothing survives a request except the proof the runner
copies, so **state between steps travels only inside `π`**.

Every step proves one fresh leaf of exactly `n` hashes (`n = 2^22`, the contract's `leafCap`, in
season 1; 64 in the smoke), `n_i = n` permutations per step:

```
L_i = leafStmt (leafValue s_i n) n
c_1 = L_1,        c_i = nodeStmt c_{i-1} L_i                          (i = 2 … M)
```

- **Step 1** (`prover first /work`): input `leaf.json` (`n` and the seed `s_1`). Output
  `proof.bin`: a signed proof of `c_1 = L_1`.
- **Step i ≥ 2** (`prover step /work`): inputs `prev.stmt` (`c_{i-1}`), `prev.bin` (the previous
  step's output, exactly as the runner received it in the service run) and `leaf.json` (`s_i`).
  Output `proof.bin`: a signed proof of `c_i = nodeStmt c_{i-1} L_i`.

A step may make any number of `SIGN` requests within the lifetime's budget of `2^16` signatures (a
node needs signed proofs of its children as its witness). The runner computes every statement
itself and checks outputs against them (below).

**What is fixed, what is drawn, and what is told** (AGENTS.md §6). The shape is **fixed and
published**: `M` and the one leaf size `n` (`[stream]` of `harness/season.toml`;
`harness/smoke.toml` has its own), the same for every evaluation and every entry. The **seeds**
(one per step) are fresh secret draws per evaluation from the OS CSPRNG, published only after the
run; a step learns its seed only when its inputs arrive.

**The two runs** (AGENTS.md §6).

1. **The service run** (untimed): the stream as above against the service, under `step_s` per
   request and the benchmark's `stream_s`. No key is anywhere in the prover's reach. Its times are
   recorded (`P_service_s`), never scored. Every output is kept and checked (below) before any
   secret is revealed.
2. **The timed passes** (`timed_runs = 2`): the runner removes every request directory of the
   service run, then, before each pass, puts the service in **replay mode**: it reveals its PRF key
   `k`, resets its one-time-key counter to 0, and from then on answers `SIGN` at index `j` only if
   the trace digest equals the one it signed at index `j` in the service run (it returns that same
   signature), else it refuses with status 4 `MISMATCH` (`service/PROTOCOL.md`); `QUERY` is served
   unchanged. Each pass runs steps `1 … M` again, each a fresh sandbox, with the same leaf, the
   runner's `prev.stmt`, the **service run's** output of step `i − 1` as `prev.bin`, and one more
   input, **`oracle.key`**: `k` as 64 lowercase hex characters and a newline, staged with the other
   inputs, so it appears in `/work` only when the clock runs (every `k`-dependent computation is
   timed). A prover may use `k` to compute oracle answers itself instead of asking the service, or
   ignore it; it may branch on whether `/work/oracle.key` exists.

**Determinism is required.** Each timed output must be **byte-identical** to the service run's
output of that step; otherwise the entry is REJECTed, the reason naming the pass, the step and the
first differing byte offset. A prover's output must be a function of its inputs, its setup and the
oracle answers: no clock, no `/dev/urandom`, no thread-order dependence in what it writes, a
deterministic grinding order (for example the least nonce in a fixed search order), and its `SIGN`
requests in an order its inputs fix (the service assigns one-time indices in the order `SIGN`
requests arrive, and a replay refuses any other digest at an index). **A timed pass must make
exactly the service run's `SIGN` requests**: any replay `MISMATCH` (in any pass), and any total
other than `timed_runs` times the service run's signatures, is the entry's REJECT (a refusal at an
index would otherwise be a bit carried from the service run into a timed pass).

**The handshake** (per request):

1. The runner starts the process (with `vk.hex` already in `/work`). The prover loads its setup and
   prints the line **`ready`** on stdout within `ready_s` (10 s). Start-up is untimed (reported).
2. The runner writes the inputs to a staging directory the prover cannot see, **starts the
   clock**, renames them into `/work` (constant time, whatever their size) and writes the
   line **`go`** on the prover's stdin.
3. The prover writes `/work/proof.bin` and prints the line **`done`** (or exits). At `done`, or at
   the prover's exit, the runner kills **every process of the sandbox at once and stops the clock
   when all of them are dead**. Only then is `proof.bin` read. So work done after
   `done` (a thread, a forked child) is either on the clock or never happens: no byte written after
   the clock stopped exists. A prover that closes stdout without `done` is timed until its last
   process exits. The cap is `step_s` (60 s) from the inputs to the death of the last process.

**Before every request** (untimed, with no entry process alive) the runner reads every regular file
of `/setup` and the binary in full, so every page of the files that outlive a request is in the page
cache: their cache state carries nothing from one request to the next.

`/work` is on a tmpfs where the machine has one: what the prover writes there counts against its
memory cgroup. When the prover is dead, `/work` may hold at most `work_cap` (4 GiB, a sparse file at
its size) in at most 65,536 entries. **Any failure the runner meets while the prover's sandbox
exists, or because of what a prover left behind, is the entry's failure**: an input's name
taken, the directory made unreadable, the filesystem filled so that the runner's own writes fail,
files the runner cannot remove, the filesystem left fuller after cleanup.

**The checks of the service run** (AGENTS.md §6, §7), never while an entry process is alive:

- every output's size is at most `pi_cap` (1 MiB): its `|π|` if it parses as a signed proof
  (`harness/FORMAT.md`) that `acc` accepts, else its file size;
- the intermediate outputs are checked with `acc` under the run's `vk` against the runner's
  statements `c_i`, in batches of `check_every` (8) between steps, each batch warmed by an untimed
  check of its first output, each `V_i` one measurement on one pinned core;
- the **final** output (step `M`) is then checked on its own: it must be accepted, with
  `|π_M| ≤ final_pi_cap` (512 KiB) and `V_M ≤ v_cap` (128 ms; above it the check is timed twice more
  and the minimum counts), and its statement canaries rejected (`c_M` with its first bit flipped,
  and its first child `c_{M-1}`): the track **`final`**. A crash or timeout of these checks is the
  entry's REJECT;
- the track **`every`** additionally needs every intermediate output accepted with `V_i ≤ v_cap`
  (timed twice more above it, the minimum) and the statement canaries of outputs 1 and 2 rejected
  (output 1, a leaf, has no first child: only its flipped statement). An entry that meets `final` but not `every` is
  scored in `final` only, the result saying why (`score.tracks_reason`); intermediate outputs need
  not be proofs at all. A crash or timeout of an intermediate check, or of the canaries of outputs
  1 and 2, costs only the track `every` (such a badge run is bounded by 60 s plus 2 `v_cap` per
  check); once the track is lost, no intermediate is timed again and those canaries are skipped.

The final output's checks have no time cap of their own. Calibration samples (AGENTS.md §6) are
taken before the service run's step 1 (and every `every` steps), before each timed pass, and a
closing one if 30 s of `stream_s` remain. The whole benchmark, the service run, every request, check,
canary, calibration sample and both timed passes, runs within `stream_s` (3,000 s, wall time; the
season file's value binds, and a later season may set another); reaching it is the entry's
REJECT.

**The score** (AGENTS.md §7; one score, both tracks; lower is better, seconds):

```
S       = P_total · 2^(|π_M| / 1 MiB)
P_total = Σ_i P_i                       the stream's wall time
P_i     = the minimum of step i's two timed times
```

`|π_M|` the bytes of the final output's `π` alone. `V` is not scored (it is capped), nor the size of
any intermediate output (capped), nor the service run's times. Only the total counts: moving work
between steps (deferring it to the last one included) changes nothing. The per-step records
(`WORK/stream.jsonl`, and `stream.steps` in the result) give the service run's time, both timed
times, `|π|`, `V` and each step's share of `P_total`.

## 4. The oracle

Every oracle query a prover needs, Merkle hashes included, goes to the service:
`QUERY` batches for answers while proving, one `SIGN` per output proof with the verifier's query
sequence (the service re-computes those answers and signs their trace digest). See
`service/PROTOCOL.md`. The answer to a query `q` is `Keccak-256(k ‖ q)` under the service's 32-byte
secret key `k`: `floor((32 + |q|) / 136) + 1` permutations (one for `|q| ≤ 103` bytes). Use one
connection per thread and batches of hundreds to thousands of
queries. The service's measured throughput on the job's machine is published in every result
(`calibration.service`).

## 5. What fails a run

A prover build or setup that fails or exceeds `build_s`, `setup_s` or `setup_cap`; a request (of the
service run or of a timed pass) with no `ready` line within `ready_s`, a non-zero exit, a timeout of
`step_s`, or a missing, non-regular or over-cap (`file_cap`, 64 MiB) `proof.bin`; any output above
`pi_cap`; a final output that `acc` rejects, above `final_pi_cap`, with `V_M` above `v_cap` (the
minimum of three checks), or whose statement canary `acc` accepts; a timed output that is not
byte-identical to the service run's output of its step; a replay `MISMATCH`, or a timed pass that
does not make exactly the service run's signatures; a crash or timeout of the final output's checks; a
filesystem error the prover caused in `/work`; the service dying during the run; the benchmark
reaching `stream_s`. An intermediate output that `acc` rejects (or rejects when timed again), or
above `v_cap`, a canary of output 1 or 2 that `acc` accepts, or a crash or timeout of their checks,
does not fail the run: it leaves the entry out of the track `every`. Every job of an evaluation ends within 30 minutes, the certificate job within 50 and the
benchmark job within 70, and these caps are nested inside them. The first failure ends the
evaluation (`harness/run-benchmark.py`). The reason in the result names the cause: the prover's
output (its first 16 KiB and last 48 KiB are kept; the reason quotes the tail), the service's
refusals of this run (`rf-oracle: refused (status S): MESSAGE`, e.g. a query above 2^20 bytes, or a
replay `MISMATCH`), and a kill by the memory cgroup (`killed: out of memory (cap …, peak …)`).

## 6. The Lean side's caps (the certificate job)

Each within the certificate job of 50 minutes on the evaluation VM (`[certificate]` of the
season file): the entry's `lake build` of the challenge and `Solution`'s import closure 1,200 s; the kernel's
check of the exported proofs 600 s (a breach leaves the certificate unchecked: PROVISIONAL); the
gate 120 s; the badge build 180 s. The badge build compiles the object code of every module of
`Solution`'s import closure that the organiser has not precompiled. Precompiled, once per core
commit: the import closures of `RecursionFast`, `CompPoly.Fields.Binary.BF64.Ext3`, `.Bytes` and
`Mathlib.Tactic` (`harness/org-setup.sh` step 4). The entry's own modules and any other module it
imports are compiled inside the 180 s, at about 4.8 objects per second on 4 cores (measured on an
organiser workstation): about 860 such modules fit; `import Mathlib` (about 5,700 more) does not.

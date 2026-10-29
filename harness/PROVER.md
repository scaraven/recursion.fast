# The prover interface (normative)

The efficient prover of an entry is an **x86-64 Linux program submitted as GNU assembly**
(BRIEF P4, V4-9). The runner builds it, runs it in a sandbox, and measures it. Everything it
produces is checked by the compiled `acc` (`harness/FORMAT.md`); nothing it says is trusted.

## 1. Build

- Sources: the entry's `prover/*.s` (AT&T or `.intel_syntax`), nothing else. Sources in any other
  language may sit beside them for readers; they are not built.
- **The reference toolchain is the runner image's**, and it is part of the rule:
  - GitHub's `ubuntu-24.04` image (the result records `ImageOS` and `ImageVersion`; season 1 was
    first run on `ubuntu24 20261012.334.1`);
  - GCC 13.3, GNU Binutils 2.42 (`as`, `ld`), glibc 2.39 (static);
  - every result records the exact `gcc`, `as`, `ld` and glibc version lines.

  The `.s` files must assemble with **that** `as`. Assembly emitted by a newer compiler may use
  directives it rejects: GCC 15's `.base64`, LLVM 23's `.prefalign` and DWARF-5 `.file` forms.
  `harness/tools/asm-compat.py IN.s OUT.s` (untrusted, a convenience) rewrites them; the
  committed toy prover went through it. CI assembles every committed `.s` file with the image's
  toolchain first (RF-M2).
- Command, inside the build sandbox (V4-A6), in a directory holding only copies of the `.s` files,
  within `build_s` (2 min in season 1, V4-A11):

  ```
  gcc -static -O2 -pthread /build/*.s -o /build/prover -lm
  ```

  with the runner image's `gcc`, `as`, `ld` and static glibc. `.include` and `.incbin` see only the
  copied `.s` files and the toolchain (no other file of the machine). The result records the
  image version, the tool versions, every source's SHA-256 and the binary's SHA-256.
- The binary must run on every CPU model of the runners (GitHub-hosted `ubuntu-24.04`: AMD EPYC and
  Intel Xeon; AVX2 and carry-less multiply available, AVX-512 and GFNI not guaranteed): dispatch on
  `cpuid`. A `SIGILL` fails the run.

## 2. The sandbox (what the prover sees)

| path | contents |
|---|---|
| `/prover/prover` | the binary (read-only) |
| `/setup` | the setup directory (read-only after `setup`) |
| `/work` | the request's own directory, read-write, the working directory |
| `/run/rf/oracle.sock` | the oracle service's socket (`RF_ORACLE`) |
| `/tmp` | an empty tmpfs (counted in the memory cap) |
| `/dev`, `/proc` | minimal devices (`null`, `zero`, `urandom`, …); `/proc` lists only the prover's own processes, but `/proc/stat`, `/proc/cpuinfo` and `/proc/meminfo` are the machine's (global) |
| `/sys/devices/system/cpu` | the CPU topology (read-only) |

Nothing else exists: no `/usr`, no shell, no network, no other process. The environment is
`RF_ORACLE=/run/rf/oracle.sock`, `RF_SETUP=/setup`, `HOME=/work`, `TMPDIR=/tmp`, `PATH=/prover`.
Resources: every CPU of the machine (shared with the service, which computes the oracle on the same
CPUs), memory capped by a cgroup (`memory.prover` of the season, 11 GiB in season 1; the service
has its own 2 GiB), `oom_score_adj = 1000`. A seccomp filter fails (EPERM) `ptrace`,
`process_vm_*`, `bpf`, `perf_event_open`, `userfaultfd`, `io_uring_*`, key management, mounts,
namespaces and module loading. When a request ends, every process the prover started is killed.

## 3. Invocations

All paths below are relative to `/work` unless absolute. Statements and keys are 64 lowercase hex
characters plus an optional newline; `vk.hex` is the service's public key. A chain file is
`{"n": N, "start": "HEX"}`: the chain of `N` steps from the 32-byte start.

### `prover setup /setup` (optional, untimed)

Runs once per evaluation, before any instance or service exists, with `/setup` writable and no
socket. It may write tables, keys or code there, within `setup_s` (4 min in season 1) and
`setup_cap` (the directory holds at most 4 GiB in at most 2^20 entries afterwards, sparse files at
their size, and must be hashable within that and 60 s; otherwise the setup fails, V4-A11 R-M1).
A prover with nothing to set up exits 0.

### The stream: `prover first /work`, then `prover step /work` (timed per request)

**One benchmark, pure IVC** (V4-A11 §2). An evaluation is one stream of `M` steps under one service
lifetime; every step is a fresh process; nothing survives a request except the proof the runner
copies, so **state between steps travels only inside `π`**.

- **Step 1** (`prover first /work`): inputs `chainA.json`, `chainB.json`. Output `proof.bin`: a
  signed proof of `nodeStmt (leafStmt (chainEnd a nA) nA) (leafStmt (chainEnd b nB) nB)`.
- **Step i ≥ 2** (`prover step /work`): inputs `prev.stmt`, `prev.bin` (the previous step's
  statement and its signed proof, exactly as the runner received it) and `chain.json`. Output
  `proof.bin`: a signed proof of `nodeStmt prev (leafStmt (chainEnd s n) n)`.

A step may make any number of `SIGN` requests within the lifetime's budget of `2^16` signatures (a
node needs a signed proof of its leaf child as its witness). The runner computes every statement
itself; every output is checked with `acc` under the run's `vk` against that statement, and must
be accepted.

**What is drawn, and what is told** (§3). Fresh per evaluation from the OS CSPRNG, published only
after the run: each chain's
length i.i.d. with density `∝ 1/n²` on `[2^17, 2^20]` (equal expected work per octave; step 1's
two chains too); the starts. A step learns its own length only when its inputs arrive. The number of
steps is **not** drawn: `M = 96` in season 1 (6 in the smoke), the same for every entry. Two cross-step side channels exist and are harmless given the re-timing rule below
(§11 m-6): the signature index the service returns (how many signatures this lifetime made) and
`CLOCK_REALTIME`. With `M` public a step can count its position anyway;
leaving the last few chains to the final check gains about 0.4–1.0 % at most (estimate), because
the verifier charge prices the work it creates.

**The handshake** (per request):

1. The runner starts the process (with `vk.hex` already in `/work`). The prover loads its setup and
   prints the line **`ready`** on stdout within `ready_s` (10 s). Start-up is untimed (reported).
2. The runner writes the inputs to a staging directory the prover cannot see, **starts the
   clock**, renames them into `/work` (constant time, whatever their size; RB-m11) and writes the
   line **`go`** on the prover's stdin.
3. The prover writes `/work/proof.bin` and prints the line **`done`** (or exits). At `done`, or at
   the prover's exit, the runner kills **every process of the sandbox at once and stops the clock
   when all of them are dead** (V4-A11 §5.1). Only then is `proof.bin` read. So work done after
   `done` (a thread, a forked child) is either on the clock or never happens: no byte written after
   the clock stopped exists. A prover that closes stdout without `done` is timed until its last
   process exits. The cap is `step_s` (60 s) from the inputs to the death of the last process.

`/work` is on a tmpfs where the machine has one: what the prover writes there counts against its
memory cgroup. When the prover is dead, `/work` may hold at most `work_cap` (4 GiB, a sparse file at
its size) in at most 65,536 entries. **Any failure the runner meets while the prover's sandbox
exists, or because of what a prover left behind, is the entry's failure** (R-M1): an input's name
taken, the directory made unreadable, the filesystem filled so that the runner's own writes fail,
files the runner cannot remove, the filesystem left fuller after cleanup.

**Between steps** the runner checks outputs (in batches of `check_every` = 8, each `V_i` the best of
two measurements, pinned to one core) and takes calibration samples, **never while an entry
process is alive**. The whole stream, every request, check, canary, calibration sample and re-run,
runs within `stream_s` (1,920 s, wall time). A stream that reaches it is scored over its completed
steps and flagged `truncated`; such a run is never ranked.

**Re-timing** (§5.3). After the stream the runner fits `P ≈ a·n + b` (trimmed least squares) and
runs once more, on the same inputs, every step with `P_i > 1.3 × (a·n_i + b)`, largest ratio first,
at most 10% of the steps. The faster run is kept and scored (its time, its `V` and its `|π|`); the
first output stays the child of the next step. The re-run's output must be accepted too.

**The score** (§4; lower is better, seconds per `2^18`-compression step):

```
S  = P̄ + V̄
P̄  = (2^18 / c_P) · ( Σ_i n_i · (P_i/n_i)^3 / Σ_i n_i )^(1/3)
V̄  = κ · (1/M) · Σ_i max(x_i, x_i^3),   x_i = V_i / v_ref + |π_i| / 2 MiB,   κ = 0.2667 s
```

`P_i` the step's time, `n_i` its new compressions (step 1: `nA + nB`), `c_P` the job's prover-shaped
calibration ratio (`harness/tools/calib.c`), `V_i` one `acc` check of the step's file (parse
included), `v_ref = T_triv / 10` (`T_triv` the organiser's chain checker on `2^24` compressions,
about 1.78 s on a runner, so `v_ref` ≈ 178 ms), `|π_i|` the bytes of `π` alone. **There is no
proof cap**: `|π|` is priced (100 KB of `π` costs about as much as 10 ms of verifier, estimate), and
`acc` only requires its length to fit a 64-bit word. Compact accumulation (folding with a running
state inside `π`) is a wanted design: `s_ref` keeps winning proofs within a few MB. The per-step
records (`WORK/stream.jsonl`, and `stream.steps` in the result) give every term, the fit, the
marginal values and the share of each step.

## 4. The oracle

Every oracle query a prover needs, Merkle hashes included, goes to the service (V4-14):
`QUERY` batches for answers while proving, one `SIGN` per output proof with the verifier's query
sequence (the service re-computes those answers and signs their trace digest). See
`service/PROTOCOL.md`. Use one connection per thread and batches of hundreds to thousands of
queries. The service's measured throughput on the job's machine is published in every result
(`calibration.service`).

## 5. What fails a run

A prover build or setup that fails or exceeds `build_s`, `setup_s` or `setup_cap`; a request with no
`ready` line within `ready_s`, a non-zero exit, a timeout of `step_s`, or a missing, non-regular or
over-cap (`file_cap`, 64 MiB) `proof.bin`; any output `acc` rejects (re-runs included); a statement
canary `acc` accepts (the outputs of steps 1, 2 and `M`, checked against their statement with one bit
flipped, against the next step's leaf statement and against their first child's statement); a check
above `verify_s` (10 s); a filesystem error the prover caused in `/work` (R-M1); the service dying
during the run; in the DoS column on the last output, a mutated or random input that `acc` (parse
plus the verifier) takes more than 10 × `v_ref` to decide, the column above its 180 s, or a crash of
the checker (an accepted DoS input is recorded, not failed). No time is a pass/fail gate on the
verifier any more: `V_i` is scored. Reaching `stream_s` is not a failure: the run is scored over its
completed steps, flagged `truncated` and not ranked. Every GitHub job of an evaluation ends within
30 minutes, the benchmark job within 50, and these caps are nested inside them (V4-A9). The first failure ends the evaluation
(`harness/run-benchmark.py`). The reason in the result names the cause: the prover's output (its
first 16 KiB and last 48 KiB are kept; the reason quotes the tail), the service's refusals of this
run (`rf-oracle: refused (status S): MESSAGE`, e.g. a query above 2^20 bytes; Q13), and a kill by the
memory cgroup (`killed: out of memory (cap …, peak …)`; Q14).

## 6. The Lean side's caps (the certificate job)

Each within a GitHub job of 30 minutes on a 4-vCPU runner (V4-A9, `[certificate]` of the season
file): the entry's `lake build` of the challenge and `Solution`'s import closure 600 s; the kernel's
check of the exported proofs 600 s (a breach leaves the certificate unchecked: PROVISIONAL); the
gate 120 s; the badge build 180 s. The badge build compiles the object code of every module of
`Solution`'s import closure that the organiser has not precompiled. Precompiled, once per core
commit: the import closures of `RecursionFast`, `CompPoly.Fields.Binary.BF64.Ext3`, `.Bytes` and
`Mathlib.Tactic` (`harness/org-setup.sh` step 4). The entry's own modules and any other module it
imports are compiled inside the 180 s, at about 4.8 objects per second on 4 cores (measured on the
development VM): about 860 such modules fit; `import Mathlib` (about 5,700 more) does not.

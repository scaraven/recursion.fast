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
  within `build_s` (5 min in season 1):

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
| `/dev`, `/proc` | minimal devices (`null`, `zero`, `urandom`, …); the prover's own processes |
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
characters plus an optional newline; `vk.hex` is the service's public key.

### `prover setup /setup` (optional, untimed)

Runs once per evaluation, before any instance or service exists, with `/setup` writable and no
socket. It may write tables, keys or code there (up to `setup_s`, 5 min in season 1). A prover
with nothing to set up exits 0.

### `prover tree /work` (the T run, timed)

Inputs: `leaves.json` = `{"n": N, "starts": ["HEX", …]}` with `2^r` starts (the runner's secret
chain starts, fresh per evaluation), `vk.hex`, and the service. Output:

- `root.bin`: a signed proof of the tree root `treeRoot` (adjacent leaf statements
  `leafStmt (chainEnd s_i n) n` joined by `nodeStmt`, level by level).

Only `root.bin` is required and read (V4-A9): other files the prover writes, such as inner proofs,
are ignored. The clock runs from the `exec` of the prover to its exit (`tree_s` cap, 10 min in
season 1). `root.bin` must be a regular file; the runner checks it with `acc` under this run's
`vk`, within `T_V`, and checks that it is rejected for the root's statement with one bit flipped
(the statement canary).

### `prover leaf /work` and `prover node /work` (the stream, timed per request)

A fresh process for every request (cost model §3.3, CM-6). The handshake:

1. The runner starts the process (with `vk.hex` already in `/work`). The prover loads its setup and
   prints the line **`ready`** on stdout. Start-up is untimed.
2. The runner writes the inputs to a staging directory the prover cannot see, **starts the
   clock**, renames them into `/work` (constant time, whatever their size; RB-m11) and writes the
   line **`go`** on the prover's stdin.
3. The prover writes `/work/proof.bin` and either prints the line **`done`** or exits. The clock
   stops at the first of the two (`step_s` cap, 60 s in season 1; the wait for `ready` has the
   same cap). The runner then kills the request's sandbox and reads `proof.bin`.

Inputs: `leaf`: `leaf.json` = `{"n": N, "start": "HEX"}`. `node`: `child1.stmt`, `child1.bin`
(the running statement and its signed proof) and `child2.stmt`, `child2.bin` (the new leaf's
statement and the signed proof the previous `leaf` request produced). The output of `node` is a
signed proof of `nodeStmt child1 child2`.

One request at a time; a start is released only after the previous output is written; nothing
survives a request except the proofs the runner copies. The whole stream, every request and every
check from the first request on, runs within `stream_s`, wall time: 960 s in season 1 (`M = 256`),
of which 60 s allow for the runner's own overhead inside it (sandbox starts, badge starts; about
30 s measured). A link that would end after it fails the run. So the entry has about 900 s for its
513 requests, each from its process's start (its start-up to `ready` included) to its output, and
for the checks of its outputs: with every check at `T_V` (about 178 ms on a runner), **about 3.1 s
per link**, a leaf and a merge with their start-ups. Every output is checked with `acc` within
`T_V`; the first two leaf and two node outputs are also checked against their statement with one
bit flipped and against their sibling's statement, and must be rejected.

## 4. The oracle

Every oracle query a prover needs, Merkle hashes included, goes to the service (V4-14):
`QUERY` batches for answers while proving, one `SIGN` per output proof with the verifier's query
sequence (the service re-computes those answers and signs their trace digest). See
`service/PROTOCOL.md`. Use one connection per thread and batches of hundreds to thousands of
queries. The service's measured throughput on the job's machine is published in every result
(`calibration.service`).

## 5. What fails a run

A non-zero exit of `tree`; a missing, non-regular or over-cap output; any output `acc` rejects; a
statement canary `acc` accepts; a check above `T_V` (season shape; a check above the cap is measured
again, best of `checker_runs`, like the cap itself, RB-M1) or `verify_s` (10 s); a timeout of any
cap (`build_s`, `setup_s`, `tree_s`, `step_s`, `stream_s`; `harness/season.toml`); the service dying
during the run; a stream link that is not accepted; in the DoS column, a mutated or random input
that `acc` takes more than 10 × `T_V` to decide, the column above its 180 s, or a crash of the
checker (an accepted DoS input is recorded, not failed). Every GitHub job of an evaluation ends
within 30 minutes, and these caps are nested inside it (V4-A9). The first failure ends the
evaluation (`harness/run-benchmark.py`). The reason in the result names the cause: the prover's
output (its first 16 KiB and last 48 KiB are kept; the reason quotes the tail), the service's
refusals of this run (`rf-oracle: refused (status S): MESSAGE`, e.g. a query above 2^20 bytes; Q13),
and a kill by the memory cgroup (`killed: out of memory (cap …, peak …)`; Q14).

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

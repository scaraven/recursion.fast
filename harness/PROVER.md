# The prover interface (normative)

The efficient prover of an entry is an **x86-64 Linux program submitted as GNU assembly**
(BRIEF P4, V4-9). The runner builds it, runs it in a sandbox, and measures it. Everything it
produces is checked by the compiled `acc` (`harness/FORMAT.md`); nothing it says is trusted.

## 1. Build

- Sources: the entry's `prover/*.s` (AT&T or `.intel_syntax`), nothing else. Sources in any other
  language may sit beside them for readers; they are not built.
- Command, inside the build sandbox (V4-A6), in a directory holding only copies of the `.s` files:

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
socket. It may write tables, keys or code there (up to `setup_s`, 1 h). A prover with nothing to
set up exits 0.

### `prover tree /work` (the T run, timed)

Inputs: `leaves.json` = `{"n": N, "starts": ["HEX", …]}` with `2^r` starts (the runner's secret
chain starts, fresh per evaluation), `vk.hex`, and the service. Outputs:

- `proofs/L<i>.bin` for every leaf `i = 0 … 2^r − 1`: a signed proof of
  `leafStmt (chainEnd s_i n) n`;
- `proofs/N<l>_<j>.bin` for every inner node, level `l = 1 … r − 1` (level 1 joins leaves),
  `j = 0 … 2^(r−l) − 1`: a signed proof of `treeLevel^l(leaves)[j]` (node `j` of level `l` joins
  nodes `2j` and `2j + 1` of level `l − 1`);
- `root.bin`: a signed proof of the tree root `treeRoot`.

The clock runs from the `exec` of the prover to its exit (`tree_s` cap). Every file must exist and
be a regular file; the runner checks `root.bin`, 16 random other proofs and the canaries of the
first 8 leaf and node proofs, all with `acc` under this run's `vk`.

### `prover leaf /work` and `prover node /work` (the stream, timed per request)

A fresh process for every request (cost model §3.3, CM-6). The handshake:

1. The runner starts the process (with `vk.hex` already in `/work`). The prover loads its setup and
   prints the line **`ready`** on stdout. Start-up is untimed.
2. The runner **starts the clock**, writes the inputs into `/work` (each by an atomic rename), and
   writes the line **`go`** on the prover's stdin.
3. The prover writes `/work/proof.bin` and either prints the line **`done`** or exits. The clock
   stops at the first of the two (`step_s` cap). The runner then kills the request's sandbox and
   reads `proof.bin`.

Inputs: `leaf`: `leaf.json` = `{"n": N, "start": "HEX"}`. `node`: `child1.stmt`, `child1.bin`
(the running statement and its signed proof) and `child2.stmt`, `child2.bin` (the new leaf's
statement and the signed proof the previous `leaf` request produced). The output of `node` is a
signed proof of `nodeStmt child1 child2`.

One request at a time; a start is released only after the previous output is written; nothing
survives a request except the proofs the runner copies.

## 4. The oracle

Every oracle query a prover needs, Merkle hashes included, goes to the service (V4-14):
`QUERY` batches for answers while proving, one `SIGN` per output proof with the verifier's query
sequence (the service re-computes those answers and signs their trace digest). See
`service/PROTOCOL.md`. Use one connection per thread and batches of hundreds to thousands of
queries. The service's measured throughput on the job's machine is published in every result
(`calibration.service`).

## 5. What fails a run

A non-zero exit of `tree`; a missing, non-regular or over-cap output; any output `acc` rejects; a
canary `acc` accepts; a check above `T_V` (season shape) or `verify_s`; a timeout; the service
dying during the run; a stream link that is not accepted. The first failure ends the evaluation
(`harness/run-benchmark.py`).

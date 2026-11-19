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
| `/prover/prover` | the binary (read-only; in a request, the runner's copy on its tmpfs, one per pass) |
| `/setup` | the setup directory (read-only after `setup`; in a request, the runner's copy on its tmpfs: directories, regular files, every byte written, and links; FIFOs, sockets and devices are left out; a fresh copy for the service run and for each timed pass, shared by the steps of that pass only) |
| `/work` | the request's own private tmpfs (a superblock of its own, fresh for every request), read-write, the working directory |
| `/run/rf/oracle.sock` | the oracle service's socket (`RF_ORACLE`), **only from `go` on**: connect after `go` |
| `/tmp` | an empty tmpfs (counted in the memory cap) |
| `/dev`, `/proc` | minimal devices (`null`, `zero`, `urandom`, …); `/proc` lists only the prover's own processes and holds no machine-wide counter: every top-level entry but the pid directories, `self` and `thread-self` reads empty (`stat`, `vmstat`, `meminfo`, `loadavg`, `interrupts`, `pressure`, `cpuinfo`, …; use `cpuid`); the links `mounts` and `net` lead into `self` |
| `/sys/devices/system/cpu` | the CPU topology, read-only: a static copy of its description as read when the runner starts, written afresh for every sandbox (`cpuidle`, `cpufreq`, `power` and the tree's links are absent) |

Nothing else exists: no `/usr`, no shell, no network, no other process. Nothing a request sees is
on the host's disks or sysfs: every bound file and directory is on the runner's own tmpfs or fresh
for the request, so a lookup of an absent name leaves nothing a later request can time and no
page-cache folio of a setup file changes shape (on a disk filesystem both persist: AGENTS.md §12).
A read-only tmpfs file still keeps state set through it (its shared memory policy, by `mbind` on a
`MAP_SHARED` mapping), so no file is shared across a pass, a badge run or a sandbox: the copy of
`/setup` and `/prover` is the pass's, the `/proc` mask files and the CPU tree are the sandbox's.
The one directory bound into a request under a name the runner chose, its socket directory at
`/run/rf` (`/proc/self/mountinfo` shows its path), is `svc/requests/<16 random hex characters>`
on that tmpfs, fresh for every request, so no name in the
sandbox tells a request its pass or its step (counters that advance with every sandbox, such as
mount ids, and the clock still roughly do: AGENTS.md §12). The environment is
`RF_ORACLE=/run/rf/oracle.sock`, `RF_SETUP=/setup`, `HOME=/work`, `TMPDIR=/tmp`, `PATH=/prover`.
Resources: every CPU of the machine (shared with the service, which computes the oracle on the same
CPUs), memory capped by a cgroup (`memory.prover` of the season, 8 GiB in season 1; the service
has its own 2 GiB), `oom_score_adj = 1000`. The setup's copy is the runner's (written by it, charged
to it, resident while its pass runs): up to `setup_cap` (4 GiB) of read-only setup is resident beyond the
prover's 8 GiB, and mapping it costs no page-in. A seccomp filter fails (EPERM) `ptrace`,
`process_vm_*`, `bpf`, `perf_event_open`, `userfaultfd`, `io_uring_*`, key management, mounts,
namespaces and module loading, and `socket` and `socketpair` for every domain but `AF_UNIX` (the
oracle's socket is the only one a prover needs). It also refuses what would read a machine-wide
counter that one request could set for a later one: `statfs`, `fstatfs` (so `statvfs`) and `ustat`
fail with ENOSYS (free space; glibc's `pathconf` then answers its defaults); `setsid` fails (the
prover is a session leader already; a new session would move the machine-wide autogroup counter);
`madvise` with `MADV_COLD` or `MADV_PAGEOUT`, and `process_madvise`, fail (they could push the
runner's tmpfs pages out to swap); `mbind`, `migrate_pages`, `move_pages` and
`set_mempolicy_home_node` fail with ENOSYS (a policy set on a shared file's pages stays in the file;
`set_mempolicy` and `get_mempolicy`, the thread's own policy, work, and so does libnuma's fallback
to "no NUMA"); no pidfd can be made, since a pidfd's inode number counts every
process the machine started (`pidfd_open`, `clone` with `CLONE_PIDFD`, `getsockopt` `SO_PEERPIDFD`
and `setsockopt` `SO_PASSPIDFD` fail with EPERM; `clone3` fails with ENOSYS, and libc falls back to
`clone`, so `fork`, `posix_spawn` and threads work); `getsockopt` `SO_COOKIE` fails (socket cookies
come from a machine-wide counter). Before every request (and every badge run) the runner moves every CPU's inode counters (behind the inode numbers of pipes, sockets, other pseudo
files and memfds) to the end of their batch and then a uniform random offset into a fresh one
(`harness/tools/scrub.c`, one pinned thread per CPU, about 0.1 s, recorded as `scrub_s`), so a
pipe's or memfd's inode number says nothing of what an earlier request did on that CPU. When a
request ends, every process the prover started is killed. The same `/proc` and CPU-tree masks and the same filter apply to `prover setup`
and to every badge run of the benchmark job (which runs the entry's compiled `V`).

## 3. Invocations

All paths below are relative to `/work` unless absolute. Statements and keys are 64 lowercase hex
characters plus an optional newline; `vk.hex` is the service's public key. A leaf is two files:
`leaf.json`, `{"n": N}`, and `leaf.bin`, its data: exactly `32 · N` bytes, the blocks
`x_0 ‖ … ‖ x_(N−1)` of 32 bytes each. The public hashes are Ethereum's Keccak-256 (rate 136 bytes,
padding `0x01 … 0x80`, not SHA3-256) of tagged inputs (`RecursionFast/Contract/Relation.lean`;
`u64` little-endian):

```
leafItem x      = Keccak-256(0x48 ‖ x)                 33 bytes, one Keccak-f[1600] permutation
dataNode l r    = Keccak-256(0x44 ‖ l ‖ r)             65 bytes, one permutation
dataLevel ds    = adjacent digests paired by dataNode; an odd last digest is carried up unhashed
dataRoot xs     = dataLevel applied |xs| times to map leafItem xs, then the first digest
                  (the zero digest for no block, leafItem x for one block)
leafStmt h n    = Keccak-256(0x4C ‖ h ‖ u64 n)         41 bytes
nodeStmt c1 c2  = Keccak-256(0x4E ‖ c1 ‖ c2)           65 bytes
```

So a leaf of `n` blocks is a Merkle tree of `n` block hashes and `n − 1` nodes (`2n − 1`
permutations); its shape is fixed by `n`, and the carry-up matters only when a level has an odd
number of digests. Known answers: `tests/vectors/data_root.json`. The verifier sees only the
statement, so the data has to be committed to and opened in the proof (a witness-sending proof of a
leaf is `u64 0 ‖ u64 n ‖ x_0 ‖ … ‖ x_(n−1)`, `16 + 32 n` bytes, above `pi_cap` at the season's `n`).

### `prover setup /setup` (optional, untimed)

Runs once per evaluation, before any instance or service exists, with `/setup` writable and no
socket. It may write tables, keys or code there, within `setup_s` (4 min in season 1) and
`setup_cap` (the directory holds at most 4 GiB in at most 2^20 entries afterwards, sparse files at
their size, and must be hashable within that and 60 s; otherwise the setup fails).
A prover with nothing to set up exits 0.

### The stream: `prover first /work`, then `prover step /work` (timed per request)

**One benchmark, an IVC stream** (AGENTS.md §6; in the track `final` only the last output needs to
be a proof). An evaluation is one stream of `M` steps (`M = 16` in
season 1, 4 in the smoke) under one service lifetime, run once against the service and then three
more times, timed, against its replay (below). Every step is a fresh process in a fresh sandbox
(fresh `/work`, fresh `/tmp`, read-only `/setup`); nothing survives a request except the proof the
runner copies, so **state between steps travels only inside `π`**.

Every step proves one fresh leaf of exactly `n` blocks (`n = 2^18`, 8 MiB of data, in season 1, at
most the contract's `leafCap = 2^20`; 6 in the smoke), about `2n` permutations per step:

```
L_i = leafStmt (dataRoot xs_i) n          xs_i the step's data (leaf.bin)
c_1 = L_1,        c_i = nodeStmt c_{i-1} L_i                          (i = 2 … M)
```

- **Step 1** (`prover first /work`): inputs `leaf.json` (`n`) and `leaf.bin` (the data `xs_1`).
  Output `proof.bin`: a signed proof of `c_1 = L_1`.
- **Step i ≥ 2** (`prover step /work`): inputs `prev.stmt` (`c_{i-1}`), `prev.bin` (the previous
  step's output, exactly as the runner received it in the service run), `leaf.json` and `leaf.bin`
  (`xs_i`). Output `proof.bin`: a signed proof of `c_i = nodeStmt c_{i-1} L_i`.

A step may make any number of `SIGN` requests within the lifetime's budget of `2^16` signatures (a
node needs signed proofs of its children as its witness). The runner computes every statement
itself and checks outputs against them (below).

**What is fixed, what is drawn, and what is told** (AGENTS.md §6). The shape is **fixed and
published**: `M` and the one leaf size `n` (`[stream]` of `harness/season.toml`;
`harness/smoke.toml` has its own), the same for every evaluation and every entry. The **data** is
the runner's: per step a fresh secret 32-byte seed `s_i` from the OS CSPRNG, expanded by the runner
to `xs_i = SHAKE-256("recursion.fast/leaf-data/v1" ‖ s_i)` truncated to `32 · n` bytes. A prover
never sees a seed, only the data, and a step sees its data only when its inputs arrive (`leaf.bin`,
staged where the prover cannot see it and renamed into `/work` at `go`; the runner keeps its own
copy in a directory no sandbox can see, and computes every statement from it before the first
request). The result publishes the seeds and the expansion (`stream.leaf_data`) after the run, so
anyone can regenerate the data and recompute every statement.

**The two runs** (AGENTS.md §6).

1. **The service run** (untimed): the stream as above against the service, under `step_s` per
   request and the benchmark's `stream_s`. No key is anywhere in the prover's reach. Its times are
   recorded (`P_service_s`), never scored. Every output is kept and checked (below) before any
   secret is revealed.
2. **The timed passes** (`timed_runs = 3`): the service run's requests are gone, each with its
   `/work` tmpfs; before each pass the runner puts the service in **replay mode**: it reveals its
   PRF key `k`, resets its one-time-key counter to 0, and from then on answers `SIGN` at index `j`
   only if the trace digest equals the one it signed at index `j` in the service run (it returns
   that same signature), else it refuses with status 4 `MISMATCH` (`service/PROTOCOL.md`); `QUERY`
   is served unchanged. Each pass runs steps `1 … M` again, each a fresh sandbox, with the same
   leaf (the same `leaf.json` and `leaf.bin` bytes), the runner's `prev.stmt`, the **service run's**
   output of step `i − 1` as `prev.bin`, and one more input, **`oracle.key`**: `k` as 64 lowercase
   hex characters and a newline, staged with the other inputs, so it appears in `/work` only when
   the clock runs (every `k`-dependent computation is timed). A prover may use `k` to compute
   oracle answers itself instead of asking the service, or ignore it; it may branch on whether
   `/work/oracle.key` exists.

**Determinism is required.** Each timed output must be **byte-identical** to the service run's
output of that step; otherwise the entry is REJECTed, the reason naming the pass, the step and the
first differing byte offset. A prover's output must be a function of its inputs, its setup and the
oracle answers: no clock, no `/dev/urandom`, no thread-order dependence in what it writes, a
deterministic grinding order (for example the least nonce in a fixed search order), and its `SIGN`
requests in an order its inputs fix (the service assigns one-time indices in the order `SIGN`
requests arrive, and a replay refuses any other digest at an index). **A timed pass must make
exactly the service run's `SIGN` requests**: any replay `MISMATCH` (in any pass), and any total
other than `timed_runs` times the service run's signatures, is the entry's REJECT (a refusal at an
index would otherwise be a bit carried from the service run into a timed pass). A pass that does
not finish is the entry's REJECT too. Three pitfalls: a
`SIGN` that fails or is retried still consumes its index, so never retry a `SIGN` unless the retry
is fixed by the inputs; no output may depend on measured memory, load or time (`sysinfo(2)` still
reports the machine's), not even through a choice of chunk size or algorithm; and a local
PRF computed from `oracle.key` must match the service's `QUERY` byte for byte, multi-block queries
included (test it on 0-, 103-, 104- and 239-byte queries).

**The handshake** (per request):

1. The runner starts the process (with `vk.hex` already in `/work`). The prover loads its setup and
   prints the line **`ready`** on stdout within `ready_s` (10 s). Start-up is untimed (reported),
   and the service is unreachable during it: `/run/rf/oracle.sock` does not exist yet.
2. The runner writes the inputs where the prover cannot see them (unnamed files on the request's
   `/work` tmpfs), **starts the clock**, links the service's socket into `/run/rf`, renames the
   inputs into `/work` (constant time, whatever their size) and writes the line **`go`** on the
   prover's stdin. A prover connects to the service only after `go`.
3. The prover writes `/work/proof.bin` and prints the line **`done`** (or exits). At `done`, or at
   the prover's exit, the runner kills **every process of the sandbox at once and stops the clock
   when all of them are dead**. Only then is `proof.bin` read. So work done after
   `done` (a thread, a forked child) is either on the clock or never happens: no byte written after
   the clock stopped exists. A prover that closes stdout without `done` is timed until its last
   process exits. The cap is `step_s` (20 s) from the inputs to the death of the last process.

**Before every request** (untimed, with no entry process alive) the runner scrubs the per-CPU inode
counters (§2); `/setup` and the binary need no warming, their copies on the runner's tmpfs being
resident (before each timed pass the runner makes the pass's fresh copy, inside the stream's time,
`stream_s`: AGENTS.md §9). The inputs are staged as five unnamed inodes in every request (a placeholder for
each input the request does not get), so a prover counting `/work`'s inode numbers before `go`
learns nothing of whether it is in a timed pass.

`/work` is a private tmpfs of the request's own, gone with the request, so its inode numbers and
free space carry nothing from one request to the next. What the prover writes there counts
against its memory cgroup; the inputs are written by the runner, so their pages are charged to the
runner (a copy the prover makes counts). When the prover is dead, `/work` may hold at most
`work_cap` (4 GiB, a sparse file at its size) in at most 65,536 entries. **Any failure the runner
meets while the prover's sandbox exists, or because of what a prover left behind, is the entry's
failure**: an input's name taken, the directory made unreadable, the filesystem filled so that the
runner's own writes fail, an output that cannot be read.

**The checks of the service run** (AGENTS.md §6, §7), never while an entry process is alive:

- every output's size is at most `pi_cap` (1 MiB): its `|π|` if it parses as a signed proof
  (`harness/FORMAT.md`) that `acc` accepts, else its file size;
- **every checked proof is judged in three separate badge runs of its own**, each a fresh process
  that first checks an organiser warm-up input (never an output) and then that one proof, and
  nothing else: no proof is checked twice in one process, and no judged run checks two outputs of
  the stream (output `i + 1` contains `π_i`: a memo of the children's acceptance gains nothing); `V_i`
  is the median of the proof's three times (each one check on one pinned core, the file's read and
  parse included), and all three runs must accept (accepted in one run and rejected in another is
  rejected);
- the intermediate outputs are checked with `acc` under the run's `vk` against the runner's
  statements `c_i`, between steps, every `check_every` (8) steps;
- the **final** output (step `M`) is then judged on its own, in three runs of its own: it must be
  accepted, with `|π_M| ≤ final_pi_cap` (512 KiB) and `V_M ≤ v_cap` (64 ms, the median of its three
  times), and its statement canaries rejected (`c_M` with its first bit flipped, and its first
  child `c_{M-1}`; each canary checked once): the track **`final`**. A crash or timeout of these
  checks is the entry's REJECT;
- the track **`every`** additionally needs every intermediate output accepted with `V_i ≤ v_cap`
  (the median of its three times) and the statement canaries of outputs 1 and 2 rejected
  (output 1, a leaf, has no first child: only its flipped statement). An entry that meets `final` but not `every` is
  scored in `final` only, the result saying why (`score.tracks_reason`); intermediate outputs need
  not be proofs at all. A crash or timeout of an intermediate check, or of the canaries of outputs
  1 and 2, costs only the track `every` (a judged run of an intermediate output is bounded by
  `60 s + 4 · v_cap`, the canary run of `c` canaries by `60 s + 2 (c + 1) · v_cap`); once the track
  is lost, those canaries are skipped.

The final output's checks have no time cap of their own. Every badge run ends within one bound
shared by all of them, 30 s past `stream_s`, and none starts once `stream_s` is reached. Calibration samples (AGENTS.md §6) are
taken before the service run's step 1 (and every `every` steps), before each timed pass, and a
closing one if 30 s of `stream_s` remain. The whole benchmark, the service run, every request, check,
canary, calibration sample and the three timed passes, runs within `stream_s` (2,000 s, wall time;
the season file's value binds, and a later season may set another); reaching it is the entry's
REJECT.

**The score** (AGENTS.md §7; one score per track; lower is better, seconds):

```
T_t      = Σ_i P_{i,t}                          the total of timed pass t (t = 1, 2, 3)
P_total  = T_{t*}                               t* the pass whose total is the median
                                                (ties: the lowest such index)
S        = P_total · 2^(|π_M| / 512 KiB)        the track `final`
S_every  = P_total · 2^(max_i |π_i| / 512 KiB)  the track `every`
```

`P_{i,t}` step `i`'s time in timed pass `t`, `|π_M|` the bytes of the final output's `π` alone,
`max_i |π_i|` the largest output's. `V` is not scored (it is capped), nor the service run's times;
in `final` the size of an intermediate output is capped, not priced. Only the pass totals count:
moving work between steps changes nothing (a step's data cannot be carried forward, so its hashing
stays in its step). The per-step records (`WORK/stream.jsonl`, and `stream.steps` in the result)
give the service run's time, the three timed times in pass order (`P_timed_s`), the median pass's
time (`P_s`), `|π|`, `V` (its three times, `V_runs_ns`, and their median) and each step's share of
`P_total`.

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
`pi_cap`; a final output that `acc` rejects (in any of its three judged runs), above
`final_pi_cap`, with `V_M` above `v_cap` (the median of its three judged runs), or whose statement
canary `acc` accepts; a timed output that is not
byte-identical to the service run's output of its step; a replay `MISMATCH`, or a timed pass that
does not make exactly the service run's signatures; a crash or timeout of the final output's checks; a
filesystem error the prover caused in `/work`; the service dying during the run; a timed pass
that does not finish; the benchmark reaching `stream_s`. `stream_s` (2,000 s) covers the 64
requests at `ready_s + step_s` each (1,920 s) and the checks, samples and scrubs, so it
binds only when an entry uses nearly every cap at once (start-ups near 10 s, steps near 20 s, a
setup directory near 4 GiB); such an entry can reach it within every per-request cap (AGENTS.md
§9). An intermediate output that `acc` rejects (in any of its three judged
runs), or above `v_cap`, a canary of output 1 or 2 that `acc` accepts, or a crash or timeout of
their checks, does not fail the run: it leaves the entry out of the track `every`. Every job of an
evaluation ends within 30 minutes, the certificate job within 50 and the benchmark job within 70,
and these caps are nested inside them. The first failure ends the
evaluation (`harness/run-benchmark.py`). The result names the stage (`reject_stage`,
`rfh.bench.REJECT_STAGES`): `prover` (the build, the setup, the setup's hash, anything before the
stream), `request` (a service-run request failed, or its output broke `pi_cap` as it arrived, or
`final_pi_cap`), `check` (a badge run failed, the final output rejected or above `v_cap`, a
canary accepted, an output above `pi_cap` only because a rejection sized it by its file),
`timed-pass` (a byte or replay mismatch, a failed timed request), `stream-cap` (`stream_s`
reached), `certificate` for a rejected certificate, first. The reason names the cause: the prover's
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

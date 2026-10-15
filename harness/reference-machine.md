# The reference machine and the measurement policy (DESIGN §6.4, O-6)

Scores are wall times measured on **one organiser-run machine** (DESIGN §6.1). This file is the
organiser's checklist: every field marked _(season)_ is filled in once per season and whenever the
machine changes, and the scoreboard shows the hardware id next to every number. The runner is
`harness/run-benchmark.py` (harness/README.md); the numbers below come from its timer.

## 1. Per-season record (fill in)

| Field | Value _(season)_ | Notes |
|---|---|---|
| Season, hardware id | | printed next to every score |
| CPU SKU, cores, SMT | | DESIGN §6.4: x86-64, ≥ 32 cores. **Requirement: carry-less multiply present** (`pclmulqdq` on x86-64, ideally also `vpclmulqdq`/`gfni`; Zbc on RISC-V): the field is GF(2^64). Check: `grep -c pclmulqdq /proc/cpuinfo` > 0 |
| Frequency policy | | governor `performance`; turbo on or off, stated; no frequency capping |
| Memory | | ≥ 64 GB. **Requirement: per-step memory cgroups** (cgroup v2 with the memory controller delegated to the evaluating user, so that `systemd-run --user --scope -p MemoryMax=…` works); the runner refuses to run without it (S6b-m1). Check: `systemd-run --user --scope -q -p MemoryMax=64M true` |
| Storage | | local NVMe; the step directories and inputs on it (warm page cache allowed) |
| OS, kernel | | |
| glibc | | |
| Lean | | `lean-toolchain` (v4.34.1 at the time of writing) |
| gcc / clang | | the Lean toolchain's clang links the executables |
| Rust / cargo | | pinned per season for native provers |
| Python | | the runner (standard library only) |
| bubblewrap | | the sandbox (`scripts/bwrap-landrun.sh`) |
| Transparent huge pages, ASLR, swap | | stated (defaults are fine; swap off) |
| Isolation | | the machine is idle during an evaluation: no other job, no interactive user, no network; one evaluation at a time |

## 2. One-time setup per machine and toolchain

- `scripts/setup-clean.sh` (Clean at the pinned rev, `ext/Clean`), then `scripts/org-build.sh
  ORG` (organiser package with Clean and the bridge; ≈ 5 min cold) and
  `scripts/olean-manifest.py check --org ORG scripts/olean-manifest.sha256`.
- **Prebuild every Mathlib object file** (S6b-A18), so that a submission may import any Mathlib
  module and its badge executables still link in the read-only sandbox:
  `(cd ORG && lake build mathlib/Mathlib:static)`. Measured here: 3 min 35 s wall, 29 min CPU for
  the ≈ 5,000 objects not yet built by the organiser build (the organiser's `harness-linkcheck`
  had built ≈ 2,000); the result is a 298 MB `libmathlib_Mathlib.a` and 974 MB of objects in the
  shared packages directory. From scratch, expect ≈ 5 min wall on 32 cores. These are build
  outputs, outside the olean manifest.

## 3. What is timed (fixed by the design; restated)

- **Timed region.** One sandboxed process: from the start of `bwrap-landrun.sh --minimal-root` to
  its exit, read with `date +%s%N` by an organiser shell running in the step's cgroup, outside the
  sandbox (fix pass, S6b-m1/m3; before, the spawn-to-exit time of the whole wrapper). The output
  file is closed when the process exits. The sandbox's set-up (mounts, namespaces: about 0.05 s
  here with the minimal root) is inside it, the cgroup's (`systemd-run`, about 0.04 s) is not. Building (`lake build`, the native prover's build), indexing and the
  organiser's own bookkeeping (copying inputs, computing statements) are outside it.
- **What a score adds up.** A step's score is the prover's wall time plus the verifier's wall time
  on the step's output proof (two processes). `S_rec` is the median over the node steps with two
  node children (levels ≥ 2), `S_wrap` over the level-1 steps, `S_leaf` over the leaf chains; each
  is the median of the per-run medians over 3 runs (DESIGN §6.2, §6.3).
- **Start-up is inside.** A Lean executable initialises every imported module (about 0.07 s for
  the contract's and the organiser's modules, §4) and the sandbox adds a few milliseconds; a
  native prover's start-up likewise. Every entry pays them.
- **Memory** (S6b-m1). Every step runs in its own cgroup with `MemoryMax` = 48 GB and
  `MemorySwapMax` = 0 and `OOMPolicy=continue` (`systemd-run --user --scope`): the cap covers the
  whole process tree, and a step in whose cgroup the kernel killed a process at the cap (an
  `oom_kill` in `memory.events`) rejects the evaluation ("killed at the memory cap"). The reported peak is the
  cgroup's `memory.peak` (the memory charged to the step, so shared pages already cached elsewhere
  are not counted). Without cgroups the runner rejects the run; it does not fall back to
  per-process accounting.
- **Parallelism.** All cores are available to every process; multi-threaded provers are expected.

## 4. Record rule and re-runs

- **Record rule** (`is_record` in `harness/run-benchmark.py`; `run-benchmark.py record NEW
  STANDING`): a score is a new record iff it is at most `0.97 ×` the standing record (it beats it
  by at least 3 %, above the measured noise).
- **Re-runs.** Every standing record is re-measured each season and whenever the machine changes;
  a re-run re-ranks, it never invalidates a record. The hardware id is published with each number.
- **Instances.** Fresh random chain starts per evaluation (`run-benchmark.py secrets`); the three
  runs of one evaluation use the same instances.
- **Prover nondeterminism** is allowed; every instance must succeed in every run.

## 5. First noise measurement (Stage 6b, this development machine, 2026-10-15): the placeholder for O-6

**Not a reference machine.** A QEMU virtual machine (32 vCPUs "QEMU Virtual CPU version 2.5+",
62 GB, Ubuntu 26.04.1, kernel 7.0.0-38, glibc 2.43, gcc 15.2.0, rustc 1.99.0, Lean v4.34.1,
Python 3.14.4, bubblewrap 0.11.1, virtual disk, THP `madvise`, no cpufreq control), **without
`pclmulqdq`/`gfni`** in its CPU flags, shared with other agents' builds during the measurement
(load average about 4 on 32 vCPUs). The numbers bound the noise from above; they do not
calibrate a reference machine.

Measured with `harness/measure-noise.py` (10 repetitions, fresh step directory each, the runner's
sandbox and timer) on the smoke protocol `cmpToy` (O-10): `verify` is the compiled `NARG` on an
honest 152-byte tape; the prover is `harness/smoke/toy_prover.py` (Python; about 15 BLAKE2s calls).

| process (10 repetitions) | median | min | max | (max − min) / median |
|---|---|---|---|---|
| `verify` (compiled `NARG`, honest tape), sandboxed | 0.1084 s | 0.0986 s | 0.1234 s | 23 % |
| `verify`, no sandbox | 0.0775 s | 0.0740 s | 0.0841 s | 13 % |
| Python prover (`toy_prover.py leaf`), sandboxed | 0.0599 s | 0.0549 s | 0.0685 s | 23 % |
| Python prover, no sandbox | 0.0372 s | 0.0315 s | 0.0409 s | 25 % |

Medians of medians (the score's own statistic), three evaluations of the smoke protocol (each 64
leaves + 16 + 16, 32 wrap and 31 node steps, 3 runs; `logs/S6b/`):

| evaluation | `S_leaf` | `S_wrap` | `S_rec` |
|---|---|---|---|
| first smoke run | 0.1695 s | 0.1638 s | 0.1709 s |
| CI run 1 | 0.1674 s | 0.1682 s | 0.1679 s |
| CI run 3 | 0.1719 s | 0.1735 s | 0.1710 s |
| spread (max − min) / min | 2.7 % | 5.9 % | 1.8 % |

Logs: `logs/S6b/noise-{verify,prover}-{sandbox,none}.json`, `logs/S6b/ci/bench-smoke.json`.

**Reading.** Single processes of 0.04–0.11 s vary by 13–25 % here, and the sandbox adds about
0.03 s per process (bubblewrap's namespaces and mounts). Over a whole evaluation the medians of
medians still move by up to 6 % between evaluations (`S_wrap`), which is **above** the 3 % record
margin. On this shared VM, with steps this short, the margin would not separate a record from
noise. Two effects shrink on a reference machine: isolation (no other jobs) and step length (a
real step is seconds to minutes, so start-up and scheduling jitter are a smaller fraction). O-6
must re-measure on the reference SKU with realistic steps before the 3 % margin is relied on.

After the fix pass (per-step cgroup + minimal sandbox root; `logs/S6b/noise-*-fixpass.json`, 10
repetitions, the executables of CI run 7):

| process (10 repetitions) | median | min | max | (max − min) / median |
|---|---|---|---|---|
| `verify`, sandboxed in its cgroup | 0.1563 s | 0.1440 s | 0.1844 s | 26 % |
| `verify`, no sandbox | 0.0840 s | 0.0777 s | 0.0875 s | 12 % |
| Python prover, sandboxed in its cgroup | 0.0948 s | 0.0904 s | 0.1042 s | 15 % |

The sandbox and the cgroup add about 0.07 s per process (was 0.03 s): `systemd-run --scope`
registers a scope with the user manager and bubblewrap mounts the minimal root. The reported peak
is now the cgroup's `memory.peak` (17 MB for `verify`, against a 76 MB `ru_maxrss`): the
executable's file pages already in the page cache are charged elsewhere. For seconds-long steps
the 0.07 s is a constant every entry pays.

## 6. Open (O-6, the user's decision)

- The reference SKU (with carry-less multiply) and the season's toolchain pins.
- Repeat §4 on it, with steps of realistic length (seconds to minutes: the smoke test's steps
  are 0.06–0.1 s, dominated by process start-up), to confirm that 3 % is above the noise of a
  median of 31 steps × 3 runs.
- Whether to report the verifier's start-up separately (it is a fixed cost of every entry).

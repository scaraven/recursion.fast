# GB — golf of stage B (v4, SROM): the trusted runtime

Golf agent, 2026-10-23, worktree `recursion.fast-v4h`, branch `v4/harness`. Base: `e572344` (stage
B as reviewed). The orchestrator committed `ea2e8ab` (stage A fix pass) on the branch during this
pass; it touches no file I changed, and my edits are uncommitted on top of it, as the stage
protocol asks. The adversarial reviewer (`RB-harness-review.md`) read the same tree concurrently.

The user asked for golf of proof size and of execution time. Priority: execution time on the
score and check paths, then trusted lines, then Lean proofs. No wire format, file format, cap,
refusal, key handling, isolation or memoisation property was changed; §1.4 lists what was
checked.

**Measurement method.** This VM (32 vCPU QEMU, 2.1 GHz, AVX2) was shared with other agents (load
average 10–25 throughout), so single runs vary by ±20 %. Every before/after number below is
interleaved: the base build (`e572344`) and the golfed build alternate run by run, and each side
keeps its best. Logs are in `logs/golf-B/` (gitignored), named per row.

## Summary

| Component | Code lines before → after | What is faster (before → after, best of interleaved runs) |
|---|---:|---|
| Service `rf-oracle` | 1,006 → 957 (−49) | `QUERY` kernel 50.8 → 38.7 ns per block (64-byte queries), 60.5 → 37.6 (4,096 × 1 KiB); scalar path 270 → 147 ns per block; trace digest of the acc probe's trace 39.8 → 21.9 ms; one connection 4,096 × 64 B 6.08 → 7.37 M calls/s; 32 connections 101 → 125 M calls/s; `SIGN` of 2^16 queries 46 → 34 ms; keygen 2.66 → 2.22 s on 1 thread, about 0.70 → 0.53 s on 4 |
| Runner (Python) | 959 → 959 | none. Fixed: `Service.stop` failed on Python 3.12 (the first CI run), §2 |
| Sandbox | 220 → 220 | none. §3 has the measured start-up cost and why it stays |
| Badge mains (Lean) | 133 → 133 | none. §4 has the measured breakdown of `acc`; the one parser change I tried was slower |
| Lean proofs in `harness/lean-tools/` | none exist | nothing to golf (§5) |

Line counts are non-blank lines that are not `//` comments (Rust), counted the same way on both
trees (`scripts/loc.py` counts Lean only). For HEAD this counter gives 1,006 service lines;
RESULT §1.1 gives 1,002 by its own count.

## 1. The service (`service/src/`)

### 1.1 What changed

1. **The ten rounds are unrolled, and scalar and AVX2 share one round body** (`blake2s.rs`, the
   `rounds!` macro). Before, both compressions looped over `SIGMA` (`for s in &SIGMA`). LLVM kept
   the loop rolled, so every round loaded its 16 message indices from the table and
   bounds-checked them at run time (`objdump` of `hash8`: 16 `cmp $0x10; jae` per round). Now
   the macro expands the ten rounds with literal round numbers, so every `m[SIGMA[r][k]]` is a
   constant index. The same macro calls the scalar `g` and the AVX2 `g`. That removes the two
   copies of the eight `g` calls per round that HEAD had.
2. **`g` mixes four columns (then four diagonals) step by step.** The G calls of a half-round use
   disjoint indices, so interleaving them computes the same result. It gives the scheduler four
   independent chains and leaves fewer spills (scalar −8 %, AVX2 −3 %, measured separately).
3. **`rot16` is shift/or** (AVX2). LLVM lowered HEAD's `_mm256_shuffle_epi8` rotate to
   `vpshuflw` + `vpshufhw`, two shuffle µops on the port that is already the bottleneck. It
   recognises the shift/or form as a rotate and emits one `vpshufb`.
4. **`hash8` reads full blocks in place.** Before, every block of every lane was copied into an
   8 × 64-byte buffer and zero-filled. Now a full block is a `&[u8; 64]` into the message. Only
   a lane's partial last block is copied, once, into a zeroed pad, which needs no fill. The
   output is written by one transpose and eight 32-byte stores, not 64 scalar copies. Against
   cold data the copies were the main cost: `measure.sh`'s 1,024 × 64 KiB in-process line went
   from 84.2 to 45.1 ns per block.
5. **The request path** (`main.rs`).
   - The answers are computed in place in the response buffer. Before, they went into a separate
     `Vec` and were then copied after the header.
   - The connection's body and response buffers are kept between requests. HEAD dropped them
     whenever their capacity was above 1 MiB. So every request with a body above 1 MiB
     (4,096 × 1 KiB, 16 × 64 KiB) mapped a fresh buffer and page-faulted all of it again: the
     instrumented build showed 2.7 ms of the 9.8 ms per 4,096 × 1 KiB request in reading the
     body.
   - Memory bound. A connection now keeps at most a 16 MiB body (the body cap) and an 8 MiB
     response; 64 connections hold at most 1.5 GiB, under the service's 2 GB scope. The peak of
     one in-flight request fell by up to 8 MiB (no separate answer `Vec`). The worst case of 64
     concurrent maximal requests was above 2 GB before and is still above it, but lower. A prover
     that drives the service out of memory fails its own run (RESULT §5.1, V4-A4).
6. **Keygen advances the chains of a whole work unit together** (`wots.rs`, `compute_leaves`).
   - Before, it ran one key at a time: 133 start hashes, then three `advance` steps, each of which
     built index, message and output vectors.
   - Now the 64 keys of a work unit go together: 8,512 start hashes, then three batches of 8,512
     chain steps, then the 64 leaf hashes, in four calls.
   - The values, and the order of the leaves and the tree, are unchanged. The `vk` from fixed test
     keys is byte-identical to HEAD's (`487809…`, checked).
7. **`wipe` takes any `Copy + Default` element type** (one volatile write per element). It
   replaces `wipe` and `wipe_words`.
   - Keygen's wipe of the chain ends now writes 32-byte elements. It used to make 4,256 single-byte
     volatile writes per key, which cost 124 ms of a single-thread keygen; now 32 ms.
   - Every wipe of HEAD is still there, still volatile: the seed, the PRF state, the key block, the
     chain ends. The disassembly of the keygen worker shows the zeroing loop before the free.

### 1.2 Measured

In process, one pinned core (`logs/golf-B/service-inprocess.log`). A scratch crate links
`service/src` as a library, once from `e572344` (`git archive`) and once from this tree.

| | base | after |
|---|---:|---:|
| `eval_many` (the `QUERY` kernel), ns per block: 4,096 × 32 B | 50.4 | 41.7 |
| 4,096 × 64 B (one block after the key block) | 50.8 | 38.7 |
| 4,096 × 100 B | 48.1 | 38.1 |
| 256 × 1 KiB | 45.6 | 34.4 |
| 4,096 × 1 KiB (4 MiB, out of L2) | 60.5 | 37.6 |
| 16 × 64 KiB / 64 × 64 KiB | 46.8 / 49.2 | 35.3 / 36.8 |
| one message, scalar path, ns per block (64 B / 1 MiB / 9.18 MB) | 307 / 270 / 277 | 193 / 147 / 157 |
| `trace_digest` of 2^16 × 100 B (what `SIGN` hashes for the acc probe), ms | 39.8 | 21.9 |
| `eval_many` of the same 2^16 queries, ms | 7.6 | 6.5 |
| keygen hashing per key: 133 starts / 3 × 133 steps / leaf, µs | 7.5 / 21.7 / 3.2 | 6.2 / 17.7 / 2.4 |
| `Signer::sign`, µs | 15.6 | 13.3 |
| keygen, 1 thread, ms | 2,657 | 2,223 |
| keygen, 4 threads (cores 4–7), ms, three runs | 832, 706, 675 | 537, 498, 563 |

Over the socket (`logs/golf-B/service-ab-socket.log`). Both services run side by side and the
same `rf-bench`, built from HEAD, alternates between them; M calls/s, MB/s of query bytes in
parentheses.

| | base | after |
|---|---:|---:|
| 1 connection, 4,096 × 64 B | 6.08 (389) | 7.37 (472) |
| 1 connection, 4,096 × 32 B | 7.26 (232) | 7.71 (247) |
| 1 connection, 256 × 64 B | 2.48 (159) | 2.83 (181) |
| 1 connection, 4,096 × 1 KiB | 0.43 (437) | 0.47 (477) |
| 1 connection, 16 × 64 KiB / 1 × 64 KiB | (563) / (137) | (677) / (195) |
| 4 connections, 4,096 × 64 B | 26.6 | 29.6 |
| 32 connections, 4,096 × 64 B | 101.1 (6,472) | 125.1 (8,004) |
| 32 connections, 4,096 × 32 B | 155.5 | 185.7 |
| 32 connections, 256 × 1 KiB | (11,400) | (14,022) |
| round trip, one 32-byte query, median µs | 28.4 | 26.9 |

`SIGN`, a fresh service per run (`logs/golf-B/service-sign.log`):

| | base | after |
|---|---:|---:|
| empty trace, µs per request | 84–90 | 78–89 |
| 2^16 queries of 64 B (6.8 MB trace), ms per request | 46.2–49.0 | 32.7–35.5 |

`tests/service/measure.sh`, run once with each build (`logs/golf-B/measure-{base,after}.log`,
not interleaved):

| | base | after |
|---|---:|---:|
| keygen, AVX2: 1 / 4 / 32 threads, ms | 2,709 / 688 / 244 | 2,103 / 532 / 147 |
| keygen, scalar (`RF_ORACLE_NO_SIMD`): 1 / 4 / 32 threads, ms | 11,637 / 2,782 / 883 | 6,699 / 1,784 / 396 |
| 1 connection, 4,096 × 64 B, M calls/s | 5.57 | 7.49 |
| `SIGN` with 64 queries, 1 connection, µs per request | 153 | 124 |
| in process, 1,024 × 64 B, AVX2 / scalar, ns per block | 61.8 / 338.7 | 43.4 / 165.9 |
| in process, 1,024 × 64 KiB, AVX2 / scalar, ns per block | 84.2 / 270.0 | 45.1 / 152.4 |

Where a single-connection `QUERY` at 4,096 × 64 B still spends its time: hashing is about
160 µs of the 540 µs request. The rest is the client (`rf-bench` builds a 278 KB request and
parses the answers), three `recvfrom`s, one `sendto` and the thread wake-ups of a VM. I measured
this with a temporary instrumented build, which is not in the tree.

### 1.3 Declined

- **AVX-512** (16 lanes; `vprord` would make rot12 and rot7 one instruction each, and 32
  registers would remove the spills). This is RESULT open question 5 and the user's decision:
  it makes runners less uniform. Not built.
- **Spinning before a blocking read.** It would cut the 27 µs round trip, but it would take CPU
  from the prover, which is timed on the same CPUs.
- **Hashing one `SIGN` on two threads** (the digest following the answers): this takes CPU from
  the prover too, and the protocol computes a request on its connection's thread.
- **Reading the body without zero-filling it** (`read_to_end` on `take`). It saves about 2 % of
  a 278 KB request, in exchange for subtler code.
- **A fixed-piece padding copy instead of `memcpy`**: measured, no difference.
- **A dedicated WOTS-chain kernel for keygen** (chain values kept transposed in registers, no
  message copies). I estimate about 1.5× on keygen, but it would add a second trusted hashing
  path for work that is not timed.
- **A larger `SO_SNDBUF`.** The request direction is limited by the client's send buffer, which
  is the prover's to set. The service's responses at batch 4,096 (128 KiB) already fit. On a
  default runner `wmem_max` is 208 KiB.

### 1.4 What was checked

- `cargo test --release`: 4 unit tests pass. `many_equals_scalar` runs mixed lengths 0…4,265
  through `hash_many` and `eval_many` against the scalar `Hasher`.
- `tests/service/test_service.py`: **89/89** (`logs/golf-B/test_service.log`). It covers:
  - keyed BLAKE2s against `hashlib` on 0…65,536 bytes, in mixed batches, on both SIMD paths;
  - signatures byte for byte, and the full `vk`, against the Python reference;
  - the liveness log;
  - every refusal and cap;
  - 64 connections and a 65th refused;
  - 2^16 signatures, then `EXHAUSTED`.
- `tests/service/test_lean_signer.py .lake/build/bin/signer`: **byte-identical** to stage A's
  compiled Lean signer; `SigOkF` true (`logs/golf-B/test_lean_signer.log`).
- `vk` from `--insecure-test-keys 11…11 22…22`: identical between the HEAD and golfed binaries.
- `strace` of the golfed service under 4,096 × 64 B requests shows only `recvfrom` and `sendto`
  per request, no memory system call (`logs/golf-B/strace-requests.log`).

## 2. The runner (`harness/rfh/`, `harness/*.py`)

**The Python 3.12 bug** (orchestrator's request). The first GitHub run failed in
`tests/service/test_service.py` and `tests/harness/test_sandbox.py`.

- **Cause.** `Service.stop()` closed the service's stdin and then called `communicate(timeout=…)`.
  On Python 3.12 `communicate` first flushes stdin, which raises `ValueError: flush of closed
  file`.
- **Reproduced** on CPython 3.12.15. I installed it with `uv python install 3.12` into
  `~/.local/share/uv`, user space; no system setting was changed. Without the fix,
  `test_service.py` fails with exactly that error under 3.12.
- **Fix** (`harness/rfh/service.py`). Drop the explicit close: with no input, `communicate`
  closes stdin itself. A docstring line says why. Behaviour is unchanged: the service still sees
  end of file, wipes its keys and exits, and `stop` still returns its statistics.
- **Same pattern elsewhere.** A grep of `harness/`, `tests/` and `scripts/` for `stdin.close` and
  `communicate` finds no other instance. `tests/service/test_service.py`'s own `stop()` closes
  stdin and then reads stdout, without `communicate`, which is fine on 3.12.
- **After the fix**:
  - `test_service.py` passes 89/89 on 3.14.4 and on 3.12.15
    (`logs/golf-B/test_service{,-py312}.log`);
  - `test_sandbox.py` passes 45/45 on both (`logs/golf-B/test_sandbox{,-py312}.log`);
  - every tracked `.py` file parses with `feature_version=(3, 12)`.

**Speed: nothing changed.**

- The runner's fixed costs are process start-ups (§3) and the untimed digests of the instance.
- `chain_end` would be 23 % faster with a copied `blake2s(b"C")` state: 500 → 386 ns per step
  in this Python. It runs untimed and on every CPU (about 5 s of CPU per stream repeat at the
  season shape). I kept the line that reads like the contract, `BLAKE2s(0x43 ‖ d)`.
- The input files of a stream request are written inside the timed window; that is RB-m11, the
  reviewer's finding, and its fix is the implementer's.

**Size: nothing changed.** I read all 959 lines and found nothing to remove without losing a
check or making the code less direct.

## 3. The sandbox (`harness/rfh/sandbox.py`, `scripts/bwrap-landrun.sh`)

The timed part of a stream request is unchanged: 0.43 ms for a trivial prover (RESULT §3). The
untimed cost per sandbox is about 55 ms from spawn to teardown, and I measured where it goes
(`logs/golf-B/sandbox-startup.log`):

| Step | Median |
|---|---:|
| `systemd-run --user --scope` (the memory cap) | 34 ms (best 22) |
| `bwrap` with the namespaces and mounts | 15 ms (best 12) |
| `choom` | 5 ms (best 4) |
| `systemctl --user kill` of the scope at teardown | 14 ms (best 11) |

At the season shape that is about 56 s per stream repeat (1,025 requests), all outside the
clock. Declined:

- **Skipping the teardown kill when the sandbox exited cleanly.** It is the backstop for
  anything outside bubblewrap's pid namespace.
- **Replacing it with a write to the scope's `cgroup.kill`.** That needs the scope's cgroup path,
  which depends on systemd's slice layout and would be fragile across runners.
- **One long-lived scope shared by a stream's requests.** It changes the per-request memory cap
  and the clean-up structure.

## 4. The badge mains (`harness/badge/*.lean.in`)

A probe executable built against the acc probe's submission splits `acc` on the 9.18 MB, 2^16-query
file into its parts, each step timed between `IO.mkRef` barriers, best of 7, with the org at
`ea2e8ab` (`logs/golf-B/badge-parts.log`). The probe was built under `.lake/rf/` and removed
afterwards; `accprobe/run.py` then rebuilt the shared probe modules from their own sources.

| Part | ms |
|---|---:|
| `parseSigned` (stage B) | 17.1 |
| `traceDigestF` (stage A, `Library/Blake2sFast`) | 64.8 |
| `SigOkF` | 0.24 |
| `runSeq` of the probe's verifier | 44.2 |
| the whole check, the badge's own `verify` (`tests/harness/accprobe/run.py`, `logs/golf-B/accprobe.log`) | 130–183 (RESULT: 135–155) |

- **The parser.** It is 13 % of the check. I tried `digestAt` as
  `Vector.ofFn fun i => b.get! (o + i)`, which avoids the `extract` and the `.data` conversion.
  It parsed in 50.0 ms, 2.9× slower, so I reverted it. The parser is unchanged.
- **The rest is outside stage B.**
  - `traceDigestF` is stage A's byte path.
  - `runSeq`'s time is mostly the probe verifier's `queryK`, which builds every 100-byte query
    from a list. The contract's `ByteArray` equality is `lean_sarray_dec_eq`, a `memcmp`.
- **An observation for the reviewer and implementer: the timing idiom in `timedCheck`.**
  - `timedCheck` makes `ok` look used before the second clock reading with
    `if ok then IO.monoNanosNow else IO.monoNanosNow`.
  - In the badge's generated C (`.lake/build/ir/RFBadgeVerify.c`) `RFBadge.check` does run
    between the two `lean_io_mono_nanos_now` calls, so the measured `T_V` is right today.
  - The idiom depends on the compiler, though. In my probe, the same idiom whose result was
    discarded let the compiler drop the computation from the timed region. That is why the probe
    uses `IO.mkRef` barriers.
  - Passing the result to an IO action before reading the clock (`IO.mkRef (check …)`) would not
    depend on the optimiser. I did not change trusted timing code in a golf pass.

## 5. Lean proofs

`harness/lean-tools/` (`Gate.lean`, `TokenSweep.lean`, the generated `ChainCheck.lean`) and the
badge mains contain no theorems: the word only occurs in comments and in the gate's rule names.
There is nothing for `lean4:golf`. The chain checker sets `T_triv,best` and hence the `T_V` cap
(RESULT open question 6), so making it faster would change the cap; I left it alone.

## 6. Tests after the changes

| Test | Result | Log |
|---|---|---|
| `cargo test --release` | 4 pass | — |
| `tests/service/test_service.py` | 89/89; also on Python 3.12.15 | `logs/golf-B/test_service.log`, `test_service-py312.log` |
| `tests/service/test_lean_signer.py .lake/build/bin/signer` | byte-identical; `SigOkF` true | `logs/golf-B/test_lean_signer.log` |
| `tests/harness/test_sandbox.py` | 45/45; also on Python 3.12.15 | `logs/golf-B/test_sandbox.log`, `test_sandbox-py312.log` |
| `tests/harness/smoke.py --mock` | 0 failures: honest pass, three broken provers rejected | `logs/golf-B/smoke-mock.log` |
| `tests/harness/smoke.py --org` | **11 checks, 0 failures**, 5 min 44 s: certified; ACCEPT with the compiled `accF` badge (canaries 62 + 16, DoS, liveness, score); three broken provers REJECT; `sorry` PROVISIONAL; `#eval` REJECT | `logs/golf-B/smoke-e2e.log` |
| `tests/harness/accprobe/run.py` (the badge on a 2^16-query trace signed by the golfed service) | accept 130–183 ms, reject 97–109 ms | `logs/golf-B/accprobe.log` |

The first `--org` run failed in the comparator because the org tree was stale. `ea2e8ab` had
changed `Contract/Oracle.lean` and `Contract/Signature.lean`, so the comparator's fresh build
tried to rebuild them inside the read-only org (`Oracle.ltar: read-only file system`). Re-running
`harness/org-setup.sh` on the worktree (4 min 40 s, `logs/golf-B/org-setup.log`) fixed it.

## 7. For the implementer

- RESULT §1.1 (service lines) and §3 (service throughput, keygen, `SIGN`) now give the base build's
  numbers. The tables in §1.2 replace them.
- `service/PROTOCOL.md` §4 still holds: the eight-lane AVX2 hashing and the grouping by block
  count are unchanged.
- §4 suggests a barrier in `timedCheck`; it is not applied.
- Nothing is committed.

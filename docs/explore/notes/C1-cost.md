# C1. Cost model: root verification, the oracle charge, D4 realism, the oracle service

Cost note, 2026-10-20, for `docs/explore/BRIEF.md` §3 (v3, D1, D2, D4, D3). Tags: **[M]** measured
(log named), **[P]** published (cited), **[E]** estimate (arithmetic shown or in `arith.py`), **[A]**
argument. "Dev VM" is the 32-vCPU QEMU VM with no `pclmulqdq`/`gfni`, shared with other agents; it
is not the reference machine. `h_V` is the number of BLAKE2s compressions one verification feeds
to the oracle (not the query count: one query may span many 64-byte blocks). Shapes: **ranked**
`r = 8`, `n = 2^14` (256 leaves, 255 nodes, `2^22` chain compressions); **long** `r = 4`, `n = 2^20`
(`2^24`); **IVC** one chain of `2^20` steps, `k` chain steps per IVC step.

## 0. Summary

| # | Quantity | Value | Tag |
|---|---|---|---|
| 1 | Witness-sending (WS) root check, ranked tree, one core | 0.19 s (8-way SIMD BLAKE2s) · 0.54 s (Rust scalar) · 0.64–0.69 s (Lean unrolled) · 21 s (reference Lean); 37–43 ms wall threaded; root 34,728 B | E · E · M · M |
| 2 | Real recursion root (v3; D4 adds online calls) | one proof, `h_V` ≈ 10k–26k, 0.2–0.8 MiB, 8–30 ms on a machine with carry-less multiply; **0.5 s on the dev VM** (Flock verify alone 477 ms) | E/P/M |
| 3 | Compression of real recursion against WS | 160–420× in compressions; 6–24× in one-core CPU against the best WS, 18–67× against Rust scalar | E |
| 4 | Deferral recursion root (D1/D2: a relativized node leaves its children's queries to the root) | re-asks `511·h_V` = 2.6–13.2 M compressions = **0.6–3.2× WS's work**; root ≥ 80–850 MB | E/A |
| 5 | Concatenation of 256 leaf SNARKs | 1.3–6.6 M oracle compressions + 256 local checks: ≥ 2 s (WHIR-class), 210 s (spartan-chain, 256 × 0.82 s) | E/M |
| 6 | `T_V` cap (CPU, one core), ranked | window ≈ 30–45 ms … 191 ms: a cap of 75–93 ms separates real recursion, D4 and a flat SNARK from WS by 2–2.5× each side; nothing separates deferral or concatenation (both slower than WS); #6's `/10` rule gives 19 ms, below some honest recursive verifiers | E |
| 7 | Same, long shape and IVC | long: WS best 0.77 s, real 8–30 ms (25–95×), deferral 35–90 ms (9–22×), `/10` cap 77 ms admits deferral narrowly; IVC: WS 130 ms serial, real 4–16×, deferral only for `k ≥ 2^17` | E |
| 8 | Leaf-level check (D1 runs no tree) | WS leaf 2.0 ms (one sequential chain) **beats** a SNARK leaf (8–30 ms WHIR-class, 0.82 s spartan-chain) at `n = 2^14`; ≥ 4× separation only at `n ≈ 2^20` | M/E |
| 9 | D1 charge with `t_hash = T_leaf/n` | score = `T_leaf·(1 + h_V/n)`; `h_V/n` = 0.31 (spartan-chain per query), 1.58 (per compression), 0.56 (leanVM child); per tree 0.6–3.2× the leaf time; at `n = 2^20` ≈ 0.01 (WHIR-class), 0.16 (Ligero) | E |
| 10 | Share of a real recursion step that a hash charge captures | R1CS-of-bits BLAKE2s 93–99.6% · FRI-based (Plonky2, Stwo) 69–75% · leanVM ≈ 10% · non-native verifier field < 1% | E/P |
| 11 | D4 in-circuit list hash against real-recursion hashing | 1.09× (spartan-chain child, 28.3k vs 25.9k); 0.79–1.56× per Merkle node query; D3 adds 145–1,059 compressions per child (0.5–12%) | E/P |
| 12 | Prover oracle traffic per leaf proof | spartan-chain: 262,614 calls, 4.47 M compressions, 278 MB (34k calls/s at its 7.7 s); Flock/WHIR-class: ≈ 10^6 calls, 64–100 MiB | E |
| 13 | Keyed-BLAKE2s service over shared memory, dev VM | batched single stream 1.2× in-process; unbatched 2.3× (spin), 82× (futex, 37 µs per call); whole machine 10–12.5 Mcalls/s (65 B) and 1.8–2.5 GB/s (2 KiB) = 0.3–0.6× in-process | M |
| 14 | True-random table against a PRF | 71 GB of queries for the ranked tree's leaves alone; 17–69 GB with 32-byte fingerprints; PRF 32 B, stateless | E |
| 15 | "A million hash chains" | 89 days at spartan-chain speed (`n = 2^14`), 51 h at `n = 16`, 9.4 h at Flock M4-Max speed; a ±1% median needs 14–62 samples at CV 3–6.3% (measured 3.7%, published up to 6.3%) | M/E/P |

Conclusions.

1. **At the ranked shape a leaf is about one verification's worth of hashing** (`n = 16,384` against
   `h_V = 5k–26k`). So every strategy that leaves inner verifications' oracle calls to the root
   (deferral, concatenation) does as much or more root work than WS: `511·h_V ≥ 2^22` once
   `h_V ≥ 8.2k`. That is the impossibility result (`vq = Ω(t)`) in numbers. In D1/D2 the only
   compressing root is a **flat SNARK** with no recursion below it (rows 4–6; A1 M7).
2. **Real recursion compresses 6–24× in CPU and 160–420× in hashing** (v3, D4). A CPU-time `T_V`
   can separate it from WS, but with a 2–2.5× margin per side at the ranked shape, and only on a
   machine with carry-less multiply: on the dev VM a binary-field root check (≈ 0.5 s) is slower
   than SIMD WS (0.19 s). The margin reaches 25–95× at the long shape.
3. **A hash charge prices most of recursion only in hash-heavy arithmetisations.** It captures 93% or
   more of an R1CS-of-bits step, 69–75% of a FRI-based step (Plonky2, Stwo), ≈ 10% of a leanVM step, and almost nothing
   when the verifier's field is non-native. With `t_hash = T_leaf/n` it is multiplicative, it is the
   same size as the leaf time at `n = 2^14`, and it falls to ≈ 1% at `n = 2^20` for WHIR-class verifiers.
4. **D4 costs what real recursion costs** (0.8–1.6× in-circuit). Its other costs are on the service:
   `certify` recomputes 4.7–14.5 M compressions per tree (1.1–3.5× WS's work), and a fast prover's
   Merkle traffic (≈ 2–3 GB/s) saturates a naive service.

## 1. Inputs

| Quantity | Value | Tag, source |
|---|---|---|
| BLAKE2s compression, Rust scalar (`chainEnd`, `2^14` steps in 2,102 µs) | 128 ns | M `submissions/logs/probes/fieldbench.log` |
| `blake2s_simd`, one 33-byte hash / `hash_many` 8-way | 124 ns / 45.6 ns per hash | M same log |
| Lean BLAKE2s unrolled / contract reference | 151–164 ns / 5.6–6.1 µs per compression | M `logs/adv-probes/{fastchain,refchain}.log` (#6) |
| This note's C keyed BLAKE2s (generic round code, key block cached) | 227–268 ns per compression, ≈ 1.8× `blake2s_simd` | M `docs/explore/probes/c1-cost/svc.log` |
| spartan-chain, `n = 2^14` | prove 7.43–7.98 s (≈ 2,200% CPU), 3.95 GB; proof 1,464,107 B; native verify 0.81–0.84 s, one thread; 5,156 queries | M S2b RESULT §5, `reports/rust-prover.md` §3 |
| spartan-chain `h_V`, `n = 2^14` | 25.9k compressions = Merkle `260·(33 + 17)` = 13,000 + absorbs `794,527/64 + 85` = 12,500 + squeezes 390; field ≈ 3.1·10^7 `K`-mul | E BLUEPRINT-R1 §6.3, §7, §12 |
| spartan-chain at `n = 16`, `2^10` | 0.18–0.19 s, 0.70–0.71 s | M S2b §5 |
| `K` / `E` product, Rust, dev VM | 17.5 ns / 66 ns | M `rust-prover.md` §3 |
| WS root proof, ranked | 34,728 B | M S2a RESULT §6.1 |
| Flock, `2^14` compressions, dev VM | prove 14.25 s (1,150/s), verify 477 ms | M `logs/probes/flock-2e14.log` |
| Flock, `2^18` compressions, Mac M4 Max | 540 ms (485,033/s), verify 1.9 ms | P leanVM README at `a386121f` |
| leanVM 2→1 recursion, M4 Max | 686,085 steps, BLAKE2S 2^14.169 = 18,420 (2.7% of steps), 206.3 KiB, 0.394 s, verify 14.6 ms | P same |
| leanVM aggregation | 900 XMSS → 2^16.989 BLAKE2s (145 each); 245 SPHINCS → 2^16.992 (532 each) | P same; E division |
| WHIR, Goldilocks³, λ = 128, ρ = 1/2 | `2^22`: UD 541 KiB, JB 274 KiB; `2^24`: UD 621 KiB/4.8 ms/10k hashes, JB 299/2.5/5.1k; `2^28`: UD 770/6.7/14k, JB 339/2.9/6.4k | P WHIR (ePrint 2024/1586) Table 5, via core-workspace R7 §2.2 |
| BLAKE2s compression in a circuit | Flock: 14,720 AND rows (15,136 rows, 82 M nnz); R1CS with XOR wires: 40,992 rows, 207k nnz; spartan-chain block: `2^14` positions; AIR/plonkish `2^10`–`2^11` cells | P D3 §5.1 (exact counts), `reports/blake2s-r1cs.md`; E F1 §5.2 |
| Plonky2 recursion circuit | `2^12` gates, ≈ 75% Merkle (Poseidon) hashing | P Plonky2 whitepaper, via R7 §5 |
| Stwo recursion (Poseidon2/M31, blowup 2) | Poseidon rows 164,040 × 96 columns against Plonk rows 231,881 × 30: 69% of cells | P row counts (l2iv research, "Recursive proofs in Stwo, part II"); E share |

Logs under `submissions/logs/` are local to the submissions repository (gitignored). `SP` is the
session scratchpad named in the brief; `docs/explore/probes/c1-cost/` holds this note's probe (`svc.c` → `svc.log`; `svc2.c`, the
multi-client version, → `svc-multi.log`) and arithmetic (`arith.py`, `arith.log`).

## 2. Root verification

### 2.1 Ranked shape (`r = 8`, `n = 2^14`)

`h_V` per proof: WHIR-class 5.1k–12k (Table 5 JB/UD plus Fiat–Shamir absorbs), leanVM-class 9.2k
(18,420 per 2→1 step), spartan-chain 25.9k. CPU is one core. "Best WS" is 0.19 s.

| Design | Strategy | Root oracle calls (compressions) | Root local work | Root proof | CPU, one core | vs best WS (CPU) |
|---|---|---|---|---|---|---|
| all | **WS** | 0 | `2^22` concrete compressions | 34,728 B [M] | 0.19 s [E] · 0.54 s [E] · 0.64–0.69 s [M] | 1× |
| v3 | concatenation | 0 (V hashes locally): `256·h_V` = 1.3–6.6 M | + 256 field checks | 256 × 274–541 KiB = 69–135 MiB (WHIR); 375 MB (spartan-chain) | ≥ 2 s (WHIR, 256 × 8 ms) [E]; 210 s (256 × 0.82 s) [E from M] | 0.001–0.1× |
| v3 | **real recursion** | 0 (local): `h_V` = 10–26k | WHIR 2.5–6.7 ms [P, its machine] + Spartan 5–20 ms [E: 0.7–3·10^5 `E`-mul at 66 ns] | 0.2–0.8 MiB [P: 206 KiB leanVM; 621–770 KiB UD] | 8–30 ms [E]; leanVM 14.6 ms [P, M4]; ≈ 0.5 s dev VM [M, Flock verify] | 6–24× |
| v3 | flat SNARK (WS below level 8) | 0 (local): ≈ 16k | as real | ≈ 0.82 MiB UD / 0.35 MiB JB at `2^30` packed [E, Table 5 trend] | 10–30 ms [E] | 6–19× |
| D1 | (no tree is run) | — | — | — | leaf-level only, §2.3 | — |
| D2 | concatenation | `256·h_V` = 1.3–6.6 M via the service | 256 field checks | as v3 | ≥ 2.4 s [E: + 0.36–1.8 s at 278 ns per compression, §5.2] | ≤ 0.08× |
| D2 | **deferral** (relativized node) | `511·h_V` = 2.6–13.2 M | root proof only | ≥ `511·32·h_V` … `511·64·h_V` B = 80–850 MB [E/A] | 0.7–3.7 s via the service; 0.33–1.7 s if hashed in process [E] | 0.05–0.6× |
| D2 | real recursion | not available: the node would arithmetise the oracle | | | | |
| D2 | flat SNARK | ≈ 16k | as v3 | as v3 | 15–40 ms [E] | 5–13× |
| D4 | real recursion, **flat** attestation | `h_V` (root's own, 10–26k) + 511 attests | as v3 | + 511 × 32 = 16,352 B | 11–45 ms [E: + 3–15 ms of batched calls] | 4–17× |
| D4 | real recursion, **recursive** attestation | `h_V` + 1 attest | as v3 | + 32 B | 11–45 ms [E] | 4–17× |

Compression in hashing (WS's `2^22` against the root's oracle compressions): real recursion and D4
160–420×; flat SNARK ≈ 260×; deferral 0.32–1.61× (`2^22/(511·h_V)`; ≥ 1 only for `h_V ≤ 8.2k`);
concatenation 0.63–3.2× in hashing but ≤ 0.1× in CPU, because each leaf check costs ≥ 8 ms of field
work against 2.0 ms of recomputation. [E]

Notes. (a) The deferral root proof must make every deferred query `q` available to the root
verifier; Merkle climbs make about half of the bytes derivable from answers, hence the range. This is
the argument-size bound (`as = Ω(t)`) of the paper in numbers [A]. A1 M2 reaches the same 2.6 M
queries and ≈ 250 MB. (b) In D2 the service does the hashing in another process. A `T_V` that times
only `V`'s process sees copies and waits, so oracle calls are free CPU. The cap must count the
service's work done for `V`, or charge the calls. (c) The dev VM row of real recursion is a machine
artefact. leanVM's field code falls back to a 22 ns loop without `pclmulqdq` (`fieldbench.log`), and
Flock verify takes 477 ms here against 1.9 ms on the M4 Max at 16× the size. `T_V` must be
calibrated on the reference machine (DESIGN §6.4 gives it carry-less multiply).

### 2.2 Long shape and IVC

| Shape | WS best (one core) | Real recursion | Deferral root | Concatenation | Flat SNARK |
|---|---|---|---|---|---|
| long, `r = 4`, `n = 2^20` (`2^24`) | 0.77 s SIMD · 2.15 s Rust · 2.65 s Lean [E] | 8–30 ms: 25–95× | `31·h_V` = 0.2–0.43 M compressions (`h_V` 6.4k–14k at `2^28`): 25–56 ms local + root ≈ 35–90 ms: 9–22× | 16 × 13.5 ms ≈ 0.22 s: 3.5× [E: WHIR UD 6.7 ms + Spartan 5 ms + 1.8 ms hashing] | ≈ 17k compressions, 10–30 ms |
| IVC, `k = 1` | 130 ms (`2^20` sequential at 124 ns; no SIMD, one dependency chain) | 8–30 ms: 4–16× | `2^20·10^4` ≈ 10^10 compressions: 1,350 s | — | — |
| IVC, `k = 2^14` | 130 ms | 4–16× | 0.64 M: 82 ms + root ≈ 90 ms (1.4×) | — | — |
| IVC, `k = 2^17` | 130 ms | 4–16× | 80k: ≈ 20 ms (6.5×) | — | — |

The proving overhead of recursion is `h_V/k` compression-equivalents per useful step: 10^4 at
`k = 1`, 0.6 at `k = 2^14`, 0.08 at `k = 2^17` [E]. D4 IVC needs recursive attestation: flat
attestation at `k = 1` makes `2^20` attest calls at the root, as slow as WS.

**Tree work: recursion against a flat SNARK** (the issue #6(b) channel), with the node cost
expressed in leaf units [E]:

| Arithmetisation | Node / leaf proving | Tree (256 leaves + 255 nodes) / flat (256 leaves) |
|---|---|---|
| R1CS of bits, spartan-chain-like children (`2·25.9k/16,384` = 3.16) | 3.16 | 4.15× |
| R1CS of bits, WHIR-class children (`2·12k/16,384`) | 1.46 | 2.46× |
| leanVM-class (Flock leaf 34 ms at 485k/s; node 0.394 s) | 11.6 | 12.6× |
| leanVM-class, long shape (leaf `2^20/485k` = 2.16 s) | 0.18 | 1.17× |

At the ranked shape recursion costs 2.5–12.6× the work of proving the same `2^22` compressions
flat. Memory is the only bound: spartan-chain's 3.95 GB per `2^14` scales to ≈ 1 TB at level 8, so
`j ≤ 4` under 96 GB (A1 M7). At the long shape recursion is nearly free (1.17×).

### 2.3 What a `T_V` cap separates

CPU time, one core, as #6 proposes. A cap separates A from B if both sides clear it by a margin.

| Shape | Pass (worst case) | WS best | Window | Margin per side at the geometric middle | `T_V = T_triv,best/10` |
|---|---|---|---|---|---|
| ranked | real 8–30 ms, flat 10–30 ms, D4 11–45 ms | 191 ms | 45–191 ms | ≈ 2× (≈ 93 ms); 2.5× (≈ 75 ms) if every passing design stays under 30 ms | 19 ms: excludes recursive verifiers above 19 ms, a 1.0–2.4× headroom for the fast end |
| ranked | deferral 0.33–3.7 s, concat ≥ 2 s | 191 ms | none: both are slower than WS | — | — |
| long | real/flat 8–30 ms | 766 ms | 30–766 ms | ≈ 5× (≈ 150 ms) | 77 ms: real passes 2.6–10×, deferral (35–90 ms) borderline, concat (0.22 s) fails 2.8× |
| IVC | real 8–30 ms | 130 ms | 30–130 ms | ≈ 2× | 13 ms: only the fastest real recursion |

**Leaf-level (D1).** D1 runs no tree, so the only check is on a leaf. A WS leaf is one chain of
`2^14` sequential compressions: 2.0 ms at 124 ns, with no SIMD or thread speed-up. A SNARK leaf check
costs 8–30 ms (WHIR-class) or 0.82 s (spartan-chain) [M/E]. WS wins by 4–15×. Break-even is at
`n ≈ 2^16`–`2^18`. At `n = 2^20` WS takes 130 ms against 8–30 ms, a 4–16× separation. A1 M6 has
`2^15`–`2^16` and `2^19` for 10× using 160 ns per compression and 5–10 ms per check. The range is
the uncertainty in the SNARK check.

## 3. The oracle charge (D1, D2)

### 3.1 What `t_hash` can be

| Choice | Values | Tag |
|---|---|---|
| `T_leaf / n` from the submitter's leaf | spartan-chain: 11.4 ms (`n = 16`), 0.69 ms (`2^10`), 0.47 ms (`2^14`), dev VM; Flock: 0.87 ms (`2^14`, dev VM), 2.06 µs (`2^18`, M4 Max) | M/P, E division |
| in-circuit size of one compression | 14,720 AND rows (Flock) · 40,992 rows (R1CS, explicit XOR) · `2^14` positions (spartan-chain) · `2^10`–`2^11` cells (AIR, estimate) | P/E |
| fixed constant in seconds | e.g. 2.06 µs (Flock published) or 0.47 ms (spartan-chain, dev VM) | — |

`T_leaf/n` spans 24× across `n` for one prover, because fixed PCS costs dominate small leaves. It
spans 400× across two machines for one prover (Flock: dev VM against M4 Max, because of carry-less
multiply), and 230× across provers. A size in rows needs a price per row, which is
system-specific: 0.47 ms / `2^14` = 29 ns per spartan-chain position (dev VM, 22 cores), 2.06 µs /
14,720 = 0.14 ns per Flock AND row (M4 Max). A fixed constant in seconds decides whether the charge
matters at all. For a
spartan-chain-like node (`2·25.9k` compressions) it is 0.107 s (1.4% of `T_leaf`) at 2.06 µs and
24 s (3.2× `T_leaf`) at 0.47 ms [E].

### 3.2 Magnitude against leaf proving

With `t_hash = T_leaf/n` the charge per proof is `h_V·T_leaf/n`, so the score is
`T_leaf·(1 + h_V/n)`: the additive charge is multiplicative. Over a tree (510 child verifications
against 256 leaves) the charge is `(510/256)·h_V/n` times the total leaf time [E]:

| Verifier | `h_V/n` at `n = 2^14` | Charge / leaf time, ranked tree | `h_V/n` at `n = 2^20` |
|---|---|---|---|
| spartan-chain, charged per **query** (5,156) | 0.31 | 0.63 | 0.0074 (7,774 queries) |
| spartan-chain, charged per **compression** (25.9k) | 1.58 | 3.15 | 0.16 (≈ 170k: Ligero's `√N` columns) |
| leanVM-class child (9.2k) | 0.56 | 1.12 | ≈ 0.01 |
| WHIR-UD-class with FS (≈ 12k) | 0.73 | 1.46 | ≈ 0.013 |

At the ranked shape the charge is about the size of the leaf time, so it shapes designs. At
`n = 2^20` it is noise, and D1 becomes a flat leaf-SNARK speed contest. For IVC at `k = 1` it is
`10^4` times the step.

### 3.3 What fraction of a real recursion step the charge captures

| System | Hash share of one recursion step | Missed | Tag |
|---|---|---|---|
| R1CS of bits, BLAKE2s gadget (`2^14` rows), spartan-chain children | `2·25.9k·2^14` = 8.5·10^8 hash rows against 6.2·10^7 `K`-mul rows: **93%** | Ligero column checks (`7k` `K`-mul per column) | E |
| same, WHIR-class children (10k compressions, 10^5 `E`-mul = 6·10^5 `K` rows) | **99.6%** | sumcheck, folding | E |
| Plonky2 (Poseidon, Goldilocks, FRI) | **≈ 75%** of gates | field and FRI folding, ≈ 25% | P |
| Stwo (Poseidon2, M31, Circle-FRI) | **≈ 69%** of cells | Plonk rows: FRI answers, folding | E from P |
| leanVM (Flock precompile, binary field) | 2.7% of steps; `18,420 × 2.06 µs = 38 ms` of 0.394 s: **≈ 10%** | MUL 31%, DEREF 31%, XOR 25% of steps: field arithmetic, memory, sumcheck/GKR verification, deferred-claim batching | E from P |
| verifier field non-native to the circuit (`GF(2^64)` checks in a prime-field circuit, ≈ 4,096 AND rows per `K`-mul) | `3.1·10^7·4,096` = 1.3·10^11 field rows against 8.5·10^8: **< 1%** | nearly everything | E |

The charge misses, in order of size: the verifier's field arithmetic (zero in D1, bounded only by
`T_V`); evaluating the constraint system's matrices, which leanVM defers to the root because
in-circuit "it would dwarf the entire remaining verifier" (leanVM doc §9; 89 M nonzeros) [P];
non-native arithmetic; and node bookkeeping (statement hashing with concrete BLAKE2s). Under
`t_hash = T_leaf/n`, D1 charges a leanVM-like design ≈ 10% of its true node cost and an
R1CS-of-bits design ≈ 95%. So it favours architectures whose recursion overhead is not hashing,
the opposite of the intended signal.

### 3.4 Where the charge is gamed

- **Per query against per block.** spartan-chain makes 5,156 queries but 25.9k compressions. Its
  absorb of `ū` alone is one query of 393 KB (6,144 compressions) [E]. Merkle arity trades queries
  for bytes. Charge per 64-byte block of `0x52 ‖ q`.
- **WS pays nothing.** No proving and no oracle calls give a D1 score of `0 + 0`, and the leaf-level
  cap cannot exclude it at `n = 2^14` (§2.3). A1 M4.
- **Local field work is free.** spartan-chain's 3.1·10^7 `K`-mul (0.54 s at 17.5 ns) is unpriced.
- **Flattening.** In D2, children with no oracle calls are re-asked for free, so "WS below level `j`,
  one SNARK above" pays one `h_V` (A1 M7). Table 2.2 shows it also saves 2.5–12.6× in proving.

## 4. Realism of D4 (and D3)

### 4.1 In-circuit list hashing against computing the hashes

The list encoding assumed: each entry is a 4-byte length, then `q`, then the 32-byte answer, streamed
through BLAKE2s, so the cost is total bytes / 64. Real recursion computes `BLAKE2s(0x52 ‖ q)` per
query [E]:

| Query | bytes of `0x52 ‖ q` | Real recursion (compressions) | D4 entry bytes | D4 (compressions) | D4 / real |
|---|---|---|---|---|---|
| Merkle node, 31-byte labels (spartan-chain `[D-8]`) | 64 | 1 | 100 | 1.56 | 1.56 |
| Merkle node, 32-byte labels | 65 | 2 | 101 | 1.58 | 0.79 |
| spartan-chain column leaf (`m = 256`) | 2,050 | 33 | 2,086 | 32.6 | 0.99 |
| FS squeeze | 34 | 1 | 70 | 1.09 | 1.09 |
| FS absorb of `L` bytes | 35 + `L` | `⌈(35+L)/64⌉` | 71 + `L` | `(71+L)/64` | → 1 |
| **spartan-chain child, whole list** | | **25.9k** | 1.81 MB | **28.3k** | **1.09** |

A WHIR- or leanVM-class child is dominated by 64-byte node queries, so the ratio is 0.79–1.56. An
encoding that omits every answer the circuit already holds as the next query's input (all Merkle
answers below the root) gives (Σ over queries of the bytes of `q`) / 64, which is the
real-recursion cost. **The claim holds: D4's in-circuit cost is real recursion's to within
0.8–1.6×.** It therefore inherits #8's sizing: 28.3k
compressions × `2^14` rows ≈ 4.6·10^8 rows per child in R1CS of bits, and only WHIR-class proofs fit
`proofCap`.

### 4.2 Per-child constants

| Design | In circuit, per child | Root | Tag |
|---|---|---|---|
| D4 flat | 0 (the list hash is a public output) | 511 attest calls: ≈ 0.3 ms batched, 19 ms at one futex round trip each; +16,352 B | E/M |
| D4 recursive | the children's attested hashes as two list entries: ≈ 2 × 69 B ≈ 2.2 compressions | 1 attest call, +32 B | E |
| D3, XMSS (leanSig parameters) | 145 compressions | one native signature check (≈ 20 µs) | P/E |
| D3, SPHINCS (leanVM's parameters) | 532 compressions | ≈ 70 µs | P/E |
| D3, WOTS+ (`w = 16`, 32 B, 67 chains) + Merkle path `h = 20` | 556 average, 1,059 worst (`67·7.5 + 34 + 20`; `67·15 + 54`) | ≈ 70–130 µs | E |

Against a child list of 9.2k–28.3k compressions, D3 adds 0.5–11.5%. A stateful XMSS key with
`h = 20` signs 511 lists per evaluation for about 2,000 evaluations.

### 4.3 Service-side work

`certify` re-evaluates every listed `(q, a)`: 511 × 9.2k–28.3k = 4.7–14.5 M compressions per ranked
tree, 1.1–3.5× WS's `2^22`. That is 0.07–0.22 s at the machine-wide in-process rate (65.6 M
compressions/s, §5.2) [E]. It runs during the tree, in harness CPU. It is cheap, but it is real work
outside the prover's budget. `certify` also returns a concrete BLAKE2s digest of a prover-chosen
string, so it is a hashing service the prover can call. Both must be metered.

## 5. The oracle service (D2, D4)

### 5.1 Calls the prover makes

Every Merkle commitment must hash through the oracle; a commitment under a concrete hash binds only
by collision resistance, which the counting form cannot charge (F1 §1). Per leaf proof [E]:

| Prover | Calls | Compressions | Bytes | Rate at its own speed |
|---|---|---|---|---|
| spartan-chain, `n = 2^14` (`2^17` leaves of 2,050 B, `2^17 − 1` nodes of 64 B, 476 FS calls) | 262,614 | 4.47 M | 278 MB | 34k calls/s, 36 MB/s at 7.7 s; ranked-tree leaves 6.7·10^7 calls, 71 GB |
| Flock/WHIR-class, `2^14` compressions (`2^27.9` bits → `2^22` packed `K` → `2^23` at ρ = 1/2: 64 MiB, plus later rounds) | ≈ 10^6 | ≈ 1.5–2 M | 64–100 MiB | ≈ 30 M calls/s, 2–3 GB/s at Flock's M4-Max 34 ms |

spartan-chain's in-process Merkle phase takes 0.1 s of its 7.7 s (measured). The verifier side is
small: `h_V` = 5k–26k per proof, of which about 400 are sequential Fiat–Shamir calls.

### 5.2 Measured service throughput (dev VM)

Probe `docs/explore/probes/c1-cost/svc.c` (multi-client rows: `svc2.c`). Keyed BLAKE2s-256 with the key block compressed once and cached; the
known answer agrees with Python `hashlib.blake2s(key=…)`. The client process copies `B` queries into a
shared `mmap`, posts a sequence number, waits (spinning or by futex), and copies the answers out.
There is no double buffering. Load average 1.8–3.5 during the runs (`svc.log`, `svc-multi.log`) [M]:

| Configuration | ns per call (65 B, 2 compressions) | Rate | Against in-process |
|---|---|---|---|
| in-process, one thread | 454 | 2.08 Mcalls/s | 1× |
| service, one server thread, `B = 1`, futex | 37,377 | 0.027 Mcalls/s | **82×** slower |
| service, `B = 1`, spin | 1,039 | 0.96 Mcalls/s | 2.3× |
| service, `B = 256`, spin / futex | 556 / 888 | 1.80 / 1.13 Mcalls/s | **1.22×** / 1.96× |
| in-process, 24 / 32 threads | — | 32.8 / 38.2 Mcalls/s | 1× |
| service, one client, 24 server threads, `B = 4096`, spin / futex | 96.9 / 226 | 10.3 / 4.4 Mcalls/s | 3.2× / 7.4× |
| service, 8 clients × 2 servers, `B = 1024`, spin | — | 12.5 Mcalls/s | 2.6× |
| 2-KiB columns: in-process 24 / 32 threads | — | 4.10 / 4.95 GB/s | 1× |
| 2-KiB columns: service, one client × 24 servers; 12 × 1 | — | 2.52; 1.81 GB/s | 1.6×; 2.3× |

The C compression is 1.8× slower than `blake2s_simd` and 5× slower than its 8-way `hash_many`, so
the hashing-bound rows would improve by up to 5× with a SIMD service. The copy-and-synchronise rows
would not.

### 5.3 True-random table against a PRF [E]

The ranked tree's leaves make 6.7·10^7 (spartan-chain) to 2.7·10^8 (WHIR-class) distinct calls,
and the nodes about as many again. Storing queries takes 71 GB for spartan-chain's leaves alone,
above the dev VM's 62 GB. Storing 32-byte fingerprints with 32-byte answers at load 0.5 (128 B per
entry) takes 17 GB (spartan-chain tree) to 69 GB (WHIR-class, 512 proofs × `2^20`). A fingerprint
is itself a keyed hash, so the table adds memory and a shared lock and buys nothing over the PRF. The
table must also persist from the tree run to the root and sample checks. A PRF needs a 32-byte key,
is stateless and parallel, and costs no extra compression per call once the key block is cached.
**Use a PRF.**

### 5.4 Slowdown in practice [E from M]

- **spartan-chain-speed provers.** The Merkle traffic of 278 MB at 1.8–2.5 GB/s plus 131k node calls
  at 10–12.5 Mcalls/s takes 0.12–0.17 s, against 0.1 s in process. With 476 sequential FS calls at
  1–37 µs (0.5–18 ms), the total is **+0.3–1.2% of `T_leaf`**.
- **Flock-class provers**, the competition's target. 64–100 MiB per 34 ms leaf against 1.8–2.5 GB/s
  is 27–58 ms of service time, against ≈ 14–26 ms in process: **+30–110% of leaf time** with this
  naive service. Closing the gap needs double-buffered rings, a SIMD multi-buffer BLAKE2s, and
  service cores reserved outside the prover's cgroup.
- **The service's CPU must be priced.** Cores outside the cgroup are free hashing for the prover,
  which favours Merkle-heavy designs. Cores inside it compete with the prover.
- **Online verification.** The root's own 10k–26k calls take 3–12 ms batched. Its about 400
  sequential FS calls take 0.4 ms (spin) or 15 ms (futex).

## 6. The "million hash chains" benchmark (D1)

### 6.1 Run time

| Prover (dev VM unless marked) | One leaf | 10^6 leaves | Tag |
|---|---|---|---|
| spartan-chain Rust, `n = 2^14` (22 cores) | 7.67 s | 7.7·10^6 s = **89 days** | M, E product |
| spartan-chain, `n = 2^10` / `n = 16` | 0.707 / 0.183 s | 8.2 days / 51 h | M, E |
| spartan-chain Lean `P`, `n = 16` | 34.9 s | 404 days | M, E |
| Flock, `2^14`, dev VM / M4-Max rate | 14.25 s / 33.8 ms | 165 days / 9.4 h | M / P, E |

A million samples is infeasible on the dev VM and unnecessary (§6.2). A1 M5 gives 35–90 machine-days.
If "a million hash chains" means one chain of `10^6 ≈ 2^20` steps: spartan-chain did not attempt
it (10.2 MiB proof; ≈ 3.95 GB × 64 ≈ 250 GB by linear scaling, above 62 GB). Flock at M4-Max rate
would take ≈ 2.2 s.

### 6.2 Samples for a stable median

These provers are data-oblivious: the work is fixed by `n`, so the spread over instances is machine
noise, not instance variance. Measured CV: spartan-chain at `2^14`, 3.7% (7.43, 7.61, 7.98 s)
[M]; leanVM publishes ±1.8–6.3% [P]. The standard error of a median is ≈ 1.2533·σ/√N, so a relative
precision `p` needs `N ≈ (1.2533·CV/p)²` [E]:

| CV | ±1% | ±0.5% |
|---|---|---|
| 3% | 14 | 57 |
| 3.7% | 22 | 86 |
| 6.3% | 62 | 249 |

v2's record rule (5 ABBA pairs, median ratio ≤ 0.97) resolves a 3% step at 2σ only if CV ≤ 1.9%
(the SE of the ratio of two 5-sample medians is ≈ 0.79·CV). On a shared VM (load average 3.8–16
during the spartan-chain runs) noise drifts with co-tenants. Drift is bias, which more samples do not
remove and pairing does. Mean, median and geomean of equal-size instances agree up to noise. A
geomean matters only across sizes, where it overweights small `n`: `T_leaf/n` is 24× larger at
`n = 16` than at `2^14`.

### 6.3 What a statistic over independent proofs measures

- **It measures single-leaf latency.** A whole-tree makespan measures the throughput of 511 proofs,
  the 8-level critical path of node proofs, and memory pressure under 96 GB.
- **The leaf's share of real tree work** is 24% (R1CS of bits, node ≈ 3.16 leaves), 41% (WHIR-class
  children, 1.46), or 8% (leanVM-class, 11.6) [E, §2.2]. D1 measures that share and replaces the rest
  by the charge, which itself prices only the hashing part (§3.3).
- **Total wall time over 10^6 chains invites batching.** A single Flock-style SNARK over 2^18
  compressions runs at 485k/s [P] and amortises the PCS. A per-chain statistic and "time to prove a
  million chains" therefore reward different provers. Without a tree, neither rewards recursion.

## 7. Open points

- No recursive verifier (WHIR-class, binary field) has been timed on this machine or on a machine
  with carry-less multiply. Rows 2–3 and 6–7 rest on WHIR Table 5 and the 66 ns `E` product. Measure
  leanVM's `recursion --n 2` verify on the reference machine before fixing `T_V`.
- §5.2 uses a generic C compression and synchronous batching. A double-buffered SIMD service may
  close most of the Flock-class gap. That is worth one more probe if D2 or D4 goes forward.
- The deferral proof-size range (80–850 MB) assumes about half the Merkle bytes are derivable from
  answers. The exact figure depends on the deferred-list format.

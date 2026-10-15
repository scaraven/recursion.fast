# S9 review: feasibility (whole repository, Stage 9)

Reviewer lens: **feasibility.** Can a strong agent produce a ranked entry, can the organiser run
the competition, and do the numbers (build and check times, caps, budgets, kernel costs) hold on
a clean machine? The other two Stage 9 reviewers cover incentives and the trusted base.

- **Scope.** The repository at `0451b32`, all stages committed. The orchestrator's doc-only commit
  `2620a62` (DESIGN §3.3–§12 refolded) landed during the review; section numbers below are those of
  the current `docs/DESIGN.md`.
- **What I did.** Re-ran everything that has a timing claim: a fresh clone, the default build, the
  full CI and the baseline's production harness. I added five probes under `probes/s9/feasibility/`
  (logs in its `logs/`): the fresh-clone driver (`fresh-clone.sh`, `fresh-ci.sh`), the `C_V` size
  model (`cv_model.py`), the decoder budget model (`o11_model.py`), the kernel `K`-product probe
  (`kmul/`) and the compiled hash/`K` benchmark (`compiled-bench/`). No other file was edited.
- **Load.** The machine was shared with the other two Stage 9 reviewers' probes. The load average
  was 1–4 at the starts and peaked at 30 during CI's concurrent phase. Single-run times carry
  about ±10 %.

Findings: `S9F-M1` … `S9F-M7` are majors, `S9F-m1` … `S9F-m8` minors (§7). The verdict is §8.

---

## 1. Fresh-clone reproduction

**Procedure.** `git clone` into `/home/devops/Verified-zkEVM/rf-fresh-check` (deleted afterwards),
following only `CLAUDE.md` and `README.md`. The packages came from the documented symlink to the
shared tree, not from `lake exe cache get` (no downloads). Clean was cloned with
`scripts/setup-clean.sh <local checkout>`. Driver: `probes/s9/feasibility/fresh-clone.sh` and
`fresh-ci.sh`. Timings come from `/usr/bin/time -v` (`logs/fresh/steps.log`, `time-*.txt`,
`out-*.log`).

| # | Step (as documented) | Outcome | Wall (CPU) | Doc or code gap |
|---|---|---|---|---|
| 1 | `git clone` | OK | 0.4 s | — |
| 2 | `scripts/setup-clean.sh /…/recursion.fast/ext/Clean` | OK, verified at `42fe4b26` | 0.2 s | The offline form (a local checkout as the argument) is documented only in the script header and DESIGN §9.3. CLAUDE.md gives the bare command, which needs network. |
| 3 | `mkdir -p .lake && ln -s …/contract/.lake/packages .lake/packages` | OK | 0 s | CLAUDE.md says "a clean clone removes the symlink and runs `lake exe cache get`". A clone has no symlink to remove. `cache get` supplies only Mathlib; CompPoly's 29-module cone and Clean must be **built**, and ArkLib/VCVio/PolyFun are cloned although nothing builds them. No from-scratch time is documented (S9F-m3). |
| 4 | `lake build` (default targets), cold project, packages prebuilt | **OK**, 2,490 jobs | **5 min 05 s** (691 s user, 249 % CPU), peak 9.1 GB | CLAUDE.md quotes only "≈ 40 s warm". The cold critical path is the kernel-evaluated controls: `RecursionNode` 121 s, `Recursion` 75 s, `Compile` 66 s, `CompileFS` 45 s (S9F-m3). |
| 4b | `lake build` again | OK | 3.5 s | — |
| 5 | `scripts/ci.sh /…/riscv-zkvm` | **FAIL at step 2 after 3 s**: `rsync: change_dir "…/RecursionFast/Bridge" failed: No such file or directory (2)`, exit 23 | 3 s | **S9F-M1.** `RecursionFast/Bridge/` is an empty directory. Git does not track it, so it is absent from every clone, and `org-build.sh` rsyncs it under `set -e`. The reference machine's documented one-time setup (`reference-machine.md` §2) fails the same way. |
| 5b | workaround `mkdir -p RecursionFast/Bridge`; `scripts/ci.sh` | **FAIL at step 3**: `olean-manifest: missing packages/Clean/Clean/Air/OrderedChannel.olean` …, "FAIL (12 differences in 35222 entries)". The organiser build itself was OK: **5 min 39 s cold**, 5,042 jobs, with the Clean cone. | 5 min 45 s (1,310 s user) | **S9F-M2.** The committed manifest records four Clean modules that no organiser target builds: `Clean.Air.OrderedChannel`, `Clean.Air.Vm`, `Clean.Examples.FibonacciWithChannels`, `Clean.Gadgets.Addition8.Theorems`. The dev tree's `ext/Clean` holds them from Stage 8's probes. |
| 5c | workaround: build those 4 modules in `.lake/org` (36 s); `olean-manifest.py check` | OK (35,222 files match) | 36 s + 3.8 s | The other 35,210 entries matched **byte for byte from a different absolute path**: `.olean` files are path-independent, which is good news for the manifest design. |
| 5d | `scripts/ci.sh` | **CI OK** | **13 min 29 s** (808 s by CI's clock; 3,022 s user, 444 % CPU), peak 7.0 GB per process | Steps 1–4: 34 s. Phase A: 123 s. Phase B: 286 s (critical path the toy harness; comparator **202.6 s**). Timed smoke benchmark with the rejections: 239 s (benchmark **217 s**). Step 11: **121 s**, because the clone's root tree builds `RecursionFastClean` cold (11 s warm in the dev tree). Step 12: 4 s. DESIGN §7.4 quotes 11 min 47 s, a warm dev-tree figure. |
| 6 | `HARNESS=1 ORG=… MANIFEST=… submissions/baseline/scripts/check.sh` | **FAIL** (`harness: no comparator at …/rf-fresh-check/tools/comparator (set COMPARATOR_HOME)`) | 1 min 29 s | `harness.sh` defaults `COMPARATOR_HOME` to `$REPO/tools/comparator`, which does not exist. `ci.sh` instead exports this machine's paths, so CI passes and the baseline check does not (S9F-m2). |
| 6b | the same, with `COMPARATOR_HOME`/`COMPARATOR_NANODA` exported as `ci.sh` sets them | **CHECK OK**; the production harness ACCEPTs | **6 min 02 s** (400 s user), 3.5 GB | Candidate build 19.9 s; `leanchecker` 23.8 s; harness **275 s** (comparator 199.3 s, closure 23,836 constants, gate PASS) |
| 7 | `olean-manifest.py gen` on the clone's organiser build | identical to the committed file (0 diff lines, after workaround 5c) | 3.4 s | — |

**Undocumented prerequisites.** None of these is described in the repository:

- `ci.sh` and `harness.sh` default `COMPARATOR_HOME` and `COMPARATOR_NANODA` to this machine's
  read-only checkouts outside the repository:
  - the comparator at `d03acab`, whose origin is a probe directory of the v0.3 workspace;
  - its `lean4export` package;
  - `nanoda_lib` at `3a24072` (`ammkrn/nanoda_lib`, built with cargo).

  There is no URL, pin or build command for any of them. Worse, the two scripts disagree:
  `harness.sh` alone defaults to `$REPO/tools/comparator`, which does not exist, so the baseline's
  `HARNESS=1 check.sh` fails out of the box (row 6) while CI passes.
- `bubblewrap` and a delegated cgroup v2 user manager (the runner refuses to run without them).
- `riscv64-unknown-elf-*` for the baseline image.
- Python ≥ 3.11 (`tomllib` in `harness/mk-tree.py`).

All of these are S9F-m2.

**Bottom line.** Reaching green CI took two code or manifest workarounds and about 25 min of wall
time, with the packages prebuilt. The baseline's production check needed a third (exporting the
comparator paths). The time breaks down as: default build 5 min, cold organiser
build 5.7 min, CI 13.5 min, workarounds 1 min. CI does not pass on a fresh clone as committed. On
a clean reference machine it would also fail step 3 for a second, larger reason (§4.6, S9F-M2).

---

## 2. The organiser's cost per submission (DESIGN §7.4)

Measured runs come from the fresh clone (`rf-fresh-check/logs/S6b/ci/`, `logs/S7/`, copied to
`probes/s9/feasibility/logs/fresh/`).

| Submission | Comparator (Lean kernel + nanoda) | Gate (build in tree 2, rules 1–9) | Badge build | Indexing | Benchmark run | Total |
|---|---|---|---|---|---|---|
| (a) baseline `P_triv` (board L claim, listed unranked: no badge, no benchmark) | **199.3 s**, 3.5 GB (closure 23,836 constants) | ≈ 76 s (sandboxed build in a second fresh tree, binding, manifest checks, rules 1–9) | — | — | — | **275 s ≈ 4.6 min** (6 min 02 s with `check.sh`'s own build, axioms, `leanchecker` and negative claims) |
| (b) `cmpToy` smoke (`audit/` toy through the harness; then the smoke protocol through the runner) | 202.6 s, 3.5 GB (23,835 constants in the certificate's closure) | ≈ 40 s | ≈ 40 s (two sandboxed builds ≈ 37 s each in CI step 10) | 0.1–0.6 s per layout | **217 s**: 3 runs × (96 leaves + 63 steps), 100 DoS tapes; 0.26 s per prover + verify pair, of which the sandbox and cgroup are ≈ 0.07 s per process | ≈ 286 s harness + 217 s benchmark ≈ **8.5 min** |
| (c) projected real FRI/WHIR-class board-R entry | 2 × the solution build (comparator tree, gate tree; ≤ 1 h each by the cap) + kernel replay of a closure of 80k–150k constants (≈ 206 s × closure / 23.8k ≈ 12–22 min if linear) | (inside the 2nd build) | ≈ 1–2 min (more if its badge root imports a large Mathlib slice; the Mathlib objects are prebuilt) | **≥ 2^(k+1.5) compiled BLAKE2s compressions per layout, 3–4 layouts** (§4.2): 13 min at k = 24 in the best case; **2.3–9 h at k = 27** | ≤ 6 h (`eval_s`), and the caps make that bound bind (§4.4) | **≈ 3–9 h of organiser machine time per evaluated entry**, and the reference machine must be idle for the benchmark |

**Kernel replay of a real certificate.** The S3/S5 data:

- an honest `NARG` run of `cmpToy` (15 compressions) costs 35–39 s of kernel CPU;
- a BLAKE2s compression costs ≈ 2.2 s;
- a `K` product costs ≈ 40 ms (§4.5 re-measures it at ≈ 50 ms).

A certificate never needs to evaluate `NARG` on a real tape:

- `live` comes from `live_of_secure` and a tape-size bound;
- `sound`, `complete` and `Secure` are general theorems;
- `fits` is `decide` on the `C` literal, < 1 s for `L_chain(16)`.

Its replay cost is therefore its closure size and proof style. A proof-only certificate replays in
tens of minutes under both kernels, and the 2 h harness cap is realistic **for it**.

What breaks the cap is any kernel evaluation at real scale. One `NARG` run of a 10k-compression
proof is ≈ 6 h per kernel. It is paid three times (elaboration, the Lean kernel and nanoda), and
the solution is built twice. A submitter's own kernel-checked controls must therefore stay on toy
instances of ≤ ~50 compressions or ≤ ~5,000 `K` products (S9F-m4).

**The caps contradict each other.** The harness builds the solution twice, once in the
comparator's tree and once in the gate's. A submission that uses its 1 h `lake build` cap
therefore needs ≥ 2 h of harness before the first kernel replay, against a harness cap of 2 h.
Neither cap is enforced: `harness.sh` runs the comparator, the gate-tree build and the badge build
with no `timeout` and no memory cgroup (S9F-m1).

---

## 3. The submitter's path to the first ranked (board R) entry

What exists that helps:

- `Library/Compile.lean`: `narg_complete*`, `narg_local`, `narg_oversize`;
- `Library/Recursion.lean`: `aggOK_iff`, `aggOK_sat_of_secure`, `live_of_secure`;
- `Library/Extractor.lean`: refinement, fuel and step lemmas;
- `Library/Layout.lean`: `Gadget.holds_iff`, `relBelow_iff`, `rel_trim_iff`;
- `Library/Field.lean`: `Field K`, `Field E`, `CharP K 2`;
- the Clean bridge (`toLayout_rel_iff`, `StatementPerm`);
- Stage 6a's G chip, kernel-checked on one G-call only, with no general theorem;
- the Python references: `probes/s3/compile_ref.py` (80 lines) for the tape grammar, and
  `gen-chain-layout.py`/`check-chain.py` for `L_chain`.

What does **not** help, contrary to the docs:

- `Library/RbrSound.lean`'s `rbrKS_of_rbr` is for unbounded extractors. `Security.lean`'s header
  says that the collapse "does not apply" to the submitted image. `chain_extracts` and
  `no_bad_imp_false` remain useful.
- **There is no ArkLib bridge.** `RecursionFast/Bridge/` is empty and `Bridge.lean` is a one-line
  comment, although DESIGN §4 and §10 say that `Bridge/ArkLib.lean` "carries over unchanged".
- **No ArkLib module is importable**: gate rule 6's allowlist has 0 of them, and CompPoly only its
  29-module `BF64` cone.
- ArkLib at the pin has sorries in exactly the parts a submitter needs: `Fri` 4, `BatchedFri` 6,
  `Stir` 4, `Sumcheck` 14, `Binius` 32, `ProximityGap` 22. WHIR is absent. Only `BerlekampWelch`
  (1,121 lines) is sorry-free.
- The v0.3 bridge was contract → ArkLib (`RbrKS.toArk`), the wrong direction for reusing ArkLib's
  proofs (S9F-M6).

| # | Item | Needs | Help available | Lines (est.) | Person-weeks |
|---|---|---|---|---|---|
| 1 | IOP over `Layout` (spec) | Uniform CCS per chip with the view (row, next, constants). A **bus argument without LogUp**: in char 2 the fractional sum counts multiplicities mod 2, so a lookup received twice and never sent balances; product or GKR-product arguments work. **Division-free**, because `PerfectComplete` quantifies over *every* challenge vector. A holographic index sized for the worst admissible layout (§4.2). | `Layout`, `Codec` (toy only) | 1.5–3k Lean | 3–5 |
| 2 | `Secure`: perfect completeness | Every layout, witness and challenge | `narg_complete` is at the compile level only | 2–4k | 3–6 |
| 3 | `Secure`: RBR-KS, `ε c ≤ 2^-128` **per round** | KSF for sumcheck, the product argument, and RS proximity with FRI/BaseFold/WHIR folding. All queries sit in one round (2^-128 per round means no grinding and no splitting), so 141–189 queries in the unique-decoding regime | `chain_extracts`, `no_bad_imp_false`; Mathlib Schwartz–Zippel | 15–30k | **25–50** |
| 4 | Extractor image | **An RS decoder in RV64 + Zbc machine code**, proved against the vendored `Rv64` semantics, within `B(k)` (§4.3). The KSF's bad-challenge counting needs the decoder's output to be the true decoding, so decoder correctness is a theorem about `run`. | `Library/Extractor.lean`; the baseline's 8-instruction image; ArkLib `BerlekampWelch` (math, not importable) | 1–3k instructions + 8–20k Lean | **10–20** |
| 5 | `cfg` | blake2s, arity 2 or 4 (arity 16 costs 2× the compressions, §4.1) | — | 5 | 0 |
| 6 | Native prover (Rust) | The tape grammar; witness generation for `L_chain` from `s` and for `C_V` from two child tapes (a NARG trace); an additive FFT over GF(2^64) with `pclmulqdq`; sumcheck and product provers; 2^27–2^28 cells per node step in ≲ 100 s (§4.4) | `compile_ref.py`, `gen-chain-layout.py`, `toy_prover.py` | 8–15k Rust | 8–14 |
| 7 | `C_V` generator and `decode` | BLAKE2s compression gadget (multi-block, counters, finalisation), Merkle `climb`, sponge `absorb`/`squeeze`, bytes↔`K`/`E` packing, challenge decoding, the query program's arithmetic over `E`, `nodeStmt`. **≈ 2^26.3–2^29 cells** (§4.1). | S6a G chip (9,225 cells per compression); leanerVM's BLAKE2s table (a 60-cell *interface* row with **no compression constraint**, S8-RESULT); `toLayout` | 3–6k | 6–10 |
| 8 | `sound` and `complete` against `NARG` | A circuit-correctness proof for every input, including adversarial tapes and every adaptive query path, under keys of any value (`complete` ranges over all accepted nodes) | `toLayout_rel_iff`, Clean `FormalCircuit` (its bus theorems assume `ringChar ≠ 2`, §9.2), `aggOK_iff` | 15–30k | **20–40** |
| 9 | `live` | `live_of_secure` + a bound that the honest tape fits `tapeCap` | `Library/Recursion.lean` | 0.3–1k | 1–2 |
| 10 | Packaging | Claim, digests, challenge, a ≤ 1 h build, harness dry runs, tuning to the step budget | harness, smoke test | — | 2–4 |
| | **Total** | | | **≈ 45–110k Lean + 10–20k Rust/asm** | **≈ 80–150 person-weeks** |

**The two or three library assets that would cut this most** (for §12):

1. **A verified "NARG gadget kit"** (cuts items 7–8 by roughly 60–70 %). A BLAKE2s compression
   chip near the byte-lookup floor (≈ 5.3k cells per compression, §4.1), with general `sound`/
   `complete` theorems against `Contract/Hash/Blake2s.compress`, plus multi-block hashing, Merkle
   `climb`, sponge and challenge-decoding gadgets proved against `Compile.lean`. That is a
   parametric `C_NARG(shapes)` with a hole for the query program. Sources: leanerVM's compression
   proof (Flock), Stage 6a's G chip, Clean's `FormalCircuit`.

   **Together with it,** decide whether to add an arithmetisation-friendly hash to the `Cfg` menu
   (S9F-M3). It is the only lever that moves the fixed point below `k = 27`.
2. **A verified RS decoder image over `K`** (cuts item 4 to glue). Unique decoding by syndromes,
   Berlekamp–Massey and Forney in RV64 + Zbc, with a proved step bound `≈ 1.5·N²·(10–14)` and the
   theorem "δ-close received word ⇒ the image outputs the message". Optionally Koetter GS at
   multiplicity ≤ 2.
3. **An importable IOP-soundness library** (cuts item 3 by about half). Either allowlist a curated,
   sorry-free ArkLib slice with a bridge in the **ArkLib → contract** direction, or write in
   `Library/`: sumcheck RBR-KS over `E`, the char-2 product (bus) argument, and RS proximity for
   FRI/BaseFold folding in the unique-decoding regime with explicit `ε ≤ 2^-128` accounting. O-7
   (a funded reference entry) is items 1–3 plus a prover.

Without these the first ranked R entry is a **multi-person-year** project. Even with them it is a
team-quarter, and it fits only at `k = 27–28` (§4.1).

---

## 4. Numbers check

### 4.1 `C_V` cells against `2^k`: is the fixed point reachable?

**Model.** `probes/s9/feasibility/cv_model.py`; logs `logs/cv_model.log`, `cv_model_whir.log` and
`cv_model_optimistic.log`. It counts the BLAKE2s compressions of one `NARG` run under the
contract's tape grammar:

- no path batching; a repeated query is opened again;
- absorb is `H(0x00‖s‖m)`, so a 32-byte root costs **2** compressions (65 bytes);
- squeeze is `H(0x01‖s)`; the key digest `D` hashes `8·vkLen + 32` bytes.

The protocol modelled is FRI/BaseFold-like or WHIR-like over `K`:

- layer-0 trees of witness size and of index size;
- `E`-valued folding layers;
- one query round reaching 2^-128 (unique-decoding radius `(1-ρ)/2`, or Johnson `1-√ρ-0.05`);
- `3k` sumcheck rounds.

`C_V` is 2 `NARG` runs + `H(x₁‖x₂)` + 2 M cells of non-hash arithmetic, the `add8` table and
packing. Three gadget costs are compared:

- **9,225 cells per compression**: Stage 6a's chip as built;
- **5,337**: the S6a-A7 floor for byte-lookup additions, 58 cells per G-call × 80 + 697 of state;
- **60**: leanerVM's table row. That row is not a compression; it is shown only to correct the
  "60 cells/row" premise.

| Design (k = 24) | Compressions per `NARG` | Tape | `log₂ C_V` at 9,225 | at 5,337 | Least k ≤ 28 with `C_V ≤ 2^k` |
|---|---:|---:|---:|---:|---|
| FRI, ρ = 1/4, unique, A = 2, f = 4 (189 queries) | 34,011 | 1,259 KiB | 29.23 | 28.44 | **none** (and tape > 1 MiB) |
| FRI, ρ = 1/16, Johnson, A = 2, f = 4 (74 queries) | 15,380 | 568 KiB | 28.09 | 27.31 | 9,225: none; 5,337: **28** |
| WHIR-like, ρ = 1/16, unique (141, 130, 129, … queries) | 30,590 | 1,083 KiB | 29.08 | 28.29 | **none** |
| WHIR-like, ρ = 1/16, Johnson, Merkle-cap emulation (2^6 sub-oracles) | 10,854 | 375 KiB | 27.59 | 26.81 | **28** (both) |
| the same, 1 witness + 1 index tree (most optimistic) | 7,470 | 260 KiB | 27.06 | 26.29 | 9,225: **28**; 5,337: **27** |
| the orchestrator's "≈ 10k hashes" | 10,000 | — | 27.48 | 26.70 | 9,225: **28**; 5,337: **27** |

**Reading.**

- **It does not fit `2^24` or `2^26` in any configuration.** Even in the most optimistic row:
  - fitting `2^24` would need ≤ ~1,000 cells per compression, a fifth of the floor;
  - fitting `2^26` would need ≤ ~3,900, below the floor's 5,337, i.e. ≤ ~40 cells per G-call
    against 58.

  The floor binds any byte-lookup arithmetisation (S6a-A7). With BLAKE2s as
  the only menu hash, **the fixed point exists only at `k = 27–28`**, against `k_range ≤ 28`.
- It needs a WHIR-class protocol (or FRI at ρ = 1/16) in the Johnson regime. **Unique-decoding
  designs have no fixed point at any k ≤ 28.** It also needs either the floor gadget or the most
  optimistic tree count.
- Consequences:
  - each node proof is a 2^27–2^28-cell statement;
  - the index oracle is ≥ 2^31 elements (§4.2);
  - Johnson-regime extraction is needed, and `B(k)` admits it only at GS multiplicity ≤ 2 (§4.3).

This is S9F-M3. Merkle-cap emulation (splitting an oracle into `2^c` sub-oracles, each its own
round) is legal under the grammar and saves 15–21 %. Arity 4 equals arity 2 in compressions; arity
16 costs 2× (each 512-byte level is 8 compressions).

### 4.2 The index oracle cap against `L_chain(2^10)`, and what indexing costs

**`L_chain(2^10)` against the cap.**

| Quantity | Value |
|---|---|
| matrix entries | 1,163 |
| fixed cells | 786,464 |
| `eLayout` (S7 `tape-size.log`) | 792,851 elements, 2^19.6 |
| index-oracle cap `2^(k+8)` at k = 24 | 2^32 |

So `L_chain(2^10)` uses **0.02 % of the cap**, and the cap is not what binds.

**What binds is that `idxShape` is a constant of `Protocol k`.** A protocol that is complete for
every admissible layout must commit, for every layout, an index oracle of size ≥ the information
content of the worst admissible layout:

- matrix entries: ≤ 2^(k+4), each ≈ 1.4 `K`-elements (row 8 bits, column 11 bits, matrix 6 bits,
  value 64 bits);
- fixed cells: ≤ 2^(k−4).

That is ≥ ~2^(k+4.5) elements before any encoding. A sparse (row, col, val) encoding at RS rate ρ
fits `2^(k+8)` only for ρ ≥ ~3/16, so a holographic index oracle must use rate ≥ 1/4 even when the
witness uses 1/16.

**Hashing.** The trusted `commit` hashes every leaf of `idxShape`, padding included, and the
executed indexer is the Lean-compiled `index` (one thread). It therefore performs, whatever the
layout:

- ≥ 8·2^(k+4.5)/64 = **2^(k+1.5) compressions** per layout at rate 1;
- **2^(k+3.5)** at rate 1/4.

**Encoding.** An interleaved code whose zero rows are skipped can make the `IDX` encoding scale
with the *actual* layout. Even so, at the measured compiled `K` product (26.9 µs), additive-FFT
encoding of `L_chain`'s 786k fixed cells alone at rate 1/4 (768 rows, 2^10 → 2^12) is ≈ 2.3 × 10^7
products, ≈ 8–10 min per layout, unless that codeword is precomputed as a literal. O-9 therefore
applies to the indexer too. A
precomputed array of 2^(k+6.5) boxed `K` values needs ≈ 36 GB at k = 24 (`K` is `BitVec 64`, a
`Nat`, heap-allocated above 2^63).

**Measured** (probe `probes/s9/feasibility/compiled-bench/`, an executable against the
organiser package, `logs/compiled-bench.log`):

- compiled `blake2s256`: **5.3–7.0 µs per compression** (2^16 and 2^20-byte inputs; 64-byte
  chains);
- compiled `K` multiply-add: **26.9 µs**, confirming O-9.

The runner indexes every leaf-board size plus `C_V`: three layouts at k = 24, four at k ≥ 26
(`run-benchmark.py`, step 2). Hashing alone, at 5.5 µs per compression:

| k | compressions per layout, ρ_idx = 1 / 1/4 | per layout | all layouts per evaluation | budget |
|---|---|---:|---:|---|
| 24 | 4.7 × 10^7 / 1.9 × 10^8 | 4.4 / 17 min | **13 / 52 min** (3 layouts) | 1 h |
| 26 | 1.9 × 10^8 / 7.6 × 10^8 | 17 / 70 min | **1.2 / 4.6 h** (4) | 1 h |
| 27 | 3.8 × 10^8 / 1.5 × 10^9 | 35 min / 2.3 h | **2.3 / 9.3 h** (4) | 1 h |
| 28 | 7.6 × 10^8 / 3.0 × 10^9 | 70 min / 4.6 h | **4.6 / 18.6 h** (4) | 1 h |

This is S9F-M4: at the fixed point (§4.1, k = 27–28) indexing exceeds its 1 h budget by 2–18×,
even before the encoding and the memory cap. Real layouts have ≈ 10^3–10^4 entries, so lowering
the entries cap from `2^(k+4)` to `2^(k−4)` (or a constant 2^20) removes the problem without
touching any security statement. The index would then be dominated by the fixed cells, at most
2^(k−4).

### 4.3 The extractor budget against a Guruswami–Sudan decoder (O-11)

**CompPoly's GS cannot be the extractor as it stands.**

- It is Lean code over KoalaBear (an NTT and `fastKoalaBear…` backends).
- Its interpolation is dense Gaussian elimination or Lee–O'Sullivan/Mulders–Storjohann, with
  Roth–Ruckenstein/Alekhnovich root finding.
- The extractor must be **RV64 machine code** of ≤ 1 MiB over `K`.

What fits is a question about the algorithm's operation count. Model:
`probes/s9/feasibility/o11_model.py`, `logs/o11_model.log`.

- Steps per `K` multiply-add: S4-M2's 10, and 14 for a straight RV64 + Zbc loop of 2 `ld`,
  `clmul`, `clmulh`, two folds by `0x1B`, 3 xors and 3 loop instructions.
- `N = 2^(k+r)`, with r = log₂(1/ρ).
- The slack `log₂(B(k)/steps)` is independent of `k`, since both are `2^(2k+c)`.

| ρ | Decoder | `log₂ steps − 2k` (10 / 14 steps per op) | Fits `B(k) = 2^(2k+16)`? | Radius | Queries for 2^-128 |
|---|---|---|---|---|---|
| 1/4 | unique (syndromes + BM + Forney, ≈ 1.5 N²) | 7.9 / 8.4 | yes, 2^7.6 slack | 0.375 | 189 |
| 1/4 | GS, Koetter, multiplicity m = 5 (C = 15N, ≈ C² ops) | 15.1 / 15.6 | yes, barely | 0.452 | 148 |
| 1/4 | GS m = 6 | 16.1 / 16.6 | **no** | 0.460 | 145 |
| 1/16 | unique | 11.9 / 12.4 | yes, 2^3.6 slack | 0.469 | 141 |
| 1/16 | GS m = 2 (C = 3N) | 14.5 / 15.0 | yes, 2^1 slack | 0.694 | 75 |
| 1/16 | GS m = 3 | 16.5 / 17.0 | **no** | 0.711 | 72 |

**Answer to O-11.** `B(k)` admits the quadratic GS (Koetter interpolation) at ρ = 1/16 only up to
multiplicity 2 (radius 0.69, ≈ 75 queries). That is enough for §4.1's best configuration, with
1–2 bits of slack.

**The measurement still needed** is the exact Koetter constant and the instruction count of the
actual RV64 inner loop. Run it on the contract machine (`Machine.run` compiled, `#eval`) at k = 20,
with N = 2^24 and m = 2, against `B(20) = 2^56`. **The real cost is not the budget but the
proof**: item 4 of §3.

### 4.4 Budgets and caps of the benchmark run (§6.3, §6.5)

The runner is sequential, each step "with all cores", and `eval_s` = 6 h = 21,600 s includes
indexing (`run-benchmark.py`: `t0` at start). One evaluation is:

- 3 runs × (96 leaves: 64 tree chains + 16 of `2^8` + 16 of `2^12` at k ≥ 26);
- 3 runs × 63 tree steps;
- 1,000 DoS `verify` runs;
- indexing.

The arithmetic follows.

- **Leaves.** At the `leaf_s` cap: 288 × 120 s = 34,560 s > 21,600 s. Leaves must average
  **≤ 74 s**.
- **Steps.** With 10 s leaves and 1 h of indexing:
  (21,600 − 2,880 − 200 − 3,600)/189 ≈ **79 s per step** (prover + verify). The stated `step_s` is
  600 s: 189 × 600 s = 31.5 h.

So the binding step budget is **≈ 80–100 s**, not 600 s, for a 2^27–2^28-cell node proof with no
GPU (S9F-M5). On a reference machine with `pclmulqdq` that is plausible for a well-engineered
binary-field prover. **On this VM it is not**: no carry-less multiply (§5).

### 4.5 Kernel cost of `decide +kernel` on `K` and its implications

- **Measured here:** **≈ 50 ms per product** (`probes/s9/feasibility/kmul/`, `logs/kmul.log`:
  random products, each its own `decide +kernel` theorem). With 50 products the file takes 5.03 s
  wall, against 2.51 s for the imports alone; with 10 products, 2.98 s. That is 47–50 ms wall and
  57 ms user per product, about 25 % above DESIGN §7.2's 40 ms.
- **Controls.** The default build's critical path is already the kernel-evaluated controls, ≈ 5 min
  cold (§1, row 4). Each new `cmpToy`-scale `NARG` control adds ≈ 35–40 s of CPU three times over
  (build, Lean kernel, nanoda, where it is in a certified closure). Each G row adds ≈ 1.8 s with
  `mul_fast`.
- **Rule for `Controls/` growth.** Budget kernel controls by compressions (2.2 s) and `K` products
  (≈ 50 ms), not by theorems. Keep the default build under ~10 min cold.
- **For submitters (S9F-m4).** Positive controls must use toy instances. A sumcheck of 2^10 `E`
  products is ≈ 9,000 `K` products ≈ 7.5 min per kernel, ≈ 22 min across elaboration and both kernels.

### 4.6 The 1 h `lake build` cap and large Mathlib imports; manifest regeneration

**The build cap and large imports.**

- `import Mathlib` costs 11–12 s and 6.9 GB per Lean process (`probes/clean-build/RESULT.md`,
  re-used). Mathlib's `.olean`s and (S6b-A18) objects are prebuilt, so importing a large slice
  costs only load time.
- A 100-module submission importing all of Mathlib pays ≈ 20 CPU-min of loading. At Lake's
  parallelism (≈ 13 concurrent processes here) the RSS sums to ≈ 90 GB. The olean pages are
  shared mmaps (≈ 7 GB physical), so a cgroup `MemoryMax` would see far less, but a per-process
  or summed-RSS limit would not. How the 48 GB build cap is to be measured is unspecified, and the
  cap is unenforced (S9F-m1).
- The 1 h cap itself is realistic for a proof-only entry of 50–100k lines: ArkLib-scale libraries
  build in tens of minutes on 32 cores. It is the harness-cap arithmetic of §2 that does not add
  up.

**Manifest regeneration.**

- `olean-manifest.py check` takes 3.8 s (35,222 files). `gen` takes the same plus a **clean**
  organiser build: 5 min 39 s cold here, or ≈ 30 s warm after a trusted change.
- It is error-prone in two ways, both observed:
  1. **It hashes every `.olean` in each package directory, not the organiser's closure** (S9F-M2).
     Of the committed entries, **710 are outside the import closure that the gate trusts**:
     ArkLib 136, VCVio 357, PolyFun 78, CompPoly 108, Clean 13, mathlib 18 (`Cache.*`). They are
     whatever the shared tree accumulated from v0.2/v0.3 and Stage 8's probes.

     The fresh clone failed on 12 of them (Clean). A clean reference machine (`cache get`, then
     the organiser build) would also miss ArkLib's, VCVio's, PolyFun's and CompPoly's 679. The 18
     `Cache.*` files exist wherever `cache get` has run, and one Clean file is built anyway. Conversely, any later build into the
     shared tree adds "extra" files and turns CI red here.
  2. **Trusted changes require regeneration on the machine of record.** A regeneration on a
     developer machine bakes that machine's package state into the committed file.

---

## 5. Machine (O-6)

**What this VM lacks.**

- It is a QEMU "Virtual CPU version 2.5+" with 32 vCPUs and 62 GB.
- Its flags have **no `pclmulqdq`, `vpclmulqdq` or `gfni`** (checked:
  `grep -o 'pclmul\|vpclmul\|gfni' /proc/cpuinfo` is empty). It does have AVX-512F/BW/DQ/VL.
- A native prover that uses carry-less-multiply intrinsics gets `SIGILL` here. A portable
  software `clmul` is roughly an order of magnitude slower (an estimate, not measured here), so no
  competitive binary-field prover can be developed or timed on it. The compiled Lean `K` product
  takes 26.9 µs here (§4.2).
- It has no cpufreq control and a virtual disk.
- It is shared: load 1–30 during this review, 4 during S6b's noise measurement.
- Cgroup v2 delegation and bubblewrap work: CI step 10 passes.

**Proposed reference machine.**

- **Hardware.**
  - Bare metal, x86-64, **32 physical cores**, AVX-512 with **VPCLMULQDQ and GFNI**: e.g. AMD EPYC
    9355P (Zen 5) or 9354P (Zen 4), or Intel Xeon 6 / Sapphire Rapids-class with ≥ 32 P-cores.
  - **SMT off**, **boost off** (a fixed base clock, governor `performance`), C-states limited to
    C1.
  - 128 GB DDR5 on all channels, so the 48 GB step cap leaves room for the page cache.
  - Local NVMe (≥ 2 TB) for step directories and the `.lake` trees. No GPU.
- **Software.**
  - Linux LTS, kernel and glibc pinned per season; cgroup v2 with user delegation; bubblewrap.
  - Lean v4.34.1, Rust stable pinned, Python ≥ 3.11.
  - THP `madvise`, swap off, ASLR on.
  - No other tenants. `irqbalance` stopped during evaluations; the network down.
- **Developer access.** Submitters get the same SKU class, or at least the same ISA extensions,
  for development.

**Noise-measurement protocol** (to justify, or replace, the 3 % margin):

1. **Calibration workloads** at three lengths, ~1 s, ~10 s and ~80 s (the real step budget,
   §4.4). Use a fixed native reference prover: a BLAKE2s chain plus an additive-FFT RS commit of
   2^22, 2^25 and 2^27 elements with Merkle hashing. Run through the runner's sandbox and cgroup.
2. **Run conditions.** For each, 30 repetitions per session, on 5 sessions on different days.
   Before each session: drop caches, then one warm-up run; record `turbostat` frequency and
   temperature, load average (must be < 0.1 at start) and kernel version.
3. **Statistics.**
   - Within a session: the median of 31 × 3 (the score's statistic, by resampling the 30 runs).
   - Across sessions: the spread `(max − min)/min` of that statistic, and the 95th percentile of
     `|S_a/S_b − 1|` over session pairs.
4. **Margin rule.** Set the record margin to ≥ 2 × that 95th percentile, and publish it per
   season. If it exceeds 3 %, keep the larger value.
5. **Close calls.** A challenger within 2 × margin of the record is re-run interleaved with the
   standing entry (ABABABAB, 4 each). The median ratio decides.
6. **Re-runs.** Repeat after any firmware, kernel or toolchain change. Store the raw per-step times
   with the hardware id (`harness/reference-machine.md` §1).

---

## 6. What the stage RESULTs' timing claims look like on a clean run

| Claim (where) | Claimed | Measured (fresh clone) |
|---|---|---|
| default `lake build` (CLAUDE.md) | ≈ 40 s warm | 3.5 s warm; **5 min 05 s cold** (packages prebuilt) |
| organiser build cold (`reference-machine.md` §2, S7) | ≈ 5 min; 5 min 46 s | 5 min 39 s (with Clean) |
| CI (DESIGN §7.4, S6b fix pass) | 11 min 47 s | **13 min 29 s** (step 11 cold 121 s vs 11 s), after two workarounds |
| toy comparator (S6b) | 207 s | 202.6 s |
| smoke benchmark (S6b) | 218 s | 217 s |
| baseline production harness (S7) | 293–298 s | 275 s (comparator 199.3 s), after setting `COMPARATOR_HOME` |
| `RecursionFastClean` (DESIGN §9.3) | 3 min 34 s cold | Clean cone inside the org build; our 6 modules in the root tree 121 s |

---

## 7. Findings

### Majors

**S9F-M1 — CI and the organiser build fail on every fresh clone (`RecursionFast/Bridge/` is untracked).**

- **What fails.** `scripts/org-build.sh` runs
  `rsync -a --delete "$HERE/RecursionFast/$d/" …` for `d ∈ {…, Bridge, …}` under `set -e`. The
  directory is empty, so git never checks it out. CI step 2 exits 23 after 3 s. The reference
  machine's documented setup (`reference-machine.md` §2) and `scripts/harness.sh`, which needs
  `--org`, fail the same way.
- **Fix (code).** In `org-build.sh`:
  `for d in …; do [[ -d "$HERE/RecursionFast/$d" ]] || { rm -rf "$DEST/RecursionFast/$d"; continue; }`.
  Alternatively, drop `Bridge` from the list while it is a stub, or commit a real
  `Bridge/ArkLib.lean`.
- **Fix (CI).** Add a fresh-clone job (`git clone` into a temporary directory, then `ci.sh`), so
  this class of bug cannot recur.

**S9F-M2 — The committed `.olean` manifest is machine state, not the organiser's trusted closure.**

- **The defect.** `olean-manifest.py` hashes every `.olean` in each package's build directory. 710
  of the 35,222 entries are modules outside the import closure that the gate trusts (allowlist ∪
  frontend). Nothing in the organiser build produces 691 of them; the other 19 are `Cache.*`
  from `lake exe cache` and one Clean file.
- **Observed.** In a fresh clone, step 3 fails on 4 Clean modules (12 files).
- **Predicted.** A clean reference machine would also miss ArkLib's 136, VCVio's 357, PolyFun's 78
  and CompPoly's 108. Any later build into the shared tree adds "extra" files and fails CI.
- **Fix (code).** Scope `scope()` to the trusted closure: the modules of `import-allowlist.txt` ∪
  `import-frontend.txt` ∪ the project prefixes ∪ `core/`. Keep the "extra file" check only *inside*
  those modules' directories, e.g. a new `Mathlib/Evil.olean` under a trusted directory. A module
  outside the allowlist cannot be imported (gate rule 6), so it needs no hash.
- **Fix (docs).** Document that the manifest is regenerated on the machine of record after its
  clean build (`reference-machine.md` §2).

**S9F-M3 — With BLAKE2s as the only hash, the recursion fixed point exists only at `k = 27–28`, the top of `k_range`.**

- **The numbers.** By §4.1's model, `C_V` is ≥ 2^26.3 cells in the most optimistic configuration
  and 2^27–2^29 in ordinary ones. Unique-decoding FRI or WHIR has no fixed point ≤ 28 at all. No
  byte-lookup BLAKE2s gadget can bring it to 2^26 (that needs ≤ 40 cells per G-call against the
  58 floor).
- **A false premise.** The "60 cells/row" of leanerVM's table is a memory/bytecode interface row
  with no compression constraint (S8-RESULT). It is not a per-hash cost.
- **Not acknowledged.** DESIGN §5.2 and §7.3 describe the fixed point as the "whole game" but do
  not say that it sits at the edge of the range.
- **Fix (decision; DESIGN §3.2 and §12).** Either:
  - (a) add an arithmetisation-friendly hash with a Lean spec to the `Cfg` menu: a permutation
    whose rounds are low-degree over GF(2^64), expected (not measured here) to cost one to two
    orders of magnitude fewer cells than BLAKE2s's 5.3–9.2k. It is the only lever that moves `k*`
    down; or
  - (b) widen `k_range` to ≤ 30 and re-derive every `2^(k+c)` cap; or both.
- **Fix (docs).** In any case, state the estimate (`k* ≈ 27–28`, needing Johnson-regime WHIR and a
  ≈ 5.3k-cell compression gadget) in DESIGN §5.2 and §7.3, and add an O-item for the gadget.

**S9F-M4 — Indexing cost is fixed by the worst admissible layout, not by the benchmark's, and exceeds the 1 h budget near the fixed point.**

- **The cause.** `idxShape` is a constant of `Protocol k`, and `relK k` admits 2^(k+4) matrix
  entries and 2^(k−4) fixed cells. A complete holographic protocol therefore commits
  ≥ ~2^(k+4.5) elements for **every** layout.
- **The cost.** The trusted `commit` hashes every leaf, so each indexing costs ≥ 2^(k+1.5)
  Lean-compiled compressions plus the compiled `IDX` encoding. Measured at 5.3–7.0 µs per
  compression: 13–52 min per evaluation at k = 24, and **2.3–9.3 h at k = 27** against the 1 h
  budget (§4.2). The compiled `K` multiply-add is 26.9 µs, so a `K`-linear encoding of even
  `L_chain`'s fixed table costs ≈ 8 min.
- **Fix (contract, no security statement changes).** Lower the entries cap to `2^(k−4)` or a
  constant such as 2^20 (`L_chain` uses 1,163). Or let `idxShape` depend on a declared size class
  of `L`. Or (organiser code) provide a `@[csimp]`-proved `commit` that hashes an all-zero subtree
  once per height.
- **Fix (docs).** State the indexing cost model in DESIGN §6.3, step 2.

**S9F-M5 — The benchmark's caps are mutually unreachable: the real step budget is ≈ 80–100 s, not 600 s, and the real leaf budget ≤ 74 s, not 120 s.**

- **The cause.** A sequential runner with `eval_s = 6 h` containing 288 leaf runs, 189 step runs,
  1,000 DoS verifies and up to 1 h of indexing (§4.4).
- **The effect.** An entry that honours `leaf_s` and `step_s` can still be rejected for "the
  evaluation exceeded its budget".
- **Fix (decision).** Choose one:
  - derive and publish budgets that fit `eval_s`, e.g. `leaf_s` = 20 s, `step_s` = 70 s and
    `index_total_s` = 30 min (3 × (96·20 + 63·70) + 200 + 1,800 = 20,990 s ≤ 21,600 s);
  - raise `eval_s` to ≥ 3 × (96·`leaf_s` + 63·`step_s`) + `index_total_s`;
  - run 1 repeat for scoring plus 2 only for records;
  - shrink the tree (e.g. 16 leaves).
- **Fix (code).** Make `run-benchmark.py` reject a config whose budgets cannot fit `eval_s`.

**S9F-M6 — The docs promise an ArkLib bridge that does not exist, and no ArkLib module is importable.**

- **The mismatch.** DESIGN §4 ("carries over unchanged"), §8, §10 and CLAUDE.md's layer table name
  `Bridge/ArkLib.lean`. The directory is empty, and gate rule 6's allowlist contains 0 ArkLib
  modules.
- **Why it matters.** The submitter's largest proof obligation (item 3 of §3) has no importable
  library. The pinned ArkLib proofs that would help are partly sorried, and the v0.3 bridge's
  direction (contract → ArkLib) would not let a submitter reuse them anyway.
- **Fix (docs).** Correct DESIGN §4, §8, §10 and CLAUDE.md now: there is no bridge, and ArkLib is
  not importable.
- **Fix (decision).** Either allowlist a curated, sorry-free ArkLib slice with an ArkLib →
  contract transfer lemma, or build asset 3 of §3 in `Library/`.

**S9F-M7 — The DESIGN understates the work of a ranked entry.**

- **The understatement.** §7.3 says the gap is "write a known verifier as a circuit with a
  verified gadget library". The two largest items are elsewhere: the `Secure` proof with a
  per-round 2^-128 RBR-KS (25–50 person-weeks), and a **machine-code RS decoder proved against
  `Rv64`** (10–20 person-weeks). Neither has library support.
- **The total.** §3 estimates 80–150 person-weeks for the first entry. Without the assets of §3,
  the boards may open with no ranked R entry for the season.
- **Fix (docs).** Replace the §7.3 paragraph with §3's table, or a short form of it, and name
  §3's three assets in §11/§12 as the organiser's next steps. Tie O-7 to them.

### Minors

**S9F-m1 — The build and harness caps (§6.5) are not enforced, and they are inconsistent.**

- **Not enforced.** `harness.sh` has no `timeout` and no `MemoryMax` around the comparator, the
  gate-tree `lake build` or the badge build.
- **Inconsistent.** The solution is built twice (comparator tree, gate tree), so a 1 h build forces
  a ≥ 2 h harness.
- **Fix.** Wrap each stage in
  `systemd-run --user --scope -p MemoryMax=48G -p OOMPolicy=continue timeout …`, and set the
  harness cap to ≥ 2 × the build cap + 1 h of replay. Alternatively, bind the build cap to the
  first build only and say so in DESIGN §6.5.

**S9F-m2 — The external tools are undocumented.**

- **What is missing.** The comparator (`d03acab`, cloned from a v0.3 probe directory),
  `lean4export`, `nanoda_lib` (`3a24072`, cargo), bubblewrap, delegated cgroups,
  `riscv64-unknown-elf-*` and Python ≥ 3.11. `ci.sh` defaults to this machine's paths, and
  `harness.sh` to a nonexistent `$REPO/tools/comparator`, so
  `HARNESS=1 submissions/baseline/scripts/check.sh` fails on a clone (§1, row 6).
- **Fix.** Add a "Setup on a new machine" section to README (pins, URLs, build commands), and a
  `scripts/setup-tools.sh`. Give `harness.sh` and `ci.sh` one shared default, e.g. a
  `scripts/tools.env` sourced by both.

**S9F-m3 — CLAUDE.md's fresh-clone and timing text is wrong or incomplete.**

- **The text.** "Removes the symlink and runs `lake exe cache get`": there is no symlink in a
  clone, and `cache get` is not sufficient. "≈ 40 s warm" is the only build time given.
- **Fix.** Give the sequence (setup-clean with or without network; cache get; the CompPoly and
  Clean builds) and the measured cold numbers: 5 min 05 s for the default build; 5 min 39 s for
  the organiser build; 13 min 29 s for CI from a clone, or 11 min 47 s warm.

**S9F-m4 — Submitters are not told the kernel cost model.**

- **The rates.** A BLAKE2s compression is ≈ 2.2 s, a `K` product ≈ 50 ms (measured), and a `cmpToy` `NARG`
  run 35–40 s, each paid at elaboration and again by both kernels.
- **The consequence.** Any kernel evaluation at real scale breaks the 2 h harness cap.
- **Fix.** A paragraph in `submissions/baseline/README.md` or a submitter guide: kernel-checked
  controls only on toy instances; prove `live` with `live_of_secure`, not by evaluation.

**S9F-m5 — The development VM cannot host prover development.**

- **The gap.** No `pclmulqdq`, `vpclmulqdq` or `gfni`; shared and noisy.
- **Fix.** Record in `reference-machine.md` that the reference SKU and the agents' development
  machines must share the ISA extensions (§5). Prefer a bare-metal dev box with the reference
  flags for O-6's measurements.

**S9F-m6 — O-11's wording is out of date.**

- **The issue.** CompPoly's GS is Lean code over KoalaBear, not an RV64 image over `K`, so it
  cannot "fit `B(k)`" as such.
- **Fix.** Restate O-11 as "an RV64 + Zbc RS decoder with a proved step bound". `B(k)` admits
  unique decoding with 2^3.6–2^7.6 slack, and Koetter GS up to multiplicity 2 at ρ = 1/16 or 5 at
  ρ = 1/4 (§4.3). Name the measurement: the inner-loop steps and Koetter's constant at k = 20.

**S9F-m7 — Two design constraints for submitters go unstated.**

- **In char 2 LogUp-style bus or lookup arguments are unsound.** Multiplicities are taken mod 2.
- **`PerfectComplete` over every challenge vector excludes division-based arguments.** An honest
  `1/(γ − a)` fails at `γ = a`.
- **Fix.** Add both to DESIGN §9.2 or a submitter guide. Clean's §9.2 discussion covers only
  balance in its own `Ensemble.Statement`.

**S9F-m8 — Cold timings in docs are warm timings.**

- **The gap.** DESIGN §7.4's 11 min 47 s CI assumes a warm root tree (step 11: 11 s warm, 121 s
  in a clone). CLAUDE.md's 40 s build is warm.
- **Fix.** Report both warm and cold figures wherever a time is a cap or an operator's estimate.

---

## 8. Feasibility verdict

1. The organiser pipeline works, but **not from a fresh clone** (M1: an empty untracked directory;
   M2: a manifest that is machine state). CI is green in 13.5 min after two one-line workarounds.
2. **Per submission**, the harness costs ≈ 5 min for a toy, and ≈ 2 × the build plus tens of
   minutes of replay for a real entry.
3. **The caps do not compose** (M5: the real step budget is ≈ 80–100 s), and indexing near the
   fixed point exceeds its budget (M4).
4. **The decisive number:** with BLAKE2s alone, `C_V` fits only at k = 27–28, the top of
   `k_range`, and only with Johnson-regime WHIR (M3). The first ranked R entry is ≈ 80–150
   person-weeks without organiser libraries (M6, M7).
5. **Board L can open after M1, M2 and M5. Board R should not open** until M3 is decided (a cheaper
   menu hash, or k ≤ 30), M4 is fixed, and the NARG gadget kit and the verified decoder image exist.

# S9 review (whole repository): incentives and gaming of the competition

Stage 9, one of three whole-repository adversarial reviews (incentives; the other two cover the
definitional soundness of the trusted base and feasibility, and are cited as "the definitions
reviewer" and "the feasibility reviewer"). 2026-10-15, at commit `0451b32` (plus the
documentation agent's uncommitted DESIGN §6 patch, which this review read as current).

**Lens.** Do the rules as implemented make "build a fast, sound, recursive hash-based SNARK over
GF(2^64)" the winning strategy, and nothing cheaper? I played the adversarial submitter with
unlimited engineering budget, aiming at the top of board R (`S_rec`) or board L with the least
cryptographic work.

**Read.** `CLAUDE.md`; `docs/DESIGN.md` in full, including the current §6; `docs/DESIGN-AMENDMENTS.md`
in full (S1-A1 … S6b-A26); every `docs/stages/S*-RESULT.md` headline (S6b in full); every
`docs/reviews/S*-review.md` verdict and residual (S6b in full). The code that defines the game:
`RecursionFast/Contract/{Protocol,Extractor,Security,Compile,Recursion,Certificate}.lean`,
`scripts/Gate.lean` (rules 1–9), `scripts/source-rule.py`, `scripts/harness.sh` stage 3b,
`scripts/bwrap-landrun.sh`, `harness/run-benchmark.py` (all of it), `harness/README.md`,
`harness/reference-machine.md`, `RecursionFast/Challenge/{L,R}.lean.in`,
`scripts/render-challenge.py` (header), `submissions/baseline/README.md` and `prover/README.md`.
The standard: the v0.3 incentive review `CambridgePQ/recursion.fast/reviews/A1-incentives.md`
and DESIGN §6.6.

**Edited.** Only this file and `probes/s9/incentives/`. Logs are in `logs/S9/`.

---

## Verdict

**Board R (the headline): the core incentive is right. It is openable for ranking after three
fixes, one of them already known.**

- **What makes it work.** A ranked entry needs a kernel-checked `Secure` (worst-case RBR knowledge
  soundness with a bounded RISC-V extractor, over every admissible layout, `L_chain` included).
  It also needs a `RecursionEntry` whose `sound`, `complete` and `live` make its compiled
  verifier, as a layout, fit the protocol's own class.
- **What that excludes.** The trivial protocol, proof concatenation and "verify by recomputing
  the chains" are all excluded or uncompetitive (strategy rows 1, 4, 5). So the cheapest fast
  step is a small verifier circuit with a fast prover for it, which is a recursive SNARK.
- **Before ranking:**
  1. **O-12** (S6b-M3; the definitions reviewer's), so that the executed verifier is the proved one.
  2. **S9I-M2**: change the `S_rec` statistic. The current median rewards parking work in the
     unranked wrap steps.
  3. **S9I-M3**: change the record rule. At the measured noise, 3 % against a stored number is a
     lottery under resubmission.

**Board L: not openable as a ranked board in its current form (S9I-M1).**

- **The flaw.** The witness of `L_chain(n)` is a function of a 32-byte start (S6-A4), so its
  NP witness is 32 bytes, not 78 MiB.
- **The winning protocol.** Its verifier recognises the leaf key, reads `s` from a 64-byte tape
  and recomputes `blake2s^n(s)`. It is provably secure under the contract (its extractor
  regenerates the witness from `s`), fits every proof-size cap, and sits at the timer floor.
- **The cost to build it.** No cryptography: a completeness theorem for whole chains and a
  verified RISC-V witness generator.
- **The fix.** Unrank board L, or rescore it as "time until a leaf is inside a recursion proof"
  (`S_leaf + S_wrap/2`, board-R entries only).

Boards W and DoS are unranked and fine. Cross-step and cross-run persistence is closed: I probed
daemons, `/tmp`, `/dev/shm`, SysV shared memory and kernel keyrings, and nothing survives a step.

---

## Strategy table

"Residual": **closed** (by a theorem or a fail-closed check), **raised bar** (a rule makes it
expensive but not impossible), **open**. Gains are on the board the strategy targets.

| # | Strategy | What stops it (file: declaration / rule / function) | Residual | Proposed rule / gain |
|---|---|---|---|---|
| 1 | Trivial protocol (proof = the full witness), board R | `RecursionEntry.complete` with `Layout.rel`'s cell clause (the fixed point); `NARG`'s `tapeCap` (`Compile.lean`); `triv_no_entry`, `triv_narg` (baseline) | closed | none |
| 2 | Same, board L | the runner's `caps.tape_L = 2^17` on every leaf tape (`run-benchmark.py`, leaves loop) | closed for the full witness (72 MiB of prover-chosen cells) | none |
| 3 | **Compressed witness on L**: send `s` (32 bytes), the verifier recomputes the chain | nothing. `Secure` holds: on the leaf key the image regenerates the tables from `s` (≈10^9 steps ≤ `B(24) = 2^64`). The tape is 64 bytes. | **open** | **S9I-M1**: unrank L or rescore it; S_leaf drops to the timer floor |
| 4 | Compressed witness at nodes ("starts" proofs: a node proof lists the starts of its leaves; verify by recomputation) | `complete` covers every accepted node. The root proof (64 starts) must be accepted, so `C_V` must recompute the chains of two children of up to 64 starts each: `2·64·1024` compressions, ≥ 393 M cells at ≥ 3,000 cells per compression (S6-A7's floor is 4,640 with byte lookups), > `2^28` | closed at N = 64, n = 2^10. Margin ≈ 1.5–2.3× at k = 28, ≥ 23× at k = 24. Uncompetitive in time anyway. | S9I-m1 (keep 2·N·n·c > 2^28 as a design constraint) |
| 5 | Proof concatenation (a node proof is its children's proofs) | `NARG`'s 1 MiB cap at depth 6 (64 leaf proofs); `complete` puts up to 64 leaf verifications per child inside `C_V` | closed or uncompetitive | none |
| 6 | `live` met through the key of a trivially satisfiable layout, nothing hard accepted (S5-A10's gap) | the benchmark run: every leaf and node proof must verify (`Runner.verify`) | closed by measurement | none |
| 7 | Accept-all or accept-most verifier, in Lean | `Protocol.Secure` = `SecureWith (relK k) …` with `ExtractorImage.toExtractor` (B(k) in all, S4-A14); `relK` ranges over every admissible layout, `L_chain(n)` included | closed (kernel) | none |
| 8 | **Executed `verify`/`index` ≠ proved** (forged emitted code; e.g. a verifier that accepts MAC-keyed fake proofs, prover does nothing) | twin `rfl` (S6b-A4), the A7-M3 build binding, gate rules 3, 6, 7, 8, 9, the source rule (S6b-A20) | **open until O-12** (S6b-M3; the definitions reviewer's) | O-12 before ranking. Gain: every board, unbounded. S9I-m3 canaries catch only naive forgeries. |
| 9 | Unsound shortcut "caught only if the organiser tests wrong proofs" | Nothing at run time. The runner presents no wrong proof to `verify`, only 1,000 random DoS tapes under the **leaf** key. Protection rests on rows 7 and 8. | raised bar | S9I-m3: grammar and soundness canaries; DoS under `vkC` too |
| 10 | Verifier special-cases its own `C_V` (by `VK`) | allowed (DESIGN §6.6); `Secure` makes the special case sound | intended | none |
| 11 | `C_V` special-cases `vkL` (the benchmark leaf key) | `complete` ranges over every `vkL`. Only W steps verify leaves; ranked steps have node children. | no effect on `S_rec` | none |
| 12 | Specialised SNARK for `L_chain` (recognised by `VK`, own BLAKE2s arithmetisation) | allowed: `VK : Layout K → …` is any computable function (P_triv's `VK` already decides admissibility) | legit, but board L then ranks hash-chain provers, not the universal SNARK on `L_chain` | part of S9I-M1 |
| 13 | Per-instance precomputation at indexing (untimed, 1 h) | `VK`, `IDX` are functions of the layout only (`Protocol`); statements are fresh per evaluation (`run-benchmark.py secrets`, `chain_stmt`) | closed; layout-only preprocessing is holography (legit) | none |
| 14 | Precomputation in the native prover's build (1 h, writable build directory, no network) | only public layouts (`C_V`, `L_chain(n)`) exist at build time; the build directory is read-only (`--ro`) during steps | legit (e.g. baked index trees) | none |
| 15 | Cross-step state: daemons, `/tmp`, `/dev/shm`, SysV shm, kernel keyrings, step directories | `bwrap-landrun.sh --minimal-root`: `--unshare-pid --die-with-parent`, a fresh tmpfs `/tmp`, `--dev`, `--unshare-ipc`, an unprivileged user namespace; a fresh step directory, with the run directory hidden | closed, **measured**: `persist_probe.py` and `daemon_probe.sh` (`logs/S9/persist-probe.log`, `daemon-probe.log`). Nothing written in one step is visible in the next; a double-forked daemon dies with its step. | none |
| 16 | Runs 2 and 3 reuse the instances (S6b-A8), so a cache would make them free | row 15 | closed while row 15 holds | none |
| 17 | Multi-process memory | per-step cgroup `MemoryMax`, `MemorySwapMax = 0`; an `oom_kill` rejects (S6b-A23) | closed | none |
| 18 | Move work verifier ↔ prover | each step's score = prover wall + `NARG` wall of its output (`step_record`) | closed | none |
| 19 | Move work leaf → wrap (pre-digested leaf proofs) | W is unranked; leaf time counts on L only | legit (§6.6) | none |
| 20 | **Move work wrap → level 2** (W emits cheap-to-verify proofs) | nothing. The 16 level-2 steps are a majority of the 31 ranked steps, so the median is a level-2 step. | **open** | **S9I-M2**: `S_rec` 2–4× better with no change in steady-state cost |
| 21 | Alternate modes across levels ≥ 2 | the median over steps | **open** (same mechanism) | S9I-M2 |
| 22 | Lucky single steps, nondeterministic prover | median over 31 steps × 3 runs; every instance must succeed | closed for single steps | none |
| 23 | **Record by noise** (3 % margin, stored standing number) | `is_record`: `new ≤ 0.97·standing` | **open**: 17.7 % false records per identical resubmission at the measured noise, 3.2 % at a plausible reference noise | **S9I-M3** |
| 24 | **Sybil**: k near-identical resubmissions | nothing | **open**: 86 % (VM noise) and 27 % (reference noise) chance of a false record within 10 tries | S9I-M3 |
| 25 | FS grinding to cut queries | `PerfectComplete`: the honest transcript must be accepted for **every** challenge vector, so a PoW check on challenges breaks completeness | closed, uniformly (a design-space constraint) | none |
| 26 | Hash menu, arity, leaf packing | `Cfg` (`HashId.blake2s` only; arity ∈ {2, 4, 8, 16}), `OShape.logLeaf` | legit choices. A new menu hash with hardware support on the SKU (SHA-NI) will move native vs in-circuit trade-offs; that is one-machine overfitting, accepted. | none |
| 27 | Pass work to the extractor, or hide it in `enc` | S4-A1 (the contract's serialisation), the image literal ≤ 1 MiB (`Certificate.img`), `fuel_le` (a total); neither the extractor nor the Lean prover is executed, so no timed work can move there | closed | none |
| 28 | Class choice `k` ∈ [24, 28] on R | `k_range`; `Declared.k` pinned (S6b-A22) | free parameter: at k = 28, `C_V` has 16× more room, the extractor 2^8× more budget per benchmark instance, and row 4's margin is ≈ 1.5× | S9I-m1 |
| 29 | Class boundary on L (2^12 only at k ≥ 26) | the runner skips 2^12 below 26 | `S_leaf` is a different order statistic per class | S9I-m2 |
| 30 | Scoreboard values not pinned | S6b-A22 pins `k`, hash, digests and `C`; the arity is the submission's | residual: bench parameters, hardware id and prover source are not in the result's identity | S9I-m5 |
| 31 | Secrets reuse (the leaf prover sees `s` and can hide it in unchecked tape bytes) | procedural: `harness.sh --secrets FILE` takes any file | raised bar | S9I-m4 |
| 32 | Organiser trust: `Compile.lean` grammar (no batching, no grinding), `L_chain` generator, `treeRoot` | trusted by review; fidelity tested (§7.2); Python `tree_root` KAT-checked (`selftest`) | uniform. A generator bug does not help rows 3 or 20, and `Secure` quantifies over all layouts. Changing the grammar or the trusted hash speed re-ranks everyone (O-9). | freeze per season |
| 33 | One-machine overfitting | accepted (§6.1) | accepted | none |

---

## Findings

### S9I-M1 (major): board L is won by a sound protocol that sends the chain's start and recomputes the chain

**The premise that fails.** DESIGN §6.2: "on L the proof-size cap plays that role, since a leaf
has no fixed point (proof = witness is 78 MiB for `L_chain(2^10)`…; the cap is 128 KiB)". The
same premise is in §6.6 row 1 and the baseline README §6 ("Any protocol whose proof contains the
witness is excluded, whatever its shapes. This is the role DESIGN §6.2 gives the proof-size
cap"). But:

- the witness of `L_chain(n)` is **unique given the 32-byte start `s`** (S6-A4);
- the leaf prover is even handed `s` (`secret.hex`, S6b-A16).

The minimal witness is 32 bytes. No proof-size cap separates "send the witness" from a SNARK.

**The protocol `P_rc`.**

- **Key.** `VK L` flags "`L` is `L_chain(n)`" (computable: compare `Layout.words L` with the
  generator's; it runs in the untimed indexer).
- **Shapes.** Fixed: round 0 is a plain `msg ⟨2, 2⟩` (4 elements). The next rounds are any
  secure fallback's (e.g. `P_triv`'s; on the flagged key their roots are absorbed but never
  opened).
- **On a flagged key.** The prover sends a mode bit and `s`. The query program `query 1 0`
  reads `s`, recomputes `blake2s256^n(s)` and compares it with `y`, `n` and the zero tail of `x`.
- **Completeness.** It does **not** need the unproved fidelity direction (`rel → chain`). If
  `s(w)` does not reproduce `y`, the prover sets the mode bit to the fallback.
- **Knowledge soundness on the flagged key.** It holds with the contract's extractor. Acceptance
  implies `blake2s^n(s) = y`, and the image regenerates the `L_chain(n)` tables from `s` (about
  10^9 steps ≤ `B(24) = 2^64`; output ≈ 10.2 M words ≤ `witCap = 2^36`).
- **The proof burden is deterministic program verification, no cryptography:**
  1. ∀ s, `rel (L_chain n) (stmt s) (gen s)` (the "completeness theorem for whole chains" DESIGN
     §5.3 says does not exist yet);
  2. the RISC-V generator is correct on the vendored Rv64;
  3. `VK`'s flag implies `L` is `L_chain(n)` up to `normal` (`pLayout_words`);
  4. the fallback (`P_triv`, already proved).

  This is less work than an honest entry, whose extractor must decode Reed–Solomon codewords in
  verified RISC-V within `B(k)` (O-11).

**Evidence** (`probes/s9/incentives/recompute_leaf.py`, `logs/S9/recompute-leaf.log`). The probe
builds the protocol's tape from the trusted grammar (`Compile.lean`'s header, written
independently) on a real chain and runs `NARG`'s acceptance condition:

- **Tape and acceptance.** The tape is **64 bytes** at n = 2^8, 2^10 and 2^12 (cap 131,072).
  The honest tape is accepted; a tape with a wrong start is rejected.
- **Prover.** It writes `s` and 32 arbitrary bytes.
- **Verifier.** It does n + 4 hashes: about 6.3 ms at n = 2^10 with Lean's compiled spec
  (6.1 µs per one-block hash, S2-RESULT).

**Gain.**

- **`S_leaf` of `P_rc`** is the timer floor: two sandboxed process start-ups plus 6 ms. The
  smoke protocol's `S_leaf`, which is the same floor, is **0.267 s** (DESIGN §6.4).
- **Any SNARK's `S_leaf`** is that floor, plus encoding and committing ≥ 72 MiB of prover-chosen
  cells, plus a verifier that is slower than 1,024 hashes.
- **Result.** `P_rc` beats every SNARK by the whole of the SNARK's proving time: a factor of 2
  to 10 or more, by my estimate. Once one such entry is public it can be copied, and board L
  becomes a lottery at the floor, where a single process varies by 15–26 %
  (reference-machine.md §5).

**Options I rejected.**

- **A smaller cap.** The minimal witness is 32 bytes.
- **A verifier-scaling test** (verify time at 2^12 against 2^8). Padding the small case defeats
  it, and process start-up dominates both.
- **A leaf with an incompressible witness above the cap.** Exceeding 128 KiB eightfold needs ≥
  1 MiB of private input: 16,384 compressions, ≈ 151 M cells, class 28.

**Fix.** Either option closes the hole.

- **(a) Now: board L becomes "published, unranked"**, like W. Change DESIGN §6.2's table and
  its "Why these" paragraph, and §6.6 row 1 (replace "L: proof-size cap" with "L: unranked; the
  leaf witness is 32 bytes (S9I-M1)"). Change the baseline README §6's sentence (S9I-m6) and
  `harness/README.md` "Classes and boards".
- **(b) If a second ranked board is wanted**, rank `S_LW = S_leaf + S_wrap / 2`. It is the
  per-leaf time until the leaf is inside a `C_V`-keyed proof, and it is for board-R entries
  only. `P_rc` then pays for its chains inside `C_V` at the wrap step, which needs a real SNARK
  prover. What remains is a legitimate specialisation: the submitter's own BLAKE2s circuit
  instead of `L_chain`'s 9,225 cells per compression (row 12), which should be said so.
- **Where it goes.** `harness/run-benchmark.py` `evaluate` (`out["L"]`), DESIGN §6.2 and §6.6.

### S9I-M2 (major): the `S_rec` median is decided by level 2, whose inputs come from the unranked wrap steps

**The mechanism.**

- **What the median sees.** `S_rec` is the median over the 31 steps of levels ≥ 2 (16 + 8 +
  4 + 2 + 1; `run["S_rec"] = scores(run["nodes"])` in `evaluate`). The 16 level-2 steps are a
  majority, so whenever they are faster than the rest, the median is the slowest level-2 step.
- **Where level 2's inputs come from.** The level-2 children are wrap-step outputs, and W is
  unranked.
- **The two-mode protocol.**
  - **Shapes.** Fixed shapes hold both branches; the unused branch's committed oracles get dummy
    roots.
  - **Mode B.** Selected by a mode bit in a plain round. FRI-like at rate 1/16, so fewer queries:
    cheap to verify, ≈ 8× the proving work.
  - **Mode A.** Rate 1/2: cheap to prove.
  - **The circuit.** `C_V` arithmetises both. Chip heights are prover-chosen, so a mode-B child
    costs fewer cells.
- **The schedule.**
  - W steps (unranked) emit mode B.
  - Level-2 steps verify cheap mode-B children and emit mode A.
  - Levels ≥ 3 pay the steady-state cost.

  §6.6 calls pre-digested proofs "legitimate". They are legitimate as engineering, but here they
  move the headline without lowering the steady-state cost of a recursion step.

**Gain.**

- **Query counts.** At 128 bits in the unique-decoding regime, with no grinding (row 25), rate
  1/2 needs ⌈128 / 0.415⌉ = 309 queries and rate 1/16 needs 141. The in-circuit verification of
  a mode-B child is therefore ≈ 2.2× smaller (≈ 1.9× after its 3 extra Merkle levels). In the
  Johnson regime the ratio is 256 / 64 = 4×.
- **The step.** A node step is dominated by proving `C_V`, whose size is the verification of its
  two children.
- **Probe** (`noise_sim.py` part D, `logs/S9/noise-sim.log`).
  - With level-2 cost at 0.75 / 0.5 / 0.25 of steady state, the current `S_rec` is **0.789 /
    0.526 / 0.263**.
  - The proposed statistic gives **1.005 / 1.004 / 1.005**.
- **Moving the cut does not help.** Any median over a suffix of levels is decided by its lowest
  level, which has 2^(6−ℓ) steps against 2^(6−ℓ) − 1 above it, and whose children come from
  outside the set. Alternating modes across levels (row 21) is the same mechanism.

**Fix: rank the slowest level group.**

- **The statistic.** `S_rec := max(m₂, m₃, m₄₋₆)`, where `m_g` is the median over runs of the
  per-run median over group `g`'s steps. Levels 4–6 are pooled into one group of 7 steps, so
  that no group has a single sample.
- **Why it closes the hole.** A schedule in which every group is cheap contains a cheap mode
  cycle over levels 3–6. That cycle is itself a valid uniform or periodic steady-state schedule
  at that cost.
- **The cost for an honest uniform entry** (probe):
  - at σ_step = 3 %: the mean moves by **+0.7 %**, and the sd goes from 0.57 % to 0.69 %;
  - at σ_step = 6 %: **+1.4 %**, and the sd goes from 1.09 % to 1.36 %;
  - the shift is the same for every uniform entry.
- **Also:** publish the per-level medians.
- **Where it goes.** `harness/run-benchmark.py` `evaluate`: `run["S_rec"]` becomes per-group
  medians, and `out["R"]["S_rec"]` the max of the medians over runs. Also DESIGN §6.2's R row,
  §6.3 step 6, §6.6 row "move work into the leaf proofs" (add "and from the wrap steps into level
  2: `S_rec` is the slowest level group, S9I-M2"), and `harness/reference-machine.md` §3.

### S9I-M3 (major): the 3 % record rule against a stored number does not separate records from noise, and nothing limits resubmission

**As implemented.** `is_record(new, standing, 0.03)` compares the challenger's `S` with the
standing record's stored `S`, measured in another session, with 3 runs per evaluation. Two
problems:

- "a record is never invalidated by a re-run" (§6.4), so a false record stays;
- there is no limit on resubmitting identical entries.

**What the measurement says.**

- **Measured spread.** `S` spread 1.8–5.9 % across three evaluations. Per-step noise alone,
  after a median over 93 step times, would leave ≈ 0.8 %. So most of the noise is correlated
  session drift, and more runs in the same session do not remove it.
- **The model.** `noise_sim.py` simulates the runner's statistic (median over runs of the
  per-run median over 31 steps) with session, run and step noise. Two entries of equal true
  speed:

| noise regime (σ_sess, σ_run, σ_step) | current rule: P(false record), 1 try / 10 tries | paired, 5 pairs, 3 %: 1 try / 10 tries | power for a truly 5 % faster entry (current → paired) |
|---|---|---|---|
| development VM, the only measurement (2 %, 1 %, 6 %) | **17.7 % / 85.8 %** | 0.27 % / 2.7 % | 73.9 % → 96.6 % |
| plausible reference SKU (1 %, 0.5 %, 3 %) | **3.2 % / 27.4 %** | < 0.01 % / < 0.1 % | 90.4 % → 100 % |
| quiet reference SKU (0.5 %, 0.3 %, 2 %) | 0.01 % / 0.1 % | < 0.01 % | 99.1 % → 100 % |

- **More runs and a larger margin are worse than pairing.** Unpaired, 5 runs, 5 % gives 4.95 %
  per try in the VM regime and only ≈ 49 % power at a true 5 % gain.

**Fix.**

- **Rule.** Screening as now. A tentative record (`S_new ≤ 0.97·S_std`) triggers a **paired
  confirmation**:
  - the standing entry and the challenger are re-run in **one session**;
  - **interleaved run by run** (R C R C …), **5 pairs**, on one fresh set of instances;
  - it is a record iff the **median over pairs of `S_C,i / S_R,i` ≤ 0.97**;
  - the ratio cancels session drift.
- **Margin calibration (O-6).**
  - On the season's SKU, run ≥ 10 paired self-comparisons of one realistic entry. Until one
    exists, use the smoke protocol with a fixed multi-threaded 5–30 s prover workload.
  - Estimate σ_p, the sd of the per-pair log-ratio.
  - Use `R ≥ (3.75·σ_p / m)²` pairs, i.e. 3 sd of the median below the margin. For m = 3 % that
    is 5 pairs at σ_p = 1.5 % and 10 at σ_p = 2.5 %.
  - Keep m = 3 % if that R is affordable; otherwise raise m.
- **Sybil rules.**
  - An entry's ranked score is its paired confirmation.
  - Entries with the same `digestC` and the same `.olean` hash of `leaf` are one entry.
  - At most one confirmation per team per week.
  - Ties within the margin go to the incumbent.
  - Every evaluation is published, and no best-of-k.
- **Where it goes.** `harness/run-benchmark.py`: a `paired` command beside `record` that runs
  two configurations interleaved. Also `harness/reference-machine.md` §4 and DESIGN §6.4
  (record rule, re-runs) and §6.6 row "lucky runs / noise".

### S9I-m1 (minor): the class `k` is a free parameter on board R

**What a higher class buys.** A board-R entry may declare any `k` in [24, 28] (`k_range`). Going
from 24 to 28:

- multiplies `C_V`'s cell room by 16;
- multiplies the extractor budget per benchmark instance by 2^8 (`B(28)/B(24)`);
- shrinks the fixed point's margin against non-succinct node verifiers (row 4) from ≥ 23× to
  ≈ 1.5×, because `2·N·n·c_min ≈ 393 M` against `2^28 = 268 M`.

**Effect.** None on `S_rec` today: the starts scheme is also uncompetitive in time. The exclusion
is quantitative in N and n, though. A smaller organiser tree (e.g. N = 16) at k = 28 would admit
it: 98 M < 268 M.

**Fix.**

- State the constraint `2·N·n·c_min > 2^28` (so N ≥ 64 at n = 2^10) in DESIGN §5.2 / §6.3.
- Show `k` beside every R score (`out["R"]`).
- Decide, with the feasibility reviewer's `C_V` size model, whether R should eventually be
  ranked at one class (24) or per class.

### S9I-m2 (minor): `S_leaf` is a different order statistic per class

**The problem.** `run["S_leaf"]` is the median over all leaf chains of the run:

- at k = 24: 64 × 2^10 and 16 × 2^8. The median is about the 38th percentile of the 2^10 chain
  times.
- at k ≥ 26: also 16 × 2^12. The median is about the 50th percentile.

So declaring 26 raises `S_leaf` for the same prover, adds 16 chains that must fit the 120 s
budget, and no one will run the optional scaling test.

**Fix.** `S_leaf := (m_{2^8}·m_{2^10})^{1/2}`, the geometric mean of the per-`n` medians, for every
class. Publish `m_{2^12}` separately. File: `harness/run-benchmark.py` (`run["S_leaf"]`,
`out["L"]`). This matters only if L stays ranked (S9I-M1(b)).

### S9I-m3 (minor): the runner never presents a wrong proof to `verify`

**The gap.**

- **What is tested.** Only random DoS tapes, and only under the **leaf** key with the first
  leaf statement (`R.run_verify("dos", keys[tree_n], xs[0], …)`).
- **What that leaves.** A verifier that does not read its inputs (a naive forgery under row 8, a
  misbuilt executable) passes every check the runner makes. The recursion key's verifier is
  never DoS-tested.

**Fix.** For every verified proof, or at least 8 per run and kind, run `verify` four more times,
untimed, and **reject the evaluation if any accepts**:

| canary | why it must reject |
|---|---|
| the tape with one byte appended | **grammar-guaranteed for every protocol**: `runQ`'s `.done _, _ :: _ => none` |
| the tape with its last byte removed | **grammar-guaranteed for every protocol**: every round and opening has a fixed length, so `takeN` or `readOpening` fails |
| the statement with one bit flipped (`y` of a leaf, `d2` of a node) | by soundness: FS seeds with `x`, and acceptance means broken soundness or forged code |
| leaf proofs under `vkC`, node proofs under `vkL` | by soundness: the sponge is seeded with `D` |

Also add DoS tapes under `vkC` with a node statement.

**What it catches.** Accept-all and input-blind executables. It does not catch a MAC-keyed
forgery; only O-12 does.

**Where it goes.** `harness/run-benchmark.py` (`Runner.verify`, the DoS block).

### S9I-m4 (minor): fresh secrets are a procedure, not a check

**The problem.** `scripts/harness.sh --secrets FILE` accepts any file. The leaf prover sees `s`
and can store it in tape bytes the verifier never checks; `P_rc` above has 32 such bytes. If
the proofs of an evaluation are ever kept or published and a secrets file is reused (a re-run, a
paired confirmation), a later build can bake those proofs in.

**Fix.** The production harness generates the secrets itself (`run-benchmark.py secrets` into
`WORK`, mode 0600, deleted afterwards) and refuses `--secrets`. Every evaluation, including each
paired-confirmation session, gets fresh secrets. A ledger of `secrets_sha256` (already in the
result) rejects a repeat. File: `scripts/harness.sh` stage 3b.

### S9I-m5 (minor): a result does not say what it was measured under

**The problem.** The result JSON has the machine's hostname and CPU, but not:

- a hash of the effective bench configuration (tree size, leaf board, repeats, budgets, caps,
  classes; organiser-chosen, from `--bench`);
- the season's hardware id (reference-machine.md §1);
- a hash of the prover's source tree.

`record NEW STANDING` compares bare floats.

**Fix.**

- Add `config_sha256` (the config minus the per-entry `verify`/`index`/`prover`/`layouts`/
  `claim`/`k`), `hardware_id` and `prover_tree_sha256` to `res`.
- Let `record`/`paired` refuse to compare results whose `config_sha256` or `hardware_id`
  differ.
- Fix one bench configuration per season.

Files: `harness/run-benchmark.py` (`cmd_run`, `is_record`), `harness/reference-machine.md` §1.

### S9I-m6 (minor): stale or unvalidated statements a submitter reads

**`submissions/baseline/README.md`, §1 (lines 8–12):** it says "the runner's default leaf board
`{2^8, 2^12}`" and "A class-24 entry that requests board L fails every default evaluation".
Since S6b-A8 the leaf board is `{2^8, 2^10}` at 24, and 2^12 is skipped below 26.

**The same README, §6 (line 289):** "Any protocol whose proof contains the witness is excluded,
whatever its shapes. This is the role DESIGN §6.2 gives the proof-size cap". This is false for
the compressed witness (S9I-M1). Correct it with S9I-M1's fix.

**DESIGN §6.6, the row "Lean-compiled verifier is slow … verifier time is a small share of
`S_rec`":** this has no measurement behind it.

- **The numbers.** The trusted hash costs 6.1 µs per one-block hash and the trusted `K.mul`
  27 µs (O-9). A FRI-like verifier with ≈ 300 queries × ≈ 20 path levels does ≈ 6,000 hashes
  (≈ 37 ms), plus 10^4–10^5 `K` products (0.3–2.7 s at the spec's speed unless the submitter
  proves a faster one).
- **Why it matters.** `NARG` can be comparable to the prover's time. The incentive points the
  right way (fewer native field operations means a smaller `C_V`).
- **Fix.** Restate the row with these numbers.
- **One more consequence.** Any organiser change to `Compile.lean`'s or `Blake2s.lean`'s compiled
  speed re-ranks every entry. Freeze both per season.

---

## Noise and margin: the recommendation in numbers

1. **What dominates.** Session drift, not step noise. At the measured per-step noise (σ ≈ 6 %),
   the median over 93 step times would move by ≈ 0.8 %. The measured `S` moved by 1.8–5.9 %.
   More runs in one session therefore do little. Pairing removes the drift.
2. **Current rule** (unpaired, 3 runs, 3 %): **17.7 %** false records per identical
   resubmission at the only measured noise, and **3.2 %** at a plausible reference noise. Within
   10 resubmissions that is **86 %** and **27 %**.
3. **Recommended** (screen as now, then confirm paired):
   - **Setup.** 5 interleaved pairs in one session on fresh instances; record iff the median per
     pair ratio is ≤ 0.97.
   - **False records:** **0.27 %** per try at the VM's noise and below 0.01 % at reference noise.
   - **Power** for a true 5 % improvement: **97–100 %**, against 74–90 % now.
   - **Cost:** one extra evaluation of the standing entry per tentative record, not per
     submission.
4. **Calibration** (O-6, before ranking):
   - ≥ 10 self-pairs on the SKU give σ_p.
   - Choose pairs `R ≥ (3.75·σ_p/m)²`: m = 3 % needs 5 pairs at σ_p ≤ 1.5 % and 10 at 2.5 %.
   - If σ_p > 2.5 %, raise m to `3.75·σ_p/√10`.
5. **With S9I-M2's statistic** (max of three group medians), the uniform upward shift is
   +0.7 % to +1.4 %, the same for every entry. Its extra sd (+0.1–0.3 %) is inside the
   calibration above.

---

## What I checked and found sound (no finding)

- **The fixed point does its job against the trivial family** (rows 1, 4, 5).
  - `complete` ranges over every accepted node, whatever its keys, and `rel` bounds the cells.
  - `live` at indexer keys (S5-A10) leaves only the "trivially satisfiable layout" gap, and the
    benchmark closes it (row 6).
  - A node's knowledge (2^j chain starts) cannot be shipped instead of a succinct proof: the
    root proof must be accepted, so `C_V` must handle two 64-start children. That is 2^17 chains,
    ≥ 393 M cells.
- **`Secure` covers the benchmark layout.** `relK k` contains `(L_chain(n), x)` for every `n`
  and `x`. So any `L_chain` special case, in `VK`, `verify` or `C_V`, must be RBR knowledge-sound
  with the bounded extractor. Unsound shortcuts therefore fail in the kernel, not at run time.
  The only run-time route is row 8 (O-12).
- **No per-instance precomputation exists anywhere untimed.**
  - Statements are fresh (`os.urandom`).
  - `VK` and `IDX` see only the layout.
  - The prover's build sees only public layouts.
  - The extractor and the Lean prover are never executed.
- **Isolation, measured.**
  - **Daemons.** A double-forked daemon in a step is killed with it (`daemon_probe.sh`: no file
    5 s later; the positive control without the sandbox writes it).
  - **Files and shared memory.** Writes to `/tmp`, `/dev/shm` and a SysV segment are invisible to
    the next step.
  - **Keyrings.** A key added to the user keyring is not found in the next step (ENOKEY), because
    each bwrap call has its own user namespace (`persist_probe.py`).
- **Pinning after S6b-A22.** `k`, the hash, the digests and the scored `C` come from the claim
  that rendered the challenge. The leaf key is the organiser's `L_chain` indexed by the
  submission's indexer (row 8 aside).
- **Grinding is not expressible** (row 25). The design space is uniform: no PoW, no batching
  (S3-A4). Both favour fewer queries and longer leaves, the same for all.

---

## Incentive statement (for the report)

> Board R ranks the measured wall time of one 2→1 recursion step. An entry qualifies only with a
> kernel-checked proof that its protocol is knowledge-sound with a bounded extractor on every
> admissible layout, the benchmark's included, and that its own compiled verifier, as a layout,
> accepts exactly the accepted node proofs within the protocol's class (`RecursionEntry`: `sound`,
> `complete`, `live`). That fixed point excludes the trivial protocol, proof concatenation and
> verification by recomputation, so the cheapest fast step is a small verifier circuit with a fast
> prover: a recursive SNARK. The benchmark run (fresh secrets, one sandboxed process per step with
> nothing persisting between steps, every proof verified) checks what the theorems leave to it.
> Three rules close what neither does: the executed verifier is regenerated from kernel terms
> (O-12); `S_rec` is the slowest level group, so work cannot be parked in the unranked wrap steps;
> and a record must beat the standing one by 3 % in one interleaved session. Board L is published,
> not ranked: a hash chain's witness is its 32-byte start, so a verifier that recomputes the chain
> is sound, meets any proof-size cap and runs at the timer floor.

---

## Probes and logs

| file | what | log |
|---|---|---|
| `probes/s9/incentives/recompute_leaf.py` | S9I-M1: the `P_rc` tape (64 bytes) from the trusted grammar, accepted; wrong start rejected; verify timing | `logs/S9/recompute-leaf.log` |
| `probes/s9/incentives/noise_sim.py` | S9I-M2 (part D: current vs proposed `S_rec` under the level-2 schedule; inflation for uniform entries), S9I-M3 (parts A–C: false records, power, sybil) | `logs/S9/noise-sim.log` (8,000 trials, seed 1, 21 s) |
| `probes/s9/incentives/persist_probe.py` | row 15: keyrings, SysV shm, `/dev/shm`, `/tmp` across two sandboxed steps (runner's `systemd-run` + `bwrap-landrun.sh --minimal-root` command line) | `logs/S9/persist-probe.log` |
| `probes/s9/incentives/daemon_probe.sh` | row 15: a double-forked daemon does not outlive its step | `logs/S9/daemon-probe.log` |

Reproduce: `python3 -I probes/s9/incentives/recompute_leaf.py --n 1024`;
`python3 -I probes/s9/incentives/noise_sim.py --trials 8000`. The two isolation probes need the
runner's sandbox command line; it is in each log.

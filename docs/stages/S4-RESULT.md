# S4 RESULT: the bounded extractor (Q1) and the trimmed machine

Stage 4 is DESIGN §11 step 5 (decision Q1, open item O-1). One agent implemented it on
2026-10-14. Nothing is committed.

- **New files:** `Contract/Machine.lean`, `Contract/Extractor.lean`, `Library/Extractor.lean`,
  `Controls/Extractor.lean`, `tests/asm/*.S` and `*.bin` (10 images), `probes/s4/` (2 files).
- **Appended:** one import each to the three root files (re-read before appending), and S4-A1 to
  S4-A8 to `docs/DESIGN-AMENDMENTS.md`.
- **Not edited (as instructed):** `Contract/Protocol.lean`, `Controls/{Toy,Hit,Negative}.lean`.
  The swap is prepared below and validated in a probe.

## Headline

- **Trusted lines:** `Machine.lean` 109 (target ≤ 120), `Extractor.lean` 63 (target ≤ 60).
  - The contract without `Compile.lean` and `Hash/` is now 449 code lines; the budget is 850.
- **The extractor is the program.** `ExtractorImage.toExtractor k sh` is a `Security.lean`
  `Extractor`. `extractMid m s tr w` runs the image on the tape `⟦m, s, tr, w⟧` for
  `extractorFuel k = 2^(2k+16)` steps and decodes the output. A fault, a trap, fuel exhaustion or
  an output of more than `witCap k = 2^(k+12)` words gives the empty witness.
- **Main deviation (S4-A1): the serialisation is the contract's, not the submitter's.**
  - **Why.** A submitter-supplied `enc`/`dec` is unbounded Lean computation on the extractor's
    path. For example, `enc` can append a brute-forced preimage that the image then copies, which
    voids the fuel bound. A round-trip law or a size bound does not stop this, since a preimage
    is a few words.
  - **What instead.** `WitMid` is fixed to `Mid n j`: the witness tables before round 0 (decoded
    by the trusted `decTables`), and plain words after round 0.
  - **Consequence.** `Protocol` loses its `WitMid` field.
- **What is proved:**
  - **Refinement interface.** `extractMid_eq_of_run`, `extractMid_eq_nil_of_run` and the
    `extractOut` pair.
  - **Tape round trip.** `unframe_frame`, `unframe_extractorTape`, `pLayout_words`.
  - **Codec bridge.** `Layout.words_eq`, `decTables_map_bits`.
  - **The 8-instruction first-message image, on every tape.** `run_firstMsgImage` and
    `firstMsg_extractMid`. Hence `toy_extractMid`: this image is the toy's extractor.
  - **Brute force, as a machine-level loop theorem.** At class 20 the brute-force image returns
    `none` whenever no candidate below `2^54` works (`brute_none`, `brute_extractMid_nil`).
  - **Kernel runs of the trimmed machine.** Copy, fuel exhaustion, the size cap, W-op/Zbc
    semantics and faults.
- **The swap works.** `probes/s4/ProtocolSwap.lean` proves `toy'_secure`: the toy, with the
  extractor field replaced by `firstMsgImage`, satisfies the swapped `Secure`.
- **Checks.**
  - `lake build` and `lake build RecursionFastBridge gate axiomaudit` are green.
  - The axiom audit reports **PASS** (302 S4 declarations).
  - `check-hygiene.sh` and `check-vendor.sh` report OK.
- **Closure.** The trimmed machine reaches **205 vendored declarations, 0 theorems** (v0.3: 474
  and 205), over the same 930 source lines.

## Files

Code lines are from `scripts/loc.py` (`logs/S4/loc-s4.log`, `logs/S4/loc-contract.log`). Compile
times are from `lake env lean`, as wall time and peak memory (`logs/S4/times.log`).

| File | Status | Code | Total | Time | Contents |
|---|---|---:|---:|---:|---|
| `Contract/Machine.lean` | **TRUSTED, new** | 109 | 198 | 3.0 s, 0.8 GB | memory map (`CODE_BASE`, `TAPE_BASE = 2^63`), `Image`, `unpack`, `Image.byteSize`, decoder, W/Zbc semantics, `memAccess`, `ordinaryStep`, `fetch`, `readOut`, `execute`, `initState`, `run` |
| `Contract/Extractor.lean` | **TRUSTED, new** | 63 | 148 | 5.2 s, 1.9 GB | `extractorFuel`, `witCap`, `imageCap`, `toWord`, `Table/Chip/Layout.words`, `Round.words`, `frame`, `extractorTape`, `Mid`, `decTables`, `decMid`, `ExtractorImage`, `call`, `toExtractor` |
| `Library/Extractor.lean` | untrusted, new | 423 | 569 | 8.8 s, 2.1 GB | refinement interface, symbolic-execution lemmas, tape lemmas, Codec bridge, `firstMsgImage` and its theorems |
| `Controls/Extractor.lean` | controls, new | 329 | 495 | 10.7 s, 2.8 GB | 33 theorems: copy, machine, fuel exhaustion, size bound, round trip, brute force, toy |
| `tests/asm/*.S`, `*.bin` | sources | — | — | — | `copy`, `section3`, `brute`, `spin`, `long`, `long32`, `wzbc`, `tapestore`, `misaligned`, `trap` (each `.S` names its control) |
| `probes/s4/TrustedClosure.lean` | probe | 42 | 47 | 21 s | reached vendored declarations (`logs/S4/trusted-closure.log`) |
| `probes/s4/ProtocolSwap.lean` | probe | 76 | 103 | 6.5 s | the prepared swap on a copy of `Protocol`; `toy'_secure` |

`lake build` with the four modules stale takes 25 s (`logs/S4/build.log`). The module builds are
3.1 s for `Contract.Extractor`, 6.8 s for `Library.Extractor` and 8.9 s for
`Controls.Extractor`. The vendored `RiscvZkvm` library is now in the default build's cone; it took
59 s cold (`logs/S4/build-vendor.log`).

## The trusted definitions

### `Machine.lean` (v0.3 trimmed)

- **Kept verbatim from v0.3.** `Image` (minus `harts`), `unpack`, `byteSize`, `WordOp`, `ClOp`,
  `Instruction`, `decodeInstruction`, `wordResult`, `clResult`, `memAccess` and `fetch`.
  - `ordinaryStep` is verbatim except the memory check.
  - `initState` is verbatim except the map.
- **Changed.**
  - **Memory check.** It is now "naturally aligned, and a store lands below `TAPE_BASE`". The
    address space is all of `2^64`; S4-A3.
  - **`HALT`.** `ECALL` with `t0 = 0` and an 8-aligned `a0` returns `readOut`: the `a1`
    doublewords from `a0`, through the vendored `readWords`. There is no accept/reject: an image
    gives up by trapping (S4-A4). Any other `t0` traps.
  - **`run`.** `run img input fuel : Option (List Word)`. Its docstring separates the failure
    modes: a fault, a trap, and fuel exhaustion (the `0` case of `execute`).
- **Removed.** The 18 counters, `Kind`/`tick`/`kind`/`latency`, `Acct` and first touch, the timer
  (`tock`, `opOf`, `ecallOp`, `rawAt`), harts (`Region`, `Child`, `Ctx`, `allows`, `access`,
  SPAWN/JOIN), QUERY (`query`), `Final`, `runFull`, `OUT_BASE`, `FUEL`, `TAPE_CAP`, `MEM_BYTES`,
  and `deriving DecidableEq` on the decoded instructions.
- **Imports.** Lean core, the vendored `Rv64.Execution` and `Interpreter.Decode`, and
  `Contract/Field.lean`. It uses `Nat`, not `ℕ`, so it needs no Mathlib.
- **Tape convention (v0.3's `Agrees.lean`, kept).**
  - Word `i` of the input is at `TAPE_BASE + 8·i`.
  - A `K` element is its `bits`; an `E` element is three limbs; an index challenge is
    zero-extended; a number is its low 64 bits.

### `Extractor.lean`

- **Input tape.** `extractorTape j (L, x) rounds w = frame [[j], L.words, x, round₀ …, w]`.
  - `frame` puts a directory first: the section count, then the start and length of each
    section. An image therefore finds any section in two loads.
  - `L.words` is `Codec.eLayout` read as words (`Layout.words_eq`, proved in the Library).
  - `Round.words` writes a message as its elements and a challenge as `Round.tapeWords`.
- **The two calls.** `extractMid m` uses `j = m` and the prefix through round `m`. `extractOut`
  uses `j = n`, the full transcript and `w = []`. So `extractMid (n−1)` and `extractOut` see
  the same transcript but different `j`.
- **Default witness.** It is the contract's: the empty list, which `Mid` makes well-typed at
  every round.
  - Before round 0, `[]` fails `relK`: an admissible layout has a chip, and `rel` needs one table
    per chip.
  - After round 0 it is whatever the submitter's `KSF` says about `[]`. The chain still has to
    reach round 0 with a real witness.
- **Computability.** The structure's docstring notes that `img` must be computable; the gate
  change is Stage 6.
  - `enc` and `dec` no longer exist, so only `img` is subject to it.
  - S4-A2: the image must also be the literal rendered from the claim.

## Controls (`Controls/Extractor.lean`, all kernel-checked)

| Control | What it shows |
|---|---|
| `copy_run`, `copy_steps` (`decide +kernel`) | `copy.S` (21 instr.) returns the witness `[7,8,9]` from a concrete two-round tape (oracle, `E` challenge + index) at the full fuel `extractorFuel 20 = 2^56`, in 36 steps exactly (35 fail) |
| `copy_extractMid` | through `toExtractor`: `extractMid 1` returns the input witness |
| `copy_run0`, `copy_extract_relK` | before round 0 the output `[1, 0×32]` is decoded by `decTables` as one 1×32 table, and the extracted witness **is in `relK 20`** for `triv` (end to end: image → output → trusted decoder → relation) |
| `wzbc_run` | `addw` sign-extends (`…fffe`), `clmulh` is the high carry-less word (`0x5555…`), stores and the data region work |
| `tape_readonly` / `tape_below_ok` | a store at `2^63` faults; the same program storing at `2^62` halts |
| `halt_misaligned`, `ecall_trap`, `halt_reads` | `HALT` with `a0 = 4` faults; `t0 = 1` (v0.3's QUERY) traps; data words are at address 0 |
| `spin_run_100` (kernel), `spin_run` (all tapes, all fuel), `spin_extractMid` | **fuel exhaustion**: the looping image returns `none`, so `extractMid` is `[]` for every class, round, statement, transcript and witness |
| `long_extractMid` / `long32_extractMid` | **size bound**: an output of `2^33 > witCap 20` words gives `[]` for every input; one of exactly `2^32` words is kept (both proved symbolically; never evaluated) |
| `tape_roundTrip` (kernel), `layout_roundTrip` | the directory returns `[[1], L, x, [5,6], [7,8,9,0xab], w]`; the layout section parses back to `triv.normal 256` |
| `brute_cost` (kernel) | `brute.S` finds `c = 5` for `x₀ = clmul(5, 0x1b) = 0x77` in exactly `15 + 4·5 = 35` steps (34 fail) |
| `brute_none`, `brute_extractMid_nil` | **Q1 negative control, as a machine theorem**: the brute-force image is run at class 20 (`2^56` steps), on any tape, or on any extractor tape with `x₀` addressable. If no `c < 2^54` hits the target, the run is `none` and the extracted witness is `[]`. The proof is a loop invariant (`brute_iter`, `brute_loop`: 4 steps per failed candidate) after an 8-step set-up |
| `extractorFuel_lt_word` / `extractorFuel_lt_two_words` / `word_le_extractorFuel` / `brute_steps_exceed` | the arithmetic: `B(k) < 2^64` for `k ≤ 23`; `B(k) < 2^128` for `k ≤ 28`; `B(k) ≥ 2^64` for `k ≥ 24` (S4-A7); `15 + 4c > 2^56` from `c ≥ 2^54 − 3` |
| `toy_extractMid` | for an admissible layout at `20 ≤ k ≤ 28`, the first-message image's `extractMid 0` is exactly `toyWit` for every message and witness: the toy's `next` law after the swap |

## Library interface (`Library/Extractor.lean`)

- **Refinement.**
  - `ExtractorImage.extractMid_eq_of_run`: if
    `run E.img (midTape sh m s tr w) (extractorFuel k) = some o` and `o.length ≤ witCap k`,
    then `extractMid m s tr w = decMid s.1 m.castSucc o`.
  - `extractMid_eq_nil_of_run`: a `none` run gives `[]`.
  - `extractOut_eq_of_run` and `extractOut_eq_nil_of_run` are the same for `extractOut`.
  - `call_of_run`, `call_of_run_none`, `call_of_long`, `decMid_zero`, `decMid_succ`.
- **Machine.**
  - Steps: `execute_step`, `execute_halt`, `execute_mono`/`run_mono` (more fuel keeps a halting
    run), `fetch_eq`.
  - Memory: `ordinaryStep_ld`/`_sd` (aligned access), `readWords_eq`, `length_readWords`,
    `getMem_initState_tape`.
  - Simp lemmas on registers.
  - **Note.** `getMem_initState` is deliberately not `simp`: on a symbolic address `simp` expands
    `BitVec.toNat_add` and does not terminate.
  - **Note.** `simp` must never see `(List.replicate (2^33) _).length`: a simproc builds the list
    (out of memory). Use `rw [List.length_replicate]`.
- **Tape.** `frameStart`, `frame_getD_count`, `frame_getD_start`, `frame_getD_len`,
  `frame_drop`, `frame_getD_sec`, `frame_length`, `unframe`, `unframe_frame`,
  `unframe_extractorTape`.
- **Codec bridge.** `Table.words_eq`, `Chip.words_eq`, `Layout.words_eq`, `pLayout_words`,
  `Layout.words_length` (`≤ 2^(k+8)`), `decTables_map_bits` (`= Codec.pWit`).
- **The first-message image.** `firstMsgImage`, `run_firstMsgImage` (any tape),
  `run_firstMsgImage_frame`, `run_firstMsgImage_tape`, `firstMsg_extractMid`.
  `extractorFuel_eq` unfolds the irreducible fuel.

## The Protocol swap (prepared; mechanical; to run when the orchestrator triggers it)

The swap was validated on a copy: `probes/s4/ProtocolSwap.lean` builds and proves `toy'_secure`.

1. **`Contract/Protocol.lean`.**
   - Add `import RecursionFast.Contract.Extractor`.
   - Delete the `WitMid` field and its docstring, and the `-- Stage 5: ExtractorImage …` comment.
   - Replace the `extractor` field by:

     ```lean
     /-- The extractor image (DESIGN §4 item 3, Q1): the named round-by-round extractor is this
     image run on the contract machine for `extractorFuel k` steps per call
     (`ExtractorImage.toExtractor`). -/
     extractor : ExtractorImage
     ```

   - Change `Secure` to:

     ```lean
     def Secure : Prop :=
       SecureWith (relK k) Set.univ P.prover P.specVerifier (P.extractor.toExtractor k P.shape) P.ε
     ```

   - Module docstring: "the extractor" becomes "the extractor image (computable, rendered from the
     claim)". The `Protocol.lean` line count should stay 47 ± 1.
2. **`Controls/Toy.lean`.**
   - Add `import RecursionFast.Library.Extractor` and `import RecursionFast.Library.RbrSound`.
   - In `toy`, replace `WitMid := …` and `extractor := {…}` by `extractor := firstMsgImage`.
   - Move `toy_extractMid` (with its proof) from `Controls/Extractor.lean` into `Toy.lean`, and
     drop the `Controls.Toy` import from `Controls/Extractor.lean`.
   - Replace `toyKSF` by the probe's `toyKSF'`. `toFun` is written with `Fin.cases`, because the
     witness before round 0 has type `Mid 1 0`. `next` destructures `s` and rewrites with
     `Transcript.concat_last` and `toy_extractMid`. `empty` and `full` are unchanged.
   - `toy_secure` is unchanged except for the KSF name.
3. **`Controls/CompileToy.lean` (Stage 3's `cmpToy`).**
   - Replace `WitMid := …` and `extractor := {…}` by `extractor := firstMsgImage` and add
     `import RecursionFast.Library.Extractor`. Any `ExtractorImage` would do, since `cmpToy` is
     not claimed secure.
4. **Unaffected.**
   - `Controls/Negative.lean`: `acceptAll_*` and `keepE` are stated over an arbitrary
     `Extractor`, and `rejectAll_not_secure`'s proof never touches the extractor.
   - `Controls/Hit.lean`: it uses `SecureWith` directly, not `Protocol`.
   - `Library/RbrSound.lean`: generic.
   - `Contract/Compile.lean`: it does not mention the extractor.
5. **After the swap.** The DESIGN §3.1 block gets the new field (S4-A8). Rerun `lake build`, the
   audit, hygiene, and `loc.py`.

## Closure measurement (`logs/S4/trusted-closure.log`)

`probes/s4/TrustedClosure.lean` is v0.3's probe with the roots restricted to
`RecursionFast.Contract.*` (900 roots, including `Compile` and the hash).

| | v0.3 | v2 (S4) |
|---|---:|---:|
| reached vendored declarations | 474 | **205** |
| of which theorems | 205 | **0** |
| distinct source lines | 930 | 930 |

Dropping `deriving DecidableEq` removes all the reached theorems and their instances. The line
count does not shrink, because the reached definitions still span the whole `Instr` type,
`execInstrBr` (it has a `CSRS` arm, so ZiskAccel's CSR model, 316 lines), `decode` and
`MachineState`. Per module: Basic 120 declarations / 239 lines, ZiskAccel 33 / 316, Decode 7 /
132, Execution 1 / 170, Instructions 10 / 48, Word 8 / 25.

## Axioms and hygiene

- **Axiom audit.** `lake exe axiomaudit` (`logs/S4/axiomaudit.log`) reports **PASS**: Machine
  131 declarations, Extractor 32, Library 91, Controls 48, all within `propext`,
  `Classical.choice`, `Quot.sound`.
- **Kernel evaluation.** The kernel runs use `decide +kernel` only; there is no `native_decide`.
- **Hygiene.** `scripts/check-hygiene.sh` reports OK (`logs/S4/hygiene.log`). The only attribute
  added to trusted code is `@[irreducible]` on `extractorFuel` (S4-A6, elaboration only).
- **Vendor.** `scripts/check-vendor.sh /home/devops/Verified-zkEVM/riscv-zkvm` passes:
  byte-identical to `6810fc1` (`logs/S4/check-vendor.log`).

## Deviations from the design and the brief (recorded as S4-A1 … S4-A8)

1. **S4-A1.** The serialisation is the contract's, `WitMid := Mid` is fixed, and there is no
   submitter `enc`/`dec`/`encOut`/`dflt`. The brief's `ExtractorImage` fields `enc`, `dec`,
   `encOut` and the size bound on `enc` are therefore gone.
   - The size bound (O-1) applies to the image's output instead: `witCap k = 2^(k+12)` words.
     Outputs are the only witnesses an extraction chain produces.
   - The input `w` is not capped. A witness longer than `2^60` words is simply not addressable.
2. **S4-A2.** `ExtractorImage.img_le : img.byteSize ≤ 2^20` is a structure field.
3. **S4-A3.** The memory map spans `2^64`, with the tape at `2^63`; v0.3's `TAPE_CAP` is
   replaced.
4. **S4-A4.** `HALT` returns a memory region. This matches the brief's "`none` on … rejecting
   halt", except that a rejecting halt no longer exists: an image traps.
5. **S4-A5.** The statement section is `L` itself, through a trusted 17-line encoding, not
   `Codec` imported into the trusted base. The round trip is proved in the Library by reduction
   to Codec's `pLayout_eLayout`.
6. **S4-A6.** `@[irreducible] extractorFuel`.
7. **S4-A7.** A finding: `B(k) ≥ 2^64` for `k ≥ 24`.
8. **S4-A8.** The prepared swap.
9. **`Extractor.lean` is 63 code lines** (target 60). `call` is kept as an explicit `match`
   rather than `Option.filter`/`elim`, for readability of the trusted text.

## Open questions for the orchestrator / user

1. **S4-A1 (decision).** Fixing `WitMid` to words is the sound choice. It changes the submitter
   interface: `KSF.toFun` takes words after round 0, and the submitter's structured witness lives
   only in their proofs. Please confirm. The alternative, a submitter-typed `WitMid` with a
   *machine-run* encoder and decoder, is the same thing with more trusted text.
2. **S4-A7 (user).** Should Q1's bound be tightened for `k ≥ 24`, so that one 64-bit secret is
   never enumerable, for example `B(k) = 2^(2k+16)` capped at `2^62`? The alternative is to
   document that relations with a single-word secret are unprotected at those classes. The
   benchmark (256-bit chain start) is unaffected.
3. **Stage 6/7.** The gate's `--computable` set becomes `P.extractor.img` (no `enc`/`dec`). The
   comparator must check that the image equals the claim's rendered literal (S4-A2), and the
   renderer needs an `extractor` image file in the claim JSON. The challenge stubs will name
   `firstMsgImage` for `P_triv`.
4. **`P_triv` (stage 8).** Its extractor is `firstMsgImage`, and `toy_extractMid` is the
   template for its `next` law: the baseline sends the same `eWit` serialisation in round 0.
5. **Design text (O-1).** The §4 item 3, §3.1, §6.5, §8 rows and §12 O-1 wording to patch in is
   given in S4-A1, S4-A2 and S4-A8. With this stage O-1 is resolved. The §8 table "est." values
   for `Machine.lean` and `Extractor.lean` become 109 and 63.

## Fix pass

This section applies `docs/reviews/S4-review.md` (ACCEPT WITH FIXES) as the coordinator decided, and
the Protocol swap. The golf pass (`docs/reviews/S4-golf.md`) had already shortened the Library and
Controls proofs; I re-read every file before editing. Nothing is committed and `docs/DESIGN.md`
is not edited. The new amendments are S4-A9 … S4-A13.

### Headline

- **Trusted lines.** `Machine.lean` 109 (unchanged), `Extractor.lean` 63 (unchanged: the new
  formula and docstrings fit), `Protocol.lean` 45 (was 47). The contract without `Compile.lean`
  and `Hash/` is now 447 code lines; the budget is 850. Counts are in `logs/S4/fix-loc-contract.log`.
- **S4-M1 (composed budget), as decided.** `extractorFuel k n := 2^(2k+16) / (n + 1)`.
  - Each of the `n + 1` calls gets an equal share. The whole extraction has at most `B(k)` steps
    (`composed_fuel_le`), so adding rounds buys nothing.
  - **What the controls show:**
    - **The mechanism still works.** `resumeImage` passes its search state through the witness
      words. At class 20 on 3 rounds (`2^54` steps per call), the composed `chain` returns the
      secret `9`, which the first call alone does not reach (`chain_finds`, `chain_round0`).
    - **The enumeration now fails (negative).** `chain_search_fails`: at class 20 a chained
      search whose calls each test at most as many candidates as a call has steps is **not** an
      extractor (`¬ SecureWith`). This holds for any injective `f`, any prover and errors, and
      any number `n` of free padding rounds. The `n + 1` calls cover at most `2^56` candidates,
      and the secret `2^64 − 1` lies beyond them.
    - **The per-call reading is kept as a record.** The review's `chain_secure` stays in
      `probes/s4/ChainBudget.lean`: with `2^54 − 3` candidates per call and `2^10` rounds, the
      per-call reading made accept-all "secure".
  - **Thresholds (S4-A9, superseding S4-A7).** One element is never enumerable for `k ≤ 23`.
    At `k = 24` it needs 1 step per candidate, which no loop achieves; from `k = 25` it needs at
    most `2^(2k−48)` steps per candidate. Two elements are never enumerable.
- **S4-M2 (rationale).** The `extractorFuel` docstring now states facts the controls prove:
  `oracle_sq` (the longest oracle squared is `16·B(k)`), `cube_gt` (cubic elimination never
  fits), `quadratic_fits` (O(N²) decoders fit up to `2^(k+6)` at 10 steps per operation).
  Quasi-linear decoders fit throughout. S4-A10 asks for open item O-11 (measure Guruswami–Sudan
  against `B(k)`).
- **The swap is applied (S4-A13).**
  - `Protocol.extractor : ExtractorImage`, and
    `Secure := SecureWith … (P.extractor.toExtractor k P.shape) P.ε`.
  - Migrated: `Controls/Toy.lean`, `Controls/CompileToy.lean`, `Controls/CompileFS.lean`. Hit and
    Negative build no protocol, so they did not change.
  - `toy_secure` (the full swapped `Secure`), `toy20_secure`, `rejectAll_not_secure`,
    `hit_secure` and every Stage 3 control are green. `probes/s4/ProtocolSwap.lean` is deleted.
- **Negative control for the swap (S4-m3).** `toy_spin_not_secure` (`Controls/Toy.lean`): with
  the looping image the toy is not `Secure`, at any class in range and any errors. So `Secure`
  depends on the image.

### Findings, one by one

| Finding | Action |
|---|---|
| **S4-M1** | Fuel split (trusted). Docstrings and headers say "B(k) is the total over the n + 1 calls; adding rounds buys nothing". Ported to `Controls/Extractor.lean`: `resumeImage`, `call1`…`call4`, `chain_finds`, `chain_round0`, `padShape`, `padShape_admissible`, `chainE` and its parts. Added: `chain_search_fails` (negative), `composed_lt_word`, `composed_lt_two_words`, `budget_24_25`. Library: `composed_fuel_le`, `extractorFuel_le`, `pow_le_extractorFuel`. S4-A7 is superseded by S4-A9; RESULT open question 2 (cap at `2^62`) is withdrawn. |
| **S4-M2** | `extractorFuel` docstring rewritten (S4-A10). `oracle_sq`, `cube_gt`, `quadratic_fits` are controls. O-11 is requested. |
| **S4-m1** | Ported from `probes/s4/BruteNonVacuous.lean`: `clmul_lt`, `bruteHash_lt`, `bruteHash_top`, `bruteHash_ne_top`, `sTop`, `brute_nonvacuous`. `brute_extractMid_nil`'s docstring now cites `brute_nonvacuous`. |
| **S4-m2** | Thresholds restated in S4-A9 and in `word_le_budget`/`budget_24_25`. |
| **S4-m3** | Swap applied, including `CompileFS.lean`. `toy_not_secure_of` and `toy_spin_not_secure` are in `Controls/Toy.lean`; `nil_not_relK` is in `Library/Extractor.lean`. `Security.lean` header: S4-A11, diff below. |
| **S4-m4** | `Contract/Extractor.lean` header reworded as proposed (S4-A12). |
| **S4-m5** | `witCap` docstring and header now say "interface cap … four maximum-size oracles" (S4-A12). |
| **S4-m6** | "steps", not "cycles" (S4-A12, a DESIGN wording change). |
| O1–O3 | No action. |

### S4-A11: the one comment-only edit to `Contract/Security.lean`

```diff
 `Bad`'s `∃ w` ranges over the *next-stage* witness, which the extractor maps backwards.
-At L1 the extractor is unconstrained, so `RbrKS` is equivalent to RBR *soundness*
-(`Library/RbrSound.lean`, A2-M2): records are labelled "RBR-sound".
+For an unconstrained extractor `RbrKS` is equivalent to RBR *soundness* (`Library/RbrSound.lean`,
+A2-M2); `Protocol.Secure` names the submitted image (`Contract/Extractor.lean`, Q1), to which the
+collapse does not apply.
 -/
```

No declaration changed; the code-line count stays 55. The root `Contract.lean` says so and now
lists the files in reading order (`Machine`, `Extractor`, then `Protocol`).

### Other edits

- **Library (`Library/Extractor.lean`).**
  - New: `nil_not_relK`, `run_none_of_le` (less fuel keeps a failing run failing), and the fuel
    lemmas.
  - The refinement lemmas now name `extractorFuel k n`.
  - `firstMsg_extractMid` takes `hf : 8 ≤ extractorFuel k n`, which `pow_le_extractorFuel`
    discharges for `k ≥ 1`, `n ≤ roundCap`.
  - It imports `Contract.Protocol` (for `relK`).
- **`brute_none`** now holds for every fuel `f ≤ 2^56 = B(20)` (via `run_none_of_le`). So
  `brute_extractMid_nil` holds for every round count.
- **`long_extractMid`** takes `n ≤ roundCap`, since a protocol with more rounds would have a fuel
  below 4. `copy_run`/`copy_run0` run at `extractorFuel 20 2`.
- **Golf options.**
  - Declined: `execute` via `Option.bind` and `call` via `Option.filter`. The explicit `match`
    names the fault case and the cap check, which reads better for the trusted text.
  - `unpack` is kept: `scripts/render-challenge.py` emits `unpack bits len literal` into rendered
    challenges.
  - The golf's `fun_induction` proof of `execute_mono` is kept.
- **Probes kept compiling.**
  - `ChainBudget.lean` is reduced to part (b) (`chain_secure`) and the per-call arithmetic, on
    top of the ported definitions.
  - `FuelArith.lean` reads `B(k)` as `extractorFuel k 0`.
  - `SwapNegative.lean` keeps `toy_long_not_secure`; the rest moved.
  - `ReviewAxioms.lean` has updated names and covers the new controls.
  - `BruteNonVacuous.lean`, `MachineEdge.lean` and `TrustedClosure.lean` are unchanged and green.
  - `ProtocolSwap.lean` is deleted.

### Builds and checks

- **`lake build` of the roots.** `lake build RecursionFast.Contract RecursionFast.Library
  RecursionFast.Controls RecursionFastBridge gate axiomaudit` is green, in 1 min 28 s
  (`logs/S4/fix-build-modules.log`). The Compile controls take 64 s of it. Module times:
  `Library.Extractor` 5.2 s, `Controls.Extractor` 11 s, `Controls.Toy` 4.2 s.
- **The default `lake build`** (globs) builds everything above, but fails on **Stage 6a's
  in-progress `Controls/Chain.lean`** (a `Decidable` instance for its own gadget statement;
  `logs/S4/fix-build-default.log`). That file is not part of this stage, and nothing in it uses
  the extractor.
- **Axiom audit** (`lake exe axiomaudit`, `logs/S4/fix-axiomaudit.log`): **PASS**.
  - Machine 131, Extractor 32, Protocol 61, Library.Extractor 104, Controls.Extractor 83,
    Controls.Toy 33.
  - Library.Extractor counts the golf's 8 generated `execute.*` lemmas, plus 5 new lemmas.
- **`#print axioms`** (`probes/s4/ReviewAxioms.lean`, `logs/S4/fix-axioms.log`).
  - `toExtractor` uses `[propext, Quot.sound]`.
  - `Protocol.Secure`, `toy_secure`, `toy_spin_not_secure`, `chain_round0` and
    `chain_search_fails` use `[propext, Classical.choice, Quot.sound]`.
  - Nothing else appears.
- **Hygiene, vendor and closure.**
  - `check-hygiene.sh` reports OK.
  - `check-vendor.sh` reports byte-identical.
  - The closure is unchanged: 205 declarations, 930 lines, 0 theorems
    (`logs/S4/fix-trusted-closure.log`).

### Argued points

1. **The even split penalises protocols whose extraction work sits in one round.** Such a
   protocol is, typically, a decoder at round 0. With `n` rounds that call gets `B(k)/(n+1)`
   even if the other calls need little. A protocol with a few rounds loses little (`n ≤ 15`
   costs at most a factor of 16). One at the round cap keeps about `2^(2k+1)` per call, which
   is still `2^41` at class 20.
   - The alternative is a budget threaded through the calls (the contract counting steps
     across calls). It is sound but needs more trusted text.
   - I implemented the decided split and record this for the user. It changes no statement.
2. **`chain_search_fails` is stated for chained searches that test at most one candidate per
   step.** A bit-sliced test can check up to 64 candidates per pass of a circuit.
   - The robust statement is the step bound `composed_fuel_le`: `B(20) = 2^56` steps against
     `2^64` candidates, that is 256 candidates per step.
   - The control is the faithful adaptation of the review's `chain_secure` model.

### Follow-up: the submitter declares the split (S4-A14)

This replaces the even split above. The total is unchanged, so the thresholds of S4-A9 are
unchanged.

- **Trusted change.** `ExtractorImage k n` has `fuel : Fin (n + 1) → ℕ` and
  `fuel_le : (List.ofFn fuel).sum ≤ extractorBudget k`, with `extractorBudget k = 2^(2k+16)`.
  `toExtractor` runs each call with its declared fuel: `extractMid m` with `fuel m.castSucc`,
  `extractOut` with `fuel (Fin.last n)`. The division is gone. Docstring: "the submitter chooses
  how the total budget `B(k)` is split over the `n + 1` calls (a round-0 decoder may take almost
  all of it); the total, not the split, is what the contract bounds".
- **`Protocol`.** `extractor : ExtractorImage k n`; `Secure` uses
  `P.extractor.toExtractor P.shape`.
- **Trusted lines.** `Machine.lean` 109, `Extractor.lean` 65, `Protocol.lean` 45. The contract
  without `Compile.lean` and `Hash/` is 449 code lines (`logs/S4/split-loc-contract.log`).
- **Library.** `ExtractorImage.composed_fuel_le` is now immediate from `fuel_le`. Also
  `fuel_le_budget`, two ready-made splits (`even`, with `even_fuel_ge`; `atZero`, all on the
  decoding call), and `firstMsgImage k n` (= `atZero`). `firstMsg_extractMid` is stated for any
  `E` with `E.img = firstMsgImg` and at least 8 steps of fuel in the call.
- **Controls.**
  - **Splits used.** The toy, `cmpToy` and `pfs` use `firstMsgImage` (all on round 0). The
    `copy`, `spin`, `long`, `brute` and `resume` images use `even`.
  - **Any split.** `spin_extractMid` and `brute_extractMid_nil` hold for any image with that
    code, whatever the split.
  - **`chain_search_fails`** is now stated for **any** image at class 20 (any declared split)
    and a chained search whose call before round `j` tests `T j ≤ c · fuel j` candidates with
    `c < 256`, which covers bit-slicing. The calls cover at most `255·2^56 < 2^64 − 1`
    candidates, so the composed search is not an extractor, on any number of free padding
    rounds. Reaching `2^64` would take 256 candidates per step.
  - **The mechanism** (`chain_finds`, `chain_round0`) is unchanged: resumable image, even split,
    `2^54` steps per call.
- **Checks.**
  - The roots plus `RecursionFastBridge gate axiomaudit` build green
    (`logs/S4/split-build.log`, 2 min 15 s after the `Protocol` docstring edit). The full default
    `lake build` is green too, now that Stage 6a's `Chain.lean` builds.
  - The axiom audit reports **PASS**: Contract.Extractor 34, Library.Extractor 106,
    Controls.Extractor 86.
  - `check-hygiene.sh` and `check-vendor.sh` pass, and the closure is unchanged (205 / 930 / 0).
  - `#print axioms` (`logs/S4/split-axioms.log`): `toExtractor` uses `[propext, Quot.sound]`.
    `chain_finds`, `chain_round0`, `chain_search_fails`, `toy_secure` and `Protocol.Secure` use
    the standard three.
  - All `probes/s4/*.lean` compile (adapted to the field).
- **The argued point 1 above is resolved.** The submitter now puts the budget where the work is.

# S4 review: the bounded extractor (Q1) and the trimmed machine

**Verdict: ACCEPT WITH FIXES.** The trusted code does what it says.

- **Each call is bounded.** I found no path by which work outside the fuel reaches one call's
  output.
  - **The input tape** is built from contract definitions alone. No submitter term is on it.
  - **The output** is either words the image left in memory, or zero-filled tables decoded by
    a total, trusted decoder.
  - **A failed call** (a fault, a trap, fuel exhaustion or an over-long output) yields `[]`.
    Before round 0, `[]` is never in `relK`.
- **The machine trim** deletes code and changes nothing else.
  - A token-level diff against v0.3 finds the kept definitions identical.
  - The only changes are the declared ones: the memory check, `HALT`, `execute`/`run`,
    `initState`, and `TAPE_BASE`.
- **Hygiene holds.**
  - `run` is structurally recursive. Every declaration uses only the standard axioms.
  - The vendored code is byte-identical.
  - The closure measurement reproduces exactly: 205 declarations, 930 lines, 0 theorems.
  - All ten control images re-assemble from their `.S` sources to the literals in Lean.

There are two major findings. Both are about what the bound *means*, and neither requires a
change to the trusted code.

- **S4-M1.** The fuel bounds each call, but knowledge is delivered by the composed extractor:
  `n + 1` calls that can pass a computation along through the witness words.
  - The composed budget is `(n+1)·B(k) < 2^(2k+31)`. It is not `B(k)`.
  - Rounds are free: empty challenge rounds are admissible and carry no error.
  - So a one-word (64-bit) secret is enumerable **at every class**, not only for `k ≥ 24`,
    for any candidate test of at most `2^(2k−34)` steps (64 at `k = 20`).
  - S4-A7 is therefore wrong. The remedy the RESULT proposes (cap `B` at `2^62`) would not
    work.
  - Kernel-checked: `chain_round0`, `chain_secure`.
- **S4-M2.** The trusted docstring of `extractorFuel` makes two false claims:
  - "quadratic in the oracle length": the square of the longest oracle is `16·B(k)`;
  - "admits decoding by Gaussian elimination": cubic elimination exceeds `B(k)` at every class.

  The same rationale is in the user's Q1 text.

There are six minor findings (S4-m1 … S4-m6).

Date: 2026-10-14. Scope (sha256 prefixes at review time, `logs/S4-review/reviewed-sha256.txt`):

| File | sha256 prefix |
|---|---|
| `Contract/Machine.lean` | `f8f7c27d` |
| `Contract/Extractor.lean` | `140b244a` |
| `Library/Extractor.lean` | `f6d829f6` |
| `Controls/Extractor.lean` | `8c518dff` |
| `probes/s4/ProtocolSwap.lean` | `4eabaec1` |
| `docs/stages/S4-RESULT.md` | `fdb61acb` |

- `Library/` and `Controls/Extractor.lean` are under concurrent golf. I cite declarations by
  name and statements only.
- I edited nothing under `RecursionFast/`.
- New probes are under `probes/s4/`. Their logs are under `logs/S4-review/`.

---

## Major findings

### S4-M1: the fuel bound is per call; the knowledge guarantee is for `n + 1` calls

**Where.**

- `ExtractorImage.toExtractor`, `ExtractorImage.call` and `extractorFuel` (`Contract/Extractor.lean`).
- `DESIGN-AMENDMENTS.md` S4-A7.
- S4-RESULT, open question 2.
- The docstrings of `extractorFuel_lt_word`, `word_le_extractorFuel` and `brute_extractMid_nil`,
  and the "Negative, Q1" bullet of the `Controls/Extractor.lean` header.
- DESIGN §4 item 3: "accept-all would need a provable preimage finder within `B(k)`".

**Problem.**

1. **The laws are per round.** RBR knowledge soundness produces a witness through the backward
   chain of `n` `extractMid` calls and one `extractOut` call. This chain is
   `Library/RbrSound.lean`'s `chain`, which `chain_extracts` turns into a witness of `relIn`.
2. **The contract bounds each call, not the chain.** Each call has `B(k) = 2^(2k+16)` steps.
   After round 0 the witness is a list of words, and `KSF.toFun` is the submitter's. So the
   state function can say "the search has reached candidate `c`", and each call can continue
   the previous call's search.
3. **Rounds are free.** An empty challenge round `.chal 0 []` is admissible. It has one possible
   value, so it adds no error, and the verifier does nothing in it. A protocol can therefore pad
   to `n = roundCap = 2^14` at no cost and get an extraction budget of
   `(2^14 + 1)·B(k) < 2^(2k+31)`. That is `2^71` at `k = 20` and `2^87` at `k = 28`.

**Consequences.**

- **One-word secrets.** A secret of one word is enumerable at every class in range. At `k = 20`,
  2^10 calls of the existing brute-force loop (`2^54 − 3` candidates each) cover `2^64`
  candidates. At the round cap, the chain enumerates `2^64` candidates for any test of at most
  `2^(2k−34)` steps (64 at `k = 20`, `2^22` at `k = 28`).
- **S4-A7 is wrong.** Its claim "the rationale holds for `n_w ≥ 2`, **or for `k ≤ 23`**" is
  false: the `k ≤ 23` clause does not hold.
- **The proposed remedy fails.** The RESULT asks whether to cap `B` at `2^62` (open question 2).
  That cap would not protect one word: with `2^14` rounds the total is still `2^76`.
- **Two words are safe.** The `n_w ≥ 2` half of the rationale survives: `2^87 < 2^128`.
- **The benchmark is unaffected.** Its witness is a 256-bit chain start.

**Probe.** `probes/s4/ChainBudget.lean` (kernel-checked; log `logs/S4-review/chainbudget.log`).

- **(a) The real machine and the real `toExtractor`, at class 20.** `resumeImage`
  (`probes/s4/asm/resume.S`, 34 instructions) is `brute.S` made resumable: it keeps its
  `[flag, c]` state in the witness section.
  - `extractOut` tries candidates 0–3 and returns `[0, 4]` (`call1`).
  - `extractMid 2` tries 4–7 and returns `[0, 8]`.
  - `extractMid 1` finds `9`, the preimage of `x₀ = 0xc3` (`secret_9`).
  - **`chain_round0`**: `chain (resumeImage.toExtractor 20 sh3) sC3 tr () 0 =
    decTables [32] [1, 9]`. The library's composed extractor returns the secret. The only call
    that starts from nothing gives up at 4 (`chain_finds`).
- **(b) The laws, in general.** **`chain_secure`** holds for every bijection `f` of words, every
  shape `sh : Fin n → Round`, and every `T` with `(n+1)·T ≥ 2^64`. It states that
  `SecureWith {(x, c) | f c = x} univ trivialProver acceptAll (chainE f T n sh) 0` holds:
  - perfect completeness;
  - `RbrKS` at error 0, since no challenge is bad (`chain_noBad`);
  - the error cap.

  Each call of `chainE` tests `T` candidates. An `example` instantiates the hypotheses with
  2^10 empty challenge rounds (`padShape`, which is admissible: `padShape_admissible`) and
  `T = 2^54 − 3`.
- **(c) The arithmetic.**
  - `rounds_suffice_20`: `2^64 ≤ (2^10 + 1)(2^54 − 3)` and `2^10 ≤ roundCap`.
  - `composed_budget_lt`: `(n+1)·B(k) < 2^(2k+31)` for `n ≤ roundCap`.
  - `composed_budget_ge`: `2^64·2^6 ≤ (roundCap+1)·B(k)` for `k ≥ 20`.

**Fix.** These are documentation changes, plus controls so that the composed reading is checked
in CI.

1. **S4-A7.** Replace the "Fact" and "Q1 rationale wording" bullets with:

   > The fuel bounds one call. Knowledge is delivered by the composed extractor
   > (`Library/RbrSound.lean`'s `chain`, `n + 1 ≤ 2^14 + 1` calls). Its calls may pass state
   > through the witness words (`probes/s4/ChainBudget.lean`), so it runs for at most
   > `(n+1)·B(k) < 2^(2k+31)` steps. Rounds cost nothing for this purpose (`.chal 0 []`).
   > "Excludes brute force ≈ `2^(64·n_w)`" holds for `n_w ≥ 2` at every class. It holds for
   > `n_w = 1` at no class: one call enumerates `2^64` from `k = 25`, and the chain does so
   > from `k = 20` for any test of at most 64 steps.

2. **RESULT open question 2.** Withdraw the cap proposal. If the user wants one-word secrets
   protected, the bound must cover the whole extraction. The option is a per-call fuel of
   `2^(2k+16) / (n+1)`, which is a trusted change to `call`/`toExtractor`. Its cost: honest
   round-0 decoding budgets shrink by up to `2^14`. I recommend not doing this. Instead, state
   the guarantee for the composed extractor, and keep benchmark witnesses at two or more `K`
   elements.
3. **Docstrings.**
   - `Contract/Extractor.lean` header: add "The bound is per call; RBR extraction composes
     `n + 1` calls, which may pass state through the witness words, so the knowledge guarantee
     is for `(n+1)·B(k)` steps."
   - `extractorFuel_lt_word` and the "Negative, Q1" header bullet: add "in one call".
   - `word_le_extractorFuel`: say "one call" (see S4-m2).
4. **Controls.** Port `resumeImage`, `call1`…`call4`, `chain_round0`, `composed_budget_lt` and
   `composed_budget_ge` into `Controls/Extractor.lean`. They would be the first control in which
   `extractOut`'s output feeds the chain; the toy's state function ignores the witness after
   round 0.
5. **DESIGN §4 item 3.** Change "within `B(k)`" to "within `(n+1)·B(k) < 2^(2k+31)` steps,
   `n + 1` calls of the image". Use the paragraph below.

### S4-M2: `extractorFuel`'s docstring makes two false claims

**Where.** The `extractorFuel` docstring (trusted): "quadratic in the oracle length; admits
decoding by Gaussian elimination". The same text is in DISCUSSION Q1: "Quadratic admits
Berlekamp–Welch via Gaussian elimination".

**Problem.**

1. **Not quadratic in the oracle length.** The longest admissible message oracle has `2^(k+10)`
   elements (`Round.Admissible`), and its square is `16·B(k)` (`oracle_sq`). `B(k)` is
   `2^16·(2^k)²`: quadratic in the witness-cell cap, or in `2^(k+8)`.
2. **No Gaussian elimination.** Gaussian elimination is cubic. Even on a system with only as
   many unknowns as the witness has cells, `(2^k)³ > B(k)` for every `k ≥ 17` (`cube_gt`), at
   one step per field operation.
3. **What fits.** A `K` multiply-add costs about 10 steps on this ISA: `clmul`, `clmulh`, two
   folds by `0x1b`, and loads. Hence:
   - O(N²) decoders, such as Berlekamp–Massey or Euclid-based Berlekamp–Welch, fit only for
     `N ≲ 2^(k+6)`;
   - quasi-linear decoders (additive FFT, half-GCD) fit for every admissible oracle;
   - Guruswami–Sudan, which Q1 relies on for the Johnson regime, is not shown to fit at the
     codeword lengths the design intends.

A bound that is too small is not a soundness hole: it hurts only honest submitters. But
the contract constant is justified in trusted text by a false claim, and that claim hides a
feasibility risk for ranked entries.

**Probe.** `probes/s4/FuelArith.lean`: `oracle_sq`, `cube_gt`, `k24_single_call` (log
`fuelarith.log`).

**Fix.**

1. Rewrite the docstring:

   > `2^(2k+16)` steps per call: `2^16` times the square of the witness-cell cap `2^k` (a
   > sixteenth of the square of the longest admissible oracle). At about 10 steps per
   > `K` multiply-add it admits O(N²) decoding of codewords up to about `2^(k+6)` elements, and
   > quasi-linear decoding of every admissible oracle; it does not admit cubic Gaussian
   > elimination (`k ≥ 17`). It excludes enumerating `2^128` candidates even over the `n + 1`
   > calls of an extraction.

2. Add an open item to DESIGN §12 (owner: user / library): measure the step count of the
   intended Johnson-regime decoder (CompPoly's Guruswami–Sudan) at `k = 20` on the intended
   codeword length, against `B(20) = 2^56`. Correct Q1's rationale wording when DESIGN §4
   is patched.

---

## Minor findings

### S4-m1: the Q1 negative control's hypothesis is never shown satisfiable

**Where.** `brute_none` and `brute_extractMid_nil` (`Controls/Extractor.lean`).

**Problem.**

- **Non-vacuity is asserted, not proved.** Both theorems assume `∀ c < 2^54, bruteHash c ≠ x₀`.
  `brute_extractMid_nil`'s docstring says such `x₀` exist and have preimages, "`bruteHash` is
  injective below `2^60`", but no theorem proves it. (In fact `bruteHash` is a bijection of
  words: `0x1b` is a unit mod `x^64`.)
- **Why it matters.** Without non-vacuity the control could be vacuous. And unless the `x₀` has
  a preimage, the empty witness is not attributable to the fuel.

**Probe.** `probes/s4/BruteNonVacuous.lean`.

- `clmul_lt` gives the degree bound `a < 2^p, b < 2^q ⇒ a ⊗ b < 2^(p+q)`.
- `bruteHash_top`: `bruteHash (2^63) = 2^63`.
- `bruteHash_ne_top`: no `c < 2^54` maps to `2^63`.
- `brute_nonvacuous`: at `x₀ = 2^63` a preimage exists, yet
  `(bruteImage.toExtractor 20 sh2).extractMid 1 sTop tr2 w3 = []`.

**Fix.** Move these declarations, with their helpers `bruteHash_lt` and `sTop` (≈ 40 lines),
into `Controls/Extractor.lean`. Replace the
docstring's injectivity sentence with "`brute_nonvacuous`: `x₀ = 2^63` has the preimage `2^63`
and none below `2^54`".

### S4-m2: S4-A7's single-call boundary is `k ≥ 25`, not `k ≥ 24`

**Where.** S4-A7, `word_le_extractorFuel` ("can be enumerated at up to `2^(2k−48)` steps per
candidate").

**Problem.**

- **At `k = 24` the budget is one step per candidate.** `2^(2k−48) = 1`, so the call would have
  to test each candidate in a single step, loop control included.
- **No loop does that.** Even fully unrolled, each candidate needs at least a test and a
  branch, and `B(24) < 2·2^64` (`k24_single_call`).
- **So the single-call threshold is `k = 25`** (4 steps per candidate). An unrolled
  `clmul`/`beq`/`addi` loop fits; `brute.S`'s 4-step loop, plus its 15 set-up and halt steps,
  just misses. In practice the threshold is `k ≥ 26` for any non-trivial test. S4-M1
  supersedes this for the composed extractor.

**Fix.** Make the docstring and S4-A7 say "one call, from `k = 25`, at most `2^(2k−48)` steps per
candidate including loop control".

### S4-m3: the prepared swap is incomplete, and has no negative control

**Where.** S4-RESULT, "The Protocol swap"; `probes/s4/ProtocolSwap.lean`.

**Problem.** The swap list misses three things:

1. **`Controls/CompileFS.lean`.** Its `pfs : Protocol 20` (Stage 3 fix pass, newer than the
   RESULT) sets `WitMid := …` and `extractor := {…}`. It would not compile after the swap.
2. **`Security.lean`'s reading guide** (trusted, docstring only) says "At L1 the extractor is
   unconstrained, so `RbrKS` is equivalent to RBR soundness … records are labelled
   'RBR-sound'". After the swap, `Protocol.Secure` fixes the extractor to the image, so the
   collapse `SF.rbrKS_of_rbr` no longer applies to it. An auditor reading the trusted header
   would conclude the opposite of Q1.
3. **A negative control.** `toy'_secure` shows the swapped `Secure` can hold. Nothing shows that
   it depends on the image:
   - `rejectAll_not_secure` survives unchanged; its proof never touches the extractor;
   - `hit_secure` and `acceptAll_*` are stated over `SecureWith` or arbitrary extractors.

**Probe.** `probes/s4/SwapNegative.lean` (kernel-checked):

- `toy_not_secure_of`: for any image whose round-0 output on the honest transcript of
  `(triv, 0)` is not a witness, the toy with that image is not `Secure`, whatever its errors.
- `toy_spin_not_secure` (every `k` in range) and `toy_long_not_secure` (class 20) are its
  instances, for the looping image and the over-long output.
- `nil_not_relK`: `[]` is never in `relK`. S4-A1 claims this, but no lemma proved it.

`ProtocolSwap.lean` itself builds green (`protocol-swap.log`). With `toFun` written by
`Fin.cases`, `Mid n j` was expressive enough for the toy.

**Fix.** With the swap:

- add `Controls/CompileFS.lean` to step 3;
- in step 1, reword `Security.lean`'s guide: "for an unconstrained extractor `RbrKS` is
  equivalent to RBR soundness (`Library/RbrSound.lean`, A2-M2); `Protocol.Secure` names the
  submitted image (`Contract/Extractor.lean`, Q1), to which the collapse does not apply";
- move `nil_not_relK` to `Library/Extractor.lean`, and `toy_not_secure_of` and
  `toy_spin_not_secure` to `Controls/Toy.lean`.

### S4-m4: the header overstates where the image must succeed

**Where.** The `Contract/Extractor.lean` header ("the image must succeed within the fuel exactly
where the `next`/`full` laws ask for a witness"); Q1 ("fuel exhaustion gives the default
witness, which fails the law").

**Problem.**

- **True before round 0.** There `[]` fails `relK`.
- **Not true after round 0.** There the submitter's state function decides, and it may accept
  `[]`. A failing call at round `j ≥ 1` is then not caught by that round's law. It is caught
  only through round 0, which must still produce a witness from whatever reached it.

This is not a soundness gap, but the trusted header is the text a human audits.

**Fix.** Replace the sentence with: "the laws force a witness in `relK` only before round 0,
where `[]` fails (`nil_not_relK`); after round 0 the submitter's state function says what an
output must satisfy, `[]` included."

### S4-m5: `witCap` is an interface limit, not a security bound; say so

**Where.** `witCap`, S4-A1 "Size bound (O-1)".

**Problem.**

- **It bounds no information.** An output can contain only:
  - the input tape (contract data);
  - the image's data (≤ 2^17 words, the same for every statement);
  - at most `B(k)` stored words;
  - zeros.

  So the cap bounds no information the fuel does not already bound. The round-0 decoder's
  expansion of a height word into zero cells adds no information either, and `relK` caps the
  cells (`decTables_short`).
- **What it does do.** It limits an honest state after round 0 to `2^(k+12)` words: four
  maximum-size oracles. An RBR state that must carry more decoded oracles from later rounds
  does not fit.

**Fix.** In S4-A1 and DESIGN §6.5, call it an interface cap ("the largest intermediate witness
an extraction can pass between calls"), and note the four-oracle limit for submitters. No code
change is needed, unless the user wants a larger cap.

### S4-m6: "cycles" in the design, "steps" in the contract

**Where.** DESIGN §4 item 3 and Q1 ("`B(k) = 2^(2k+16)` cycles").

**Problem.** The contract counts instruction steps. Every instruction is one step: `div`,
`clmul` and `ECALL` included. There is no cost model.

**Fix.** Use "steps" when patching DESIGN §4.

### Observations (no action)

- **O1.** 316 of the 930 closure lines are ZiskAccel's CSR model. The closure reaches it only
  through `execInstrBr`'s `CSRS` arm, and that arm is dead:
  - `ordinaryStep` makes it a fault;
  - `decodeInstruction` never produces it (opcode `0x73` decodes only to `ECALL`:
    `fence_ebreak_csr`).

  An auditor may skip it.
- **O2.** `Machine.lean` lines 112 and 157 exceed 100 characters. Both are verbatim from v0.3,
  so keep them.
- **O3.** The image's 2^17 data words are fixed advice. A Hellman time–memory trade-off for a
  64-bit function with 2^17 words needs about 2^94 steps, above the composed budget, so the
  advice does not change S4-M1's numbers.

---

## What the fuel bound guarantees (for DESIGN §4 item 3)

> Each extractor call runs the submitted image (≤ `2^20` bytes, the same for every statement) for
> at most `B(k) = 2^(2k+16)` steps on a tape the contract builds from `(j, L, x, transcript
> prefix, next witness)` alone; its output (≤ `2^(k+12)` words, else empty) is decoded by trusted
> code that adds only zeros. The laws force a valid witness only before round 0, where `[]` fails
> `relK`, so knowledge comes from the composed extractor: `n + 1 ≤ 2^14 + 1` calls that may pass
> state through the witness words, i.e. at most `(n+1)·B(k) < 2^(2k+31)` steps (`2^71` at
> `k = 20`, `2^87` at `k = 28`). Brute force is therefore excluded for witnesses of two or more
> `K` elements at every class, and for one `K` element at no class once its test costs at most
> `2^(2k−34)` steps (empty challenge rounds make `n` free). `B(k)` admits O(N²) decoding up to
> about `2^(k+6)` elements and quasi-linear decoding of every oracle, not Gaussian elimination.

---

## Coverage

| Question | Answer | Evidence |
|---|---|---|
| 1. Is every tape word a function of contract data? | Yes. `extractorTape` → `frame`, `Layout/Chip/Table.words`, `Round.words` → `Round.tapeWords`, `toWord`, `K.bits`, `E.toWords`: all trusted, no submitter term. Shapes come from the contract menu. | reading; `tape_roundTrip`, `unframe_extractorTape` |
| 1. `decTables` / directory: trusted and total? | `decTables` is structural recursion on the column list. Directory parsing happens in the image (inside the fuel); `unframe` is Library only. | `ReviewAxioms` (no `WellFounded.fix`) |
| 1. Output aliasing and defaults; can the cap be bypassed? | After round 0 the output words are the witness, so no expansion. Before round 0, missing cells are zero, which is harmless (S4-m5). The cap is an exact length check (`long_*`). | `halt_wraps`, `decTables_short` |
| 1. Default witness | `[]` ∉ `relK` for every statement. The toy's `full` ignores the witness by design. The image is load-bearing through round 0's `next`. | `nil_not_relK`, `toy_spin_not_secure` |
| 1. Memory between calls | Each call is `execute img fuel (initState img t)`, so there is no shared state. | `run_fresh` (rfl) |
| 1. `HALT` `a0`/`a1` | `a0` must be 8-aligned. `a1` is arbitrary: the output may wrap past `2^64` (to the tape end, then data word 0) and may cover the tape. Code is never visible. | `halt_misaligned`, `halt_wraps`, `code_invisible` |
| 1. Faults, traps, fuel → `none` → `[]` | Yes | `spin_*`, `ecall_trap`, `tape_readonly`, `sb_tape`, `sd_wrapped`, `fence_ebreak_csr` |
| 1. Does the bound bind? | Per call: yes. Per extraction: `(n+1)·B(k)`, **S4-M1** | `ChainBudget` |
| 2. Kept semantics vs v0.3 | Identical: `decodeInstruction`, `wordResult`, `clResult`, `memAccess`, `fetch`, `unpack`, `byteSize`, `CODE_BASE`. `ordinaryStep` differs only in the memory check. The header's removal list is complete. | `machine-diff.py` → `machine-diff.log` |
| 2. `run` total | Structural recursion on fuel; not `partial`, not `unsafe` | `ReviewAxioms` |
| 2. Code/tape overlap; tape vs memory; unmapped loads | Harvard. Stores land below `2^63` (a sub-word store at `2^63 − 1` is fine; at `2^63`, or wrapped `0 − 8`, it faults). Loads anywhere read zero beyond data or input. Tape words `≥ 2^60` are unaddressable, which only loses information. | `MachineEdge` |
| 3. Brute-force arithmetic | Correct for one call. The single-call boundary is `k = 25` (**S4-m2**); the composed boundary is every class (**S4-M1**). | `FuelArith`, `ChainBudget` |
| 3. Is the control about the loop, and `decide`-free? | Yes (`brute_iter`, `brute_loop`). Non-vacuity was missing (**S4-m1**). | `BruteNonVacuous` |
| 3. One-`K` witness | Not protected at any class for tests of at most `2^(2k−34)` steps (paragraph above) | `composed_budget_ge` |
| 4. `Secure` non-vacuous after the swap | Positive: `toy'_secure`. Negative: `rejectAll_not_secure` (unchanged), plus the new `toy_spin_not_secure`. | `ProtocolSwap`, `SwapNegative` |
| 4. Fuel class | `P.extractor.toExtractor k P.shape` with `k` the structure parameter, not a free variable | `ProtocolSwap.Protocol'.Secure` |
| 4. Is `Mid` expressive enough? | Yes: words are arbitrary, and the toy's KSF needed only `Fin.cases`. Outputs are capped at `2^(k+12)` words (S4-m5). | `toyKSF'` |
| 4. Is the swap list complete? | No: `CompileFS.lean`, the `Security.lean` guide, and no negative control (**S4-m3**) | grep; `SwapNegative` |
| 5. Axioms | 43 S4 declarations plus every probe: within `propext`, `Classical.choice`, `Quot.sound` | `axioms.log`, probe logs |
| 5. Forbidden constructs; `@[irreducible]` | None (`check-hygiene.sh` OK). The kernel unfolds the fuel (`decide +kernel`: `extractorFuel 20 = 2^56`, `extractorFuel 28 = 2^72`). The gate does not inspect the attribute. | `ReviewAxioms` |
| 5. Imports | `Machine`: Lean core, vendored `Execution`/`Decode`, `Field`. `Extractor`: `Machine`, `Security`, `Layout`. | reading |
| 5. Vendored code | Byte-identical to `6810fc1` | `check-vendor.log` |
| 5. Closure 205 / 930 | Reproduced: 205 declarations, 930 lines, 0 theorems (900 roots) | `trusted-closure.log` |
| 5. Line budget | `Machine` 109, `Extractor` 63; contract without `Compile`/`Hash` 449 ≤ 850 | `loc.log` |
| 5. Docstrings state meaning | **S4-M2**, **S4-m1**, **S4-m4** | — |
| 5. Trusted code that belongs in Library | None (`unpack` is used by `render-challenge.py`) | grep |
| Controls ↔ sources | All 10 `tests/asm/*.S` re-assemble to their `.bin` and to the Lean literals. So do the review's 9 images. | `asm-check.log` |

## Probes (all under `probes/s4/`; run with `lake env lean <file>` or `python3 -I <file>`)

| Probe | Shows | Log |
|---|---|---|
| `ReviewAxioms.lean` | `#print axioms` on the trusted definitions, the refinement interface and every control; `execute`, `decTables`, `frame` and `run` are not well-founded; the kernel sees through `@[irreducible]` | `axioms.log` |
| `ChainBudget.lean` (+ `asm/resume.S`) | **S4-M1**: `chain_round0`, `chain_finds`, `chain_secure`, `chain_noBad`, `padShape_admissible`, `composed_budget_lt`/`_ge`, `rounds_suffice_20` | `chainbudget.log` |
| `FuelArith.lean` | **S4-M2**, **S4-m2**: `oracle_sq`, `cube_gt`, `k24_single_call` | `fuelarith.log` |
| `BruteNonVacuous.lean` | **S4-m1**: `clmul_lt`, `bruteHash_top`, `bruteHash_ne_top`, `brute_nonvacuous` | `brutenonvacuous.log` |
| `SwapNegative.lean` | **S4-m3**: `toy_not_secure_of`, `toy_spin_not_secure`, `toy_long_not_secure`, `nil_not_relK` | `swapnegative.log` |
| `MachineEdge.lean` (+ `asm/edge_*.S`) | `halt_wraps`, `code_invisible`, `sb_below_tape`, `sb_tape`, `sd_wrapped`, `fence_ebreak_csr`, `decTables_short`, `run_fresh` | `machineedge.log` |
| `machine-diff.py` | Token diff of every kept or changed `Machine.lean` definition against v0.3 | `machine-diff.log` |
| `asm-check.py` | Re-assembles `tests/asm/*.S` and `probes/s4/asm/*.S`; compares them with the `.bin` files and the Lean literals | `asm-check.log` |
| `TrustedClosure.lean`, `ProtocolSwap.lean` (the author's) | Re-run: 205 / 930 / 0, and `toy'_secure` green | `trusted-closure.log`, `protocol-swap.log` |

Build: `lake build RecursionFast.Contract.Extractor RecursionFast.Library.Extractor
RecursionFast.Controls.Extractor` is green. I did not run the full `lake build`, because Stage 3's
fix pass was editing in parallel. The probes take 6–24 s each.

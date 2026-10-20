# V3-S2R handoff review: the rules handoff, attacked before implementation

Reviewed 2026-10-20 against the core at `05fde28` (head of PR #11, `v3/ks-potential`), before any
code of stage V3-S2R ("rules") was written. Input: the handoff
`recursion.fast-submissions/docs/snark-baseline/CORE-HANDOFF.md` (§2.1–§2.16), issues #4–#10, PR #11,
and the user's decisions of 2026-10-20: (a) the extractor is a computable Lean function with a proved
step-count bound, (b) completeness with error `δ` over a uniformly random oracle, cap `2^-128`
recommended, (c) O-25 must be closed, on a separate track (not implemented here).

Findings are `V3-S2R-H-M<i>` (major: the handoff as written would give a gameable, vacuous or
unrunnable rule) and `V3-S2R-H-m<i>` (minor). Each one ends with **Change:** what the stage does
instead. The stage implements the handoff as amended by these changes.

Method. Pass A (specification): each proposed rule was attacked for vacuity, for loopholes that let
an entry certify or score while doing less than intended, and for statements that say less than the
handoff claims. Pass B (fidelity): every claim the handoff makes about the code was checked against
`05fde28` (files, line numbers, line counts). Pass C (trust and hygiene): growth of the trusted base,
contradictions with DESIGN-v3 and the issues. Kernel probes are under `logs/s2r/probes/` (gitignored).

---

## Pass A: the proposed rules

### V3-S2R-H-M1. A step monad with Lean continuations charges nothing for the continuation's work (§2.5 requirement 1)

The handoff asks for "a small step-counting monad whose primitives are word-sized operations" and
warns about uncharged continuations. The warning is right. Every shallow form fails, not only the
obvious one:

- **Free monad over primitives** (`M α := ret a | prim p (k : Word → M α)`). The continuation `k` is
  any Lean function. It can do unbounded work on the word it receives before it emits the next
  primitive, and the step count does not see it. Kernel-checked: `logs/s2r/probes/Shallow.lean`,
  `bruteForce_steps (k) : (bruteForce k).steps tape = 1 := rfl`, where `bruteForce k` reads one word
  and then searches `2^k` candidates inside the continuation.
- **Parametric in the word type** (`∀ W [WordOps W], M W α`, so a continuation cannot inspect a word).
  The branch primitive must return something the continuation can branch on (a `Bool`). A program
  then reads the input bit by bit at linear charged cost and computes any function of those bits in
  the continuation for free. Parametricity bounds the information, not the work.
- `OProg` itself is of this shape (`query q (k : Digest → OProg α)`). This also settles a side
  remark of §2.3: no step count of an `OProg` verifier can price `V`'s local work, so "the same cost
  model could price `Vb`" needs `V` rewritten as a deep program with an oracle primitive.

**Change:** a **deep embedding**. The extractor is data: a statement tree over a closed enumeration
of word operations, with **no function-typed field anywhere in the syntax**. Its meaning is a
contract interpreter that consumes one unit of fuel for every statement it executes. Each interpreter
step does a bounded amount of word-RAM work: one operation on two words, one memory or input access,
one output word, or one push or pop of the statement stack. The only Lean computation the program
can trigger is the interpreter's own. Computing the program term itself is input-independent: it
amounts to advice of at most `progCap` statements, which the random-oracle model makes useless (see
m11).

### V3-S2R-H-M2. Expression trees evaluated in one step hide work in proportion to program size (§2.5 requirement 2)

A language with nested expressions (`x := (a + b) * (c ^^^ d) …`) evaluated as one step charges one
step for an expression of up to `progCap` nodes. That is a `2^20`-fold hidden factor on the budget
(`2^48` charged steps become `2^68` operations). The same holds for a `while` whose condition is an
expression.

**Change:** **three-address statements**. Every operand is a memory cell named by a constant index.
An operation reads two cells and writes one. A branch or a loop tests one cell for zero. No
statement contains a sub-expression.

### V3-S2R-H-M3. Node-extractor liveness cannot run at node size (§2.5 requirement 6, §6.3 step 8)

The handoff says the liveness check runs `E` and that benchmarks "calibrate step costs". The node
circuit's size does not depend on the tree level or on `n`, since every node verifies two
`Vb`-accepted proofs. At the handoff's own estimate the node extractor decodes a word of about
`2^29` symbols in about `2^43` steps (F1 §3.3, #7). An interpreter at an assumed 10 ns per step
(not measured) needs about 24 hours for that. A liveness rule that rejects an entry when its node extractor does not finish
within the harness's 2 h would block every recursive entry again, which is the problem #7 is about.

**Change:** the step bound is a theorem (`Computes`, below), and liveness becomes a smoke test with a
cap. §6.3 step 8 runs the compiled contract interpreter on the declared program for one leaf. For one
node, it runs only when the declared fuel at that tape length is at most a liveness cap (proposed
`2^36` steps; the value is the user's). Otherwise the record says "node liveness not run (fuel above
the cap)". Nothing in the security claim rests on liveness.

### V3-S2R-H-M4. A δ statement over random `H` loses the theorem that honest proofs verify under BLAKE2s (§2.6)

The handoff states this itself. The finding records that it is the one property the stage gives up,
and pins what replaces it. Under `Complete ∀ H`, `Vb c (P c w) = true` under BLAKE2s was a theorem.
Under `CompleteWithError δ`, a `V` that rejects every honest proof exactly when the oracle is BLAKE2s
is certified. This is the liveness analogue of O-25. It is not an exploit, because such an entry only
fails its own benchmark. It is, however, a change in what a certificate means.

**Change:** (1) the harness's concrete acceptance checks stay as the only guarantee, and §5.4 says
so: the root check, the sample checks, the smoke tree and §6.3 step 8 run the Lean `P` under
`blake2sOracle` and require `Vb` to accept. (2) The RESULT lists this as an assumption that the O-25
track must keep in view. (3) No contract clause is added: a kernel-checked concrete run of `P` and
`V` under BLAKE2s would need kernel evaluation of BLAKE2s at proof size.

### V3-S2R-H-m1. The grinding control is exact only with a bad fallback (§2.6 controls)

"A `P` that tries 128 nonces … `failProb = 2^-128` exactly" holds only if `P`'s fallback, when every
nonce is bad, returns a nonce that was already tried. A fresh fallback nonce is accepted with
probability `1/2`, which gives `2^-129`. **Change:** the control's prover falls back to nonce `0`,
which it tried first. The statement is proved for every `k ≥ 1` (`failProb = 2^-k`), so the
`k = 128` and `k = 127` controls are instances of one theorem.

### V3-S2R-H-m2. "No `BitVec`" conflates the cost model with compiled speed (§2.5 requirement 2)

In a deep embedding every statement costs one step whatever the Lean representation of a word is. A
`BitVec 64` value is a bounded 64-bit word, and no statement operates on an unbounded `Nat`. The
`BitVec`-compiles-to-`Nat` point (#9 item 9) affects how fast the compiled interpreter runs during
liveness, not what a step means. **Change:** keep `Word := BitVec 64`, so that the tape format, the
output format and `Library/Words.lean` are unchanged. The interpreter's compiled speed (UInt64) is an
open question for S3.

### V3-S2R-H-m3. The tape bound does not disappear with the RISC-V machine (§2.1 step 4, §2.11 item 6)

The handoff expects the `2^60`-word tape argument "may disappear". It moves instead. The input
primitive reads at a 64-bit address, so `Computes` must still restrict to tapes of at most `2^64`
words. At five words or more per log entry, that is at most about `2^61.7` entries, which is below
`logCap = 2^96`. `KS` still covers every log up to `logCap`, but *efficient* extraction is claimed
only within the tape bound. **Change:** state the domain `(extractorInput c π L).length ≤ 2 ^ 64` in
`Computes`. Restate the paper theorem's efficient-extraction domain in DESIGN §4.5 as
`Q + qV ≤ min(logCap, 2^61)`. Keep the `logCap` value open for the user (REPORT §6 Q2).

### V3-S2R-H-m4. The budget's linear term and the derivation (§2.5 requirement 5)

The handoff says "log indexing `≤ 2^8` per word today". In a word language, a straight-line extractor
that indexes the log by answer sorts or hashes it, at about `t·log t` comparisons. Each comparison is
four or more statements, for 4-word digests. At `log t ≈ 30` this is already about `2^8` statements
per word, with no room left. **Change:** `B t = 2^48 + 2^16·t` statements. The RESULT gives the
derivation: about `2^42.7` statements for the honest node decoder (`2^38.7` GF(2^64) operations at
about `2^4` statements each, including the reduction and the memory traffic), plus `2^5` headroom,
plus `2^16` per tape word. Two properties are checked. Within the tape bound, `B t ≤ 2^80 < 2^128`,
so enumerating `2^128` candidates is excluded. And `Rel` has no secret short enough for `2^48`
enumeration to extract: a leaf's start is 256 bits, and a node needs accepted child proofs.

### V3-S2R-H-m5. The program size cap must count statements, and memory must be charged (§2.5 requirement 3)

`imageCap = 2^20` bytes was 2^18 instructions. For a statement tree, the cap is
`progCap = 2^20` statements (`XStmt.size`). Two channels were checked and found closed. Constant
operands that are cell indices are naturals, but the program can learn only whether such an index is
in bounds, so they carry no readable table. Word constants carry 64 bits per statement, so a table
costs one statement per word. Declared memory is zero-initialised, so it holds no data. It does cost
time and space in liveness, though. **Change:** the interpreter charges one step per declared memory
word before the first statement, so every run satisfies `steps ≥ memory`.

### V3-S2R-H-m6. `E` is specification data after §2.5; the badge-path field is the program (§2.5 requirement 6, §2.8)

The handoff and the interim gate fix list `E` as a badge-path (computable) field. With a program in
place of the image, nothing executes `E`: the liveness check runs the program and decides `Rel` (for
a leaf) or `Vb` on the extracted children (for a node). Forcing `E` to be computable forbids honest
specifications that use classical choice, for no security gain. **Change:** gate rule 4's v3 entry
is `Submission: [V, P, ext]`. `E`, `ε`, `δ`, `qV` and `fuel` are specification data. DESIGN §7.6 is
corrected to match.

### V3-S2R-H-m7. Completeness is about `V`, not about `Vb` with its size cap (§2.6)

`CompleteWithError` (like `Complete`) composes `P` with `V`, not with the wrapper `Vb` that rejects
proofs above `proofCap`. A tighter form, which composes with `Vb`'s size check, was considered and
rejected. It is false for the witness-sending baseline: a node witness with two near-`proofCap`
children encodes above `proofCap`, so an honest non-succinct argument cannot be complete at
deployment for every `Rel` instance. **Change:** none in the contract. DESIGN §4.3 says that the
proof size cap is enforced by the benchmark, not by the completeness theorem.

### V3-S2R-H-m8. `Complete` (perfect, ∀ H) can leave the trusted base (§2.6)

Once `Certificate.complete` is `CompleteWithError … S.δ`, nothing trusted refers to `Complete`.
**Change:** move `Complete` to `Library/Security.lean`, with the embedding
`Complete R P V → CompleteWithError R P V 0` (`complete_withError_zero`). Existing entries port
through it, and the trusted base loses three lines.

### V3-S2R-H-m9. The prover's query count is unbounded, and that is correct (§2.6)

`failProb` sums over a lazily sampled oracle for every query `P` asks, and nothing bounds that
number. A cap is not needed for the theorem's meaning, since `failProb` is a probability for any
finite tree. It is not needed for liveness either, since a slow `P` fails liveness. **Change:**
none. The RESULT records it, so that the O-25 track does not assume a `qP`.

### V3-S2R-H-m10. CPU time does not remove SIMD (§2.3)

Measuring user+system CPU time on one core removes threads (`Task.spawn`). It does not remove
instruction-level parallelism across the `2^r` independent chains. Lean's C backend may
auto-vectorise an interleaved chain check, and the source rule bans `extern`, which is the only
route to explicit intrinsics. The calibration "`T_V ≤ T_triv,best/10`" is therefore only as good as
the organiser's best checker. **Change (design text only; the value is the user's):** the organiser's
reference trivial checker interleaves at least 8 chains, so that it is the strongest compiled-Lean
form available to an entrant, and the margin is stated against it. The step-count route (O-18) is
recorded as needing `V` as a deep program (M1).

### V3-S2R-H-m11. The extractor program is a constant; precomputation is advice (§2.5 requirement 1, the meta point)

A submitter can compute the program term by an expensive Lean computation, for example by embedding
the result of a large search as word constants. That work is independent of `(c, π, L)`. It is
equivalent to at most `progCap` words of advice fixed before the oracle is sampled, and in the ROM
such advice cannot predict log answers. A gate-computable program whose construction does not
terminate in practice fails liveness, which harms only the submitter. **Change:** none. The review
records the argument, and it is how this stage answers "no way to express unbounded computation
without steps".

## Pass B: the handoff against the code at `05fde28`

### V3-S2R-H-m12. Line references

At `05fde28` these references have moved. `Complete` is `Contract/Security.lean:110-112`, not
`:74-76`; the latter is the S1 pin, `15e4ae5`. `KState` is `:86-99`. The other cited locations match
the code: `Controls/Security.lean:58` and `:80-81`, `Controls/Backdoor.lean:151`,
`Controls/Certificate.lean:75`, `Gate.lean:251-256`, `Library/WitnessSending.lean:64-72`, and the
three `8 ≤ 2 ^ 40` terms. The other counts also check out: `Machine.lean` has 113 code lines and
the contract 331 (`scripts/loc.py`). **Change:** cite `05fde28` locations in the RESULT.

### V3-S2R-H-m13. The RISC-V `HALT` already hid bounded work, and the baseline's fuel was not "8 steps of work"

`readOut` returns `a1` words in the one `HALT` step. The witness-sending image outputs up to
`2^17 + 1` words "in 8 steps". The hidden work was bounded by `outCap` and could compute nothing, so
it was not an exploit. In the new language every output word is one step. The baseline extractor's
fuel then becomes linear in the tape, and every proof that cites "fuel 8" changes. **Change:** the
ported witness-sending program has a fuel linear in the tape, a proved bound (as built: `8·t`;
26 steps exactly on the empty proof), and the controls re-derive it. `ws_fuel_7` becomes a
fuel-exhaustion control at the new bound (as built: `ws_fuel_short`, 25 steps).

### V3-S2R-H-m14. The ledger and the PR record (§2.1, §2.13)

Confirmed: neither `V3-S2-KS-RESULT.md` nor `DESIGN-AMENDMENTS.md` records `05fde28` (the
noncomputable instance), and `docs/reviews/V3-S2-KS-review.md` is not in the core. **Change:** add
ledger entry V3-KS-A8 and a RESULT note, and copy the review in with a provenance line. The PR #11
body and the #5 comment are GitHub writes, which this stage does not make.

## Pass C: trust base, contradictions, hygiene

### V3-S2R-H-m15. Net trusted lines go down, not up (§2.5 "60–100 lines")

Removing `Machine.lean` (113 lines) and the vendored Rv64 (205 declarations reached) from the
trusted base, and adding a three-address language with a 9-constructor statement type and a
one-function interpreter, is a net reduction. **Change:** measure it with `loc.py` and report it.
Delete the machine, its library, its controls and `tests/asm`, together with the vendored tree and
its lake target, `check-vendor.sh` and CI step 1. Git keeps them at `05fde28`. If O-18 later needs a
RISC-V machine, it restores them.

### V3-S2R-H-m16. Design text that the change makes false

The change makes the following design text false: DESIGN-v3 §1 (pitch: "supply the extractor as a
RISC-V image"), §1.1 (figure), §3.2, §4.3 (`δ ≤ 2^-64`, opt-in), §4.4, §6.3 step 8, §6.6 (the `δ`,
extractor and image rows), §6.7 (grinding, magic-proof rows), §7.6 (rule 4 fields), §8 (items 2, 3,
8, the table), §10 and §12 (O-15(2), O-16, O-21, O-23). Also false, independently of this stage:
§2.1 (`Fin 32 → UInt8`), §4.1–§4.2 and §4.5 (V3-KS-A1/A2/A6), §5.3 ("cannot flatten"), §6.5
("22–29 s … 10×"), and §6.7 ("pays in `T_tree`"; #6). **Change:** patch the core's DESIGN-v3 from the
ledger, marking each patched section with its ledger id. The design workspace master is the user's
to sync.

### V3-S2R-H-m17. The nanoda budget must include the organiser closure (§2.7)

A per-entry nanoda cap measured on the entry alone would reject entries for the organiser library's
cost: the `BF64` closure takes 2.3 GB and 70 s. The cap is also the harness's defence against an
entry that exhausts the second kernel on purpose. **Change (S3; values open):** a cap on the whole
comparator run with both kernels, under a cgroup and a timeout, measured on the reference machine
over the full closure. Proposed default: 16 GB and 30 min, which is above R1's measured 2.41 GB and
70 s. Restore `scripts/tools.env` (comparator `d03acab`, lean4export `076e8e5`, nanoda `3a24072`)
from `v2-archive` so that a submitter can run the same check.

---

## Verdict

The handoff is sound in direction, and its two decided items are implementable. As written, §2.5
needs M1 and M2 to be meaningful: a deep three-address language, no function fields, one step per
statement. §2.5 also needs M3 for the harness, and §2.6 needs M4's restated guarantee. No proposed
rule was found false or unprovable. The δ embedding (`Complete → CompleteWithError 0`), the exact
grinding error and the "no prover reaches `δ < 1/2`" negative are proved in this stage. The stage
implements §2.5, §2.6, §2.8 (gate rule 4 only; the rest is recorded for S3), §2.10, §2.11 (text
items), §2.13 (ledger) and the text of §2.3, §2.4 and §2.7, with these changes. §2.2 (O-25) is out of
scope. §2.9, §2.12, §2.14, §2.15 and §2.16 are recorded as open decisions or GitHub writes.

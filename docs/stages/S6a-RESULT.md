# S6a RESULT: the benchmark leaf layout `L_chain(n)` (DESIGN §7.1–§7.2, O-3)

Stage 6a builds the leaf benchmark of DESIGN §7. One agent implemented it on 2026-10-14. Nothing
is committed.

> **Fix pass (2026-10-15).** The section "Fix pass" at the end supersedes this report where they
> differ: the kernel control's description and timings (≈ 1.8 s per G row, 24 s per file), the
> harness (its outputs are now range-checked), the mutant suite (8 mutants), the line counts, and
> the rendered `Lchain` (now `L_chain(16)`). Superseded figures below are marked "(fix pass: …)".

**Edits to existing files.**
- `RecursionFast/Controls.lean`: one import appended, `Controls.Chain`.
- `docs/DESIGN-AMENDMENTS.md`: S6-A1 to S6-A6 appended.

**Untouched.** `docs/DESIGN.md` and every file the other agents are editing. No trusted file
changed.

## Headline

- **O-3 (`k_min`, cells per `n`).** `L_chain(n)` has `9,225·n + 786,505` cells, about 115 per
  G-call.

  | n | cells | least class |
  |---|---|---|
  | 2^8 | 3.15 M | **24** |
  | 2^10 | 10.23 M | **24** |
  | 2^11 | 19.68 M | **25** |
  | 2^12 | 38.57 M | **26** |

  - **The floor.** The fixed 8-bit add table has 786,464 fixed cells, above `2^19`, so every chain
    length needs `k ≥ 24`. The kernel checks this on the benchmark layout itself:
    `Lchain_admissible`, `Lchain_not_admissible_23`.
  - **`n = 2^12` does not fit class 24.** It needs class 26, which is still inside `k_range` (20–28).
  - **Recommendation.** `k_min = 24`. The recursion tree's `n = 2^10` fits class 24 with 39 %
    headroom; the largest chain at 24 is `n = 1,733`.
  - **Your decision.** For the leaf board, either keep `{2^8, 2^10, 2^12}` at classes
    `{24, 24, 26}`, or switch to `{2^8, 2^10, 2^11}` at `{24, 24, 25}` (S6-A1).
- **The arithmetisation** (`harness/CHAIN-LAYOUT.md`) has 25 chips and 8 buses (4 lookup, 4
  interaction), with 1,163 matrix entries.
  - **G chip.** Two rows per G-call. One G needs 24 byte lookups and a chip may have at most 16
    ports, so one row per G is inadmissible.
  - **Tables.** The fixed `add8` add-with-carry table has `2^17` rows. A projection port serves the
    top byte with no carry-out cell.
  - **Rotations.** `rotr 16` and `rotr 8` are free byte permutations. `rotr 12` and `rotr 7` cost
    one range-checked wrap cell each.
  - **Routing.** Twenty state chips route words with tags `γ^r`, and a `FINAL` chip links the
    chain. Every height is pinned, and the witness is unique given `s`.
- **The Python oracle** (`harness/check-chain.py`) is independent of the generator.
  - **Clean.** It passes for 12 random secrets (n = 4, 16, 256, 1024) against `hashlib`.
  - **Mutations.** None of 2,776 single-cell mutations survive.
  - **Mutants.** Each of the 5 layout mutants admits a wrong chain, and the real layout rejects it.
  - **Agreement with the kernel.** Its verdicts agree with the kernel's on the same instances, and
    its `K` product agrees with Lean's `K.mul` on 304 pairs.
- **The kernel control** is `Controls/Chain.lean`, with data rendered from the generator's JSON
  into `Controls/ChainData.lean`. It contains 19 theorems on standard axioms only.
  - **What it covers.** The one-G-call harness: `rel` is decided for two calls of the chain, and
    proved for one call with the real `2^17`-row table. The statement agrees with the contract's
    `Blake2s.mix`. There are 3 negative controls.
  - **Time.** It builds in **128 s** (3.8 GB) (fix pass: 24 s, 3.1 GB). `ChainData.lean` takes
    9.5 s.
  - **Why not a full compression.** It is 160 G rows at about 10 s per row in the kernel, about
    27 min (fix pass: ≈ 1.8 s per row with `mul_fast`, ≈ 5–6 min per compression). The Python
    oracle covers whole chains instead.

## Files

| file | lines | what |
|---|---|---|
| `harness/gen-chain-layout.py` | 802 (fix pass: 862) | the generator, with commands `layout`, `witness`, `mini`, `mutant`, `report` (§1) |
| `harness/check-chain.py` | 631 | the evaluator of `Layout.rel` / `Admissible`, and the experiments (a)–(c) (§3) |
| `harness/render-layout.py` | 141 | JSON → Lean definitions (purely syntactic) |
| `harness/render-controls.sh` | 31 | regenerates `examples/` and `ChainData.lean`; deterministic, and rerunning it reproduces the same `ChainData.lean` |
| `harness/CHAIN-LAYOUT.md` | 241 | the arithmetisation: chips, columns, constraints, buses, tags, the soundness argument, cell counts |
| `harness/README.md` | 109 | usage, the JSON schemas, the cell-count table |
| `harness/examples/` | 1.1 MB | `chain-n{1,4,16}.layout.json`, witness and statement for n = 1 and 4, the harnesses `gcall0`, `gcall79`, `gcall0-add8` |
| `RecursionFast/Controls/ChainData.lean` | 847 code / 973 total (`scripts/loc.py`) | rendered: `LG0`, `LG79` (trimmed add table), `LGF` (full `add8`), `Lchain` = `L_chain(1024)` (fix pass: `L_chain(16)`) |
| `RecursionFast/Controls/Chain.lean` | 97 code / 195 total, 19 theorems | the kernel controls (§4) |

The logs are in `logs/S6a/` (gitignored): `experiments.log`, `experiments-1024.log`, `report.log`,
`axioms.log`, `chain-profile.log`, `kmul-kat.log`, `lean-negatives-python.log`, `kmul.lean`,
`bigtable.lean`.

## 1. Arithmetisation summary (full text: `harness/CHAIN-LAYOUT.md`)

**One chain link** is one BLAKE2s compression:
- the chaining value is `IV ⊕ 0x01010020` (unkeyed, 32-byte digest);
- the counter is `t = 32`, the flags are `f0 = 0xFFFFFFFF` and `f1 = 0`;
- the message is `m₀ … m₇` (the previous digest) with `m₈ … m₁₅ = 0`;
- the initial working vector is a constant.

The 80 G-calls per compression are numbered `q = 80i + 4s + g` (half-round `s`, slot `g`).

| chip | rows | cols | constraints | ports | cells per compression |
|---|---|---|---|---|---|
| `G` (2 rows per G-call: phase 0 = first half of G, phase 1 = second half) | 160·n | 53 | 33 | 15 | 8,480 |
| `S0 … S19` (state before half-round s, and the message words) | n each | 32 / 35 | 26 / 13 | 6 / 10 / 9 | 697 |
| `FINAL` (digest `h ⊕ v_lo ⊕ v_hi`, byte check of `H₄ … H₇`, chain link) | n | 48 | 22 | 14 | 48 |
| `PUB` (statement `(y₀ … y₃, n, 0 …)`) | 1 | 41 | 33 | 1 | (41 total) |
| `ADD8` (fixed, 8-bit add with carry) | 2^17 | 6 | 0 | 3 | (786,432 total) |
| `NIB` (fixed, nibbles) | 16 | 2 | 0 | 1 | (32 total) |

**Key choices**, each recorded as an S6 amendment:

- **G-call split.** Two rows per G-call, because of the port cap (S6-A2):
  - a row has 3 add slots, i.e. 12 byte lookups;
  - plus 1 nibble check, receive (phase 0) and send (phase 1): 15 ports.
- **Gadget form.** Every gadget is `gate · linear = 0`: degree 2, `t = 2`, `q = 1`. The gates
  are the view's `1`, `[r = 0]`, `[r + 1 = rows]`, `1 + [r + 1 = rows]`, and the phase cells `φ`,
  `1 + φ`.
- **Additions.** Each 32-bit add is four `add8` lookups, with the carries `c₁ … c₃` as cells.
  - Byte 3 goes through a projection port `(x, y, cin, z)` of the same table, so the discarded
    carry is no cell.
  - Every byte of every word is an add operand somewhere, and so is range-checked.
- **Rotations.** On packed words, `rotr 12` and `rotr 7` are a byte-aligned linear form plus
  `(1 + X^32)·W`, with `W` one nibble-checked wrap cell.
  - A wrong `W` puts a bit at position ≥ 32.
  - The next decomposition into range-checked bytes rejects that: the next G-call's `in_B`, or
    `FINAL`'s byte check of `H₄ … H₇`, which closes the aliasing of the last compression into the
    64-bit limbs of `y`.
- **Routing.** `eq` buses carry tags `γ^r`, with `γ = X` a generator of `K*`.
  - Row `r` of `G` has tag `γ^r`.
  - `S_s` row `i` has `κ = γ^{160i+8(s−1)}`.
  - `FINAL` row `i` has `κ = γ^{160i+152}`, which equals `S0`'s `κ` at `i + 1`.
  - Every counter is pinned at its first and last row, so every height is forced. The shuffles and
    the message schedule are just the column order of the `S` ports.

**Why `n = 2^12` cannot reach class 24 with byte lookups.**
- Class 24 allows about 3,904 cells per compression, i.e. about 49 per G-call.
- One G-call has 6 additions: 24 result bytes and 18 carries, before any operand or routing cell.
- Class 25 would need at most about 7,999 per compression; the layout has 9,225 (13 % more).
- The candidate savings listed in Open questions do not close that gap.

## 2. Measured cell counts (`logs/S6a/report.log`; agreeing witnesses in `experiments*.log`)

| n | cells (formula = measured) | cells need | fixed table needs | `k_min` |
|---|---|---|---|---|
| 4 | 823,405 | 20 | 24 | 24 |
| 16 | 934,105 | 20 | 24 | 24 |
| 2^8 | 3,148,105 | 22 | 24 | 24 |
| 2^10 | 10,232,905 | 24 | 24 | **24** |
| 2^11 | 19,679,305 | 25 | 24 | 25 |
| 2^12 | 38,572,105 | 26 | 24 | **26** |

Per chip at `n = 2^10`:

| chip | cells |
|---|---|
| `G` | 8,683,520 |
| `S0 … S19` | 713,728 |
| `FINAL` | 49,152 |
| `ADD8` | 786,432 |
| `NIB` | 32 |
| `PUB` | 41 |

Matrix entries: 1,163 (cap `2^(k+4)`). Fixed cells: 786,464 (cap `2^(k−4)`). Chips: 25. Buses: 8.
Maximum ports per chip: 15.

## 3. Python differential results (`harness/check-chain.py`)

The evaluator reads the JSON and implements `rowDot`, `holds`, `view`, `msgs`, `traffic`,
`Balanced`, `rel` and `Admissible` clause by clause, as `Layout.lean` writes them. It also
type-checks the JSON as a Lean `Layout K`. It shares no code with the generator.

**The K arithmetic** is checked three ways:
- against its own bit-by-bit definition, on 20,000 random pairs;
- against Lean's compiled `K.mul` (`#eval` of `Field.lean`), on 304 pairs (`logs/S6a/kmul-kat.log`);
- the kernel and the evaluator also agree on every instance of §4.

Run: `check-chain.py experiments --n 4 16 256 --seeds 5 --mutations 300` takes 6 min 28 s. The
n = 1024 run (`--seeds 1 --mutations 200 --kinds`, no mutants) takes 3 min 25 s.

**(a) Random secrets.**
- **What is checked.** `rel` holds at the least class. `Admissible 24` holds and `Admissible 23`
  fails. The statement's `y` equals `hashlib.blake2s` iterated `n` times, and `x₄ = n`,
  `x₅ … x₃₁ = 0`.

  | n | secrets | all pass | generate | load | `rel` |
  |---|---|---|---|---|---|
  | 4 | 5 | yes | 0.2 s | 0.1 s | 1.4–1.5 s |
  | 16 | 5 | yes | 0.4 s | 0.2 s | 1.6–1.7 s |
  | 256 | 1 | yes | 5.0 s | 3.9 s | 6.5 s |
  | 1024 | 1 | yes, at class 24 | 18.4 s | 16.4 s | 21.6 s |

- **Self-checks in the generator.** Every G-call is checked against RFC 7693 `G` and every
  compression against `hashlib`.

**(b) Single-cell mutations.**
- **Sampling.** Every chip with explicit cells gets three random cells, and the rest is uniform
  over all explicit cells. Each sampled cell is mutated twice, by `xor 1` and by a random value.
- **Results.**

  | n | mutations | survivors | failing clauses | time |
  |---|---|---|---|---|
  | 4 | 744 | 0 | gadget 484, bus 722, public 4, fixed 6 | 59.6 s |
  | 16 | 744 | 0 | gadget 516, bus 708, public 6, fixed 6 | 76.1 s |
  | 256 | 744 | 0 | gadget 468, bus 705, public 4, fixed 6 | 73.0 s |
  | 1024 | 544 | 0 | gadget 356, bus 514, public 6, fixed 6 | 131.4 s |

  A mutation can fail more than one clause, so a row's clause counts can sum to more than its
  mutation count.
- **How.** The re-evaluation is incremental: only the two affected gadget rows and the row's
  messages are recomputed. For n ≤ 16 this path was checked against the full `rel` on 40
  mutations each.

**(c) One layout mutant per mechanism.**
- **Method.** The generator writes the mutant and a wrong witness for it.
- **Checks.** The checker confirms four things:
  - the mutant JSON differs from the original, and the checker prints the difference (quoted
    below);
  - the mutant accepts the wrong witness and statement;
  - the original layout rejects them;
  - the claimed `y'` is not `blake2s256^n(s)`.
- All five mutants pass for n = 4, 16 and 256, in 2–4 s each at n ≤ 16 and 20–21 s at n = 256.

| mutant | change (as the checker's diff reports it) | wrong witness | the original rejects it by |
|---|---|---|---|
| `gate` | G: `M0` entry `(28, φ, 1)` removed: the gate of `out_C` | last G-call outputs `c₂ ⊕ 1` | gadget, G last row, constraint 28 |
| `addport` | G: the `ADDTOP` port of add slot 2 removed | last G-call's `a₂` top byte `⊕ 0x5A`, recomputed downstream | bus 1 (`ADDTOP`) |
| `nibport` | G: the `NIB` port removed | last G-call's `W := W ⊕ (1+X^32)^{-1}·0x12345`, so `b₂ ⊕ 0x12345` (a valid 32-bit word) | bus 3 (`NIB`) |
| `gouttag` | bus 5: tag column dropped from all 81 `GOUT` ports | `FINAL` receives slots 0 and 1 of the last half-round swapped | bus 5 (`GOUT`, `eq`) |
| `fixed` | `ADD8`: fixed table removed | one false row `(x, y, 0, z ⊕ 1, cout)` appended and used for `a₂`'s byte 0 | fixed (height `2^17 + 1`) |

**Note on eq buses.** No single eq-bus *port* removal yields a satisfiable mutant. With unique tags
at both ends, removing either side unbalances the bus for every witness. The eq-bus mechanism is
therefore shown by dropping the tag column of one link.

## 4. Lean kernel control (`RecursionFast/Controls/Chain.lean`)

**The data** come from `harness/render-controls.sh`, which renders `ChainData.lean` from the
example JSON (secret `00 … 1f`) by pure copying. The kernel checks three objects:

- **`LG0`, `LG79`.** The one-G-call harness for G-calls 0 and 79 of the chain. Call 79 is the
  diagonal step of round 9, and its `x` is the zero message word `m₁₃`.
  - **Chips.** `PUBG` (public: inputs and outputs, sends `GIN`, receives `GOUT`), the generated
    G chip with one call, `ADD8` trimmed to the 24 rows the call uses (in `add8` order), and `NIB`.
- **`LGF`.** The same harness for call 0 with the full `2^17`-row `add8` table, the benchmark's own.
- **`Lchain`.** `L_chain(1024)`, without a witness (fix pass: `L_chain(16)`).

| theorem | statement | proof | kernel time |
|---|---|---|---|
| `Lchain_admissible`, `Lchain_not_admissible_23` | the benchmark layout is admissible at 24, not at 23 | `decide +kernel` | < 0.6 s |
| `LGF_admissible`, `LGF_not_admissible_23`, `LG0_admissible` | the same for the harnesses (`LG0` at 20) | `decide +kernel` | < 0.2 s |
| `LG0_rel`, `LG79_rel`, `LG0_relK` | `rel` holds (`relK 20` for `LG0`) | `relBelow_iff` + `decide +kernel` | 22.2 s, 22.6 s |
| `LG0_mix`, `LG79_mix` | the statement's words are 32-bit, and the contract's `Blake2s.mix` maps the inputs to the outputs | `decide +kernel` | < 0.5 s |
| `LG0_trim` | every row of the trimmed tables is an `add8` row | `decide +kernel` | < 0.5 s |
| `harness_G` | the three harnesses share one G chip | `rfl` | — |
| `LG0_neg_byte` | one input byte changed (G row 0, `P₀`): ¬`rel` (gadget `in_A`) | `decide +kernel` | 8.0 s |
| `LG0_neg_sum` | the byte `t₂₀` changed (in no gadget constraint): ¬`rel`, and only the add lookup fails | `decide +kernel` | 23.0 s |
| `LG0_neg_out` | the output `b'` claimed `⊕ 1`, with the public table consistent: ¬`rel` (`eq` bus `GOUT`) | `decide +kernel` | 23.1 s |
| `mem_list_sum`, `mem_traffic`, `add8_sub` | a row of a sending port's table is on its bus; lookups certified row by row | proof | — |
| `LGF_rel` | `rel` at class 24 with the real `add8` (see below) | structured | ≈ 23 s |

**How `LGF_rel` is proved.**
- **Fixed clause:** the witness table is `add8` itself, so the clause holds by `rfl`.
- **Other buses:** bus balance on buses 2–7 is decided.
- **`add8` buses 0 and 1:** every received lookup `m` is certified as `add8` row
  `x + 2^8 y + 2^16 cin` (a cheap decide over the 18 received messages), and `mem_traffic` puts
  that row on the bus. Plain `decide` cannot do this: a 2^14-row fixed table already exceeds the
  kernel's deterministic timeout after 392 s (`logs/S6a/bigtable.lean`; 2^10 rows take 7.7 s).
- **`LG0_neg_sum`:** its offending tuple is not an addition at all, so it is not in `add8` either.

**Build.**
- `lake build RecursionFast.Controls.Chain`: **128 s, 3.8 GB** (fix pass: 24 s, 3.1 GB), with the per-theorem times in
  `logs/S6a/chain-profile.log`. `ChainData.lean` takes 9.5 s.
- The default `lake build` is green (2,482 jobs).
- **Axioms** (`logs/S6a/axioms.log`): `propext`, `Classical.choice`, `Quot.sound` only. There is
  no `sorry` and no `native_decide`.

**Python agrees with the kernel** on the same files (`logs/S6a/lean-negatives-python.log`):
- the positives `LG0`, `LG79` and `LGF` hold;
- `--flip 1 0 11` fails at gadget `G` row 0, constraint 8, and on bus 0;
- `--flip 1 1 31` fails on bus 0 only;
- `--flip 0 0 7 --xflip 7` fails on bus 5 only.

**Kernel cost.**
- One `K` product takes 44–117 ms in the kernel (`logs/S6a/kmul.lean`). It is a 64-step
  carry-less loop plus two folds, and multiplying by `1` or `0` is not cheaper.
- One G row is ≈ 10 s, so a full compression (160 G rows, plus 20 S rows and the `FINAL` row) would
  take ≈ 27 min (fix pass: ≈ 5–6 min). `n = 1` is therefore not a kernel control, and the Python oracle covers whole
  chains.

## 5. Deviations from DESIGN

1. **The §7.2 chip structure** ("a Blake2s chip (one row per compression round or per G-function),
   an 8-bit limb table chip …, a chain chip …") is replaced by the `G` / `S0 … S19` / `FINAL` /
   `ADD8` / `NIB` / `PUB` structure.
   - **Why.** The port cap of §2.2 makes one row per G-call or per round inadmissible.
   - **What it keeps.** The table chips and the `eq` chain link remain (S6-A2).
2. **`n = 2^12` does not fit class 24** (§7.2 "n is chosen so that n = 2^12 fits class 24"). It
   needs class 26; `n = 2^10` fits 24. The decision is the user's (S6-A1).
3. **The renderer.** The design says the layout is "rendered into Lean by the v0.3 renderer".
   - **What was done.** `scripts/render-challenge.py` is untouched, and a separate
     `harness/render-layout.py` renders layouts.
   - **Left for Stage 7.** A `{{layout:KEY}}` placeholder in the challenge renderer, with the leaf
     board's stub (S6-A6).
4. **The kernel control is one G-call, not `n = 1`.** A compression is infeasible in the kernel
   (§4). The control has two trimmed-table harnesses decided outright and one proof with the real
   table (S6-A5).

## 6. Open questions for the orchestrator

1. **O-3 / leaf board sizes.** Choose one:
   - keep `{2^8, 2^10, 2^12}` at classes `{24, 24, 26}` (allowed by `k_range`), or
   - use `{2^8, 2^10, 2^11}` at `{24, 24, 25}`.

   The recursion tree's `n = 2^10` fits 24 either way. §2.2's sentence "the leaf benchmark …
   fits at `k ≥ 24`" stays true.
2. **Getting `2^12` into class 25** would take about 13 % fewer cells than this layout's 9,225 per
   compression (at most about 7,999). Candidate savings:
   - a `G00` chip variant for the 21 of 80 G-calls whose two message words are zero (no message
     add: about −550 per compression);
   - a `cin = 0` projection port of `add8` (drops the zero cell: −160 per compression, plus 2^17
     table cells);
   - per-slot buses for the state chips (fewer tag cells).

   Together they give about 8,400, which is not enough. Getting there needs a different G split
   or wider tables, and the table cap binds at class 24. I do not recommend pursuing it now.
3. **The fixed-table floor `k ≥ 24`** applies even to `n = 2^8` (3.1 M cells). A 4-bit add table
   would lower the floor, but it doubles the lookups per G-call, needs 4 rows per G-call, and adds
   about 1.5× the cells (fix pass: about 1.8×, by the review's count, S6-A7). The 8-bit table matches §7.2's intent.
4. **Kernel cost of `K`.** Kernel controls of real layouts are bounded by the 44–117 ms product.
   - **Option.** A library rewrite of `rel` through a fast, proved-equal `K.mul` would make
     `decide` on whole compressions feasible. This is related to O-9.
   - **Upgrade path.** §7.2's route stays: `L_chain` from Clean's Blake2s through `toLayout`.
5. **Stage 7 integration.** Three items:
   - the leaf challenge stub with the layout placeholder;
   - where the 128 KiB proof cap of board L is checked (S3-A13);
   - whether the organiser's harness should run `check-chain.py experiments` in CI. It takes
     about 7 min for n ≤ 256.

## Fix pass (2026-10-15)

**Inputs.**
- The review `docs/reviews/S6a-review.md`, verdict "accept after one major fix".
- The orchestrator's decisions.
- The golfed `Controls/Chain.lean` (`docs/reviews/S6a-golf.md`). Its structure is kept: `mul_fast`,
  the clause-specific negatives, and `LGF_rel` reusing `LG0_rel`.

**Untouched.** `docs/DESIGN.md`, the trusted files, and the Stage 5 files. Nothing is committed.
The amendments S6-A7 to S6-A11 are appended to `docs/DESIGN-AMENDMENTS.md`.

### Findings

**S6a-M1 (major): fixed. The harness now range-checks its outputs, and the wording no longer
overclaims.**
- **The harness.** The one-G-call harness's public chip `PUBG`
  (`gen-chain-layout.py`, `mini_layout`) now decomposes the four output words `a' b' c' d'`. It
  has:
  - 16 byte cells `E{6..9}_{0..3}`, at columns 35–50;
  - the 4 packing constraints `out0 … out3`;
  - 8 receive ports on `PAIR`, the same check `FINAL` makes in `L_chain`.

  `PUBG` now has 51 columns, 29 constraints and 10 ports. The trimmed add tables also hold the
  `cin = 0` rows that serve those byte pairs (32 rows instead of 24).
- **The attack is a kernel negative.** The review's attack is
  `LG0_neg_wrap : ¬ LG0.rel 20 wrapStmt wrapWit`. Its witness:
  - G row 1: `W ⊕ 1` and `B ⊕ (1 + X^32)`;
  - `PUBG`: `x₇ ⊕ (1 + X^32)`, with its bytes `E7_0 ⊕ 1` and `E7_3 ⊕ 2^8` kept consistent.

  It is proved by deciding bus 2 (`PAIR`) alone.
- **Only `PAIR` rejects it.** `LG0_wrap_rest` decides that every gadget holds for that witness and
  every other bus balances. `wrapStmt_not_mix` shows the claimed statement is not `G`. The kernel
  thus exercises the rot-7 wrap and `NIB` in the soundness direction.
- **The review's `A6_rel_not_mix` now FAILS** (`logs/S6a/fix/A6recheck.log`).
  - **How it was checked.** The review's A6 witness and statement (`probes/s6a/out/A6_e1.*`) are
    re-rendered against the fixed `gcall0.layout.json`.
  - **The result.** `decide` proves `A6.relBelow 8 20 A6_stmt A6_wit` false, so its first conjunct
    does not hold.
  - **What holds instead.** `A6_rejected : ¬ A6.rel …`, and `A6_rejected_by_out1`: the gadget
    clause fails, at `PUBG`'s `out1`.
  - **Python agrees** (`logs/S6a/fix-harness-python.log`). The review's form fails at gadget `PUBG`
    constraint 26 (`out1`). The strongest form, bytes consistent, fails only on bus 2.
- **Wording.**
  - The `Chain.lean` module comment now says what the kernel checks: completeness on two G-calls,
    named single-cell faults, the wrap attack, `G_link` and the caps. It says that this does
    **not** prove that the harness computes `G` (`rel → MixStmt`), nor anything about whole chains.
  - S6-A8 replaces S6-A5's description and its proposed §7.2 sentence.
  - `LG0_mix` and `LG79_mix` are now described as facts about the honest statements.

### Minor findings

| finding | change | evidence |
|---|---|---|
| **m1** | `G_link` (from `probes/s6a/GchipLink.lean`) is in `Chain.lean`. The harness's G chip equals `Lchain`'s in columns, ports, shape, term and gate matrix. Its linear matrix equals `Lchain`'s except entry 13, `rho_last`'s constant: `γ` against `γ^{160·16−1}` | `propext` only, under 0.7 s |
| **m2** | Three mutants added to `mutant --kind` and to experiments (c): `nolast` (`rho_last` and every `kappa_last` gate dropped), `selpin` (the `nf` and `nl` gates dropped), `pairport` (`FINAL`'s 8 `PAIR` ports dropped). The wrong witnesses are the review's: the `(n−1)`-chain claimed as `n`; the last compression restarted from `s' = s ⊕ 0xA5…` through `nl`, `nf := X`; the last rot-7 wrap `⊕ 1` aliasing into `y₂`. The generator now writes `FINAL`'s top byte `E_k3 = H_k >> 24` unmasked (the same on honest witnesses) and packs the limbs with xor, so the `pairport` witness is constructible | each accepts a wrong chain that the real layout rejects (table below) |
| **m3** | The golfed negatives decide exactly the named clause: `LG0_neg_byte` G row 0 constraint 8 (`in_A`), `LG0_neg_sum` bus 0, `LG0_neg_out` bus 5. Kept. `LG0_neg_out`'s witness now also flips `E7_0` (column 39), so that `PUBG`'s new packing constraint holds and the public table stays consistent. On the trimmed table the flipped byte pair also misses `PAIR` (an artifact of trimming); on the full-table harness only bus 5 fails | Python, `fix-harness-python.log` |
| **m4** | The secret is read from a file or from stdin (`--secret-file F` / `-`), never from argv. `check-chain.py` and `render-controls.sh` pass it on stdin. The README says a witness file is secret material (S6-A9) | — |
| **m5** | One reading of the witness schema. The renderer now asserts `rows = len(cells)` and the K format (exactly 16 lowercase hex digits), as the checker does. The README states it | — |
| **m6** | No `/tmp` path. `render-controls.sh` renders everything from `harness/examples/`, and `Lchain` is now `L_chain(16)` (`examples/chain-n16.layout.json`). `L_chain(n)` depends on `n` only through three constants (S6-A11). The experiments examples use `mktemp -d` | — |
| **m7** | Moot: `Chain.lean` is now 24 s and stays in the default target | — |
| **m8** | Dead loop in `load_instance` removed. Lines over 100 characters wrapped. Line counts updated. The 4-bit estimate corrected to about 1.8× (S6-A7). The local `Decidable (g.holds z)` instance is removed. It is replaced by `GadgetsHold`, the named gadget clause, with a top-level `Decidable` instance like `relBelow`'s; `LG0_wrap_rest` needs it, because an instance under binders does not survive `rw [mul_fast]` | — |

**Also.** `LGF_rel`'s bus clause now certifies bus 2 (`PAIR`, the harness's new receivers) with
`add8_sub (b := 2) (cs := [1, 2])`.

### Lean (`lake build RecursionFast.Controls.Chain RecursionFast.Controls.ChainData`)

- **Build.** Green: `Chain` takes **24 s** (27.8 s wall for the target build, 3.1 GB), and
  `ChainData` elaborates in 10.0 s. The default `lake build` is green (2,489 jobs).
- **Per theorem** (`logs/S6a/fix/chain-profile.log`):

  | theorem | kernel time |
  |---|---|
  | `LG0_rel` | 5.8 s |
  | `LG79_rel` | 5.5 s |
  | `LG0_wrap_rest` | 5.4 s |
  | everything else | ≤ 0.7 s each |

- **Cost per G row.** With `mul_fast`, one G row costs ≈ 1.8 s in the kernel (golf's
  measurement), so a compression would take about 5–6 min. That is still not a CI control.
- **Hygiene.** `scripts/check-hygiene.sh` reports OK. There is no `sorry`, `native_decide` or
  `admit`.
- **Axioms** (`logs/S6a/fix/axioms.log`): a subset of `propext`, `Classical.choice`, `Quot.sound`
  for every control. `G_link`, `Lchain_admissible` and `Lchain_not_admissible_23` use `propext`
  only.
- **Size.** `Chain.lean` has 133 code lines (280 total) and 24 theorems; `ChainData.lean` has 888
  code lines (`scripts/loc.py`).

### Python suite (re-run: `logs/S6a/fix/experiments.log`, `experiments-1024.log`)

The n = 4, 16, 256 run (`--seeds 5 --mutations 300`) takes 7 min 57 s. The n = 1024 run
(`--seeds 1 --mutations 200`, all 8 mutants) takes 13 min 36 s. The two ran concurrently.

**(a) and (b).**

| n | (a) secrets | `rel` | (b) mutations, survivors | (b) time |
|---|---|---|---|---|
| 4 | 5 | 1.4–1.6 s | 744, 0 | 61.8 s |
| 16 | 5 | 1.7–1.8 s | 744, 0 | 75.4 s |
| 256 | 1 | 6.4 s | 744, 0 | 75.3 s |
| 1024 | 1, class 24 | 21.8 s | 544, 0 | 128.2 s |

- In every (a) run, `rel` holds, `y` equals `hashlib` iterated, `Admissible 24` holds and 23 fails.
- The cells measured on the witnesses agree with `9,225·n + 786,505`.

**(c): all 8 mutants pass at every n.** "Pass" means the mutant accepts the wrong witness, the
original layout rejects it, and `y' ≠ blake2s256^n(s)`:

| mutant | the original rejects it by (n = 4) | time per mutant (n = 4 / 16 / 256 / 1024) |
|---|---|---|
| `gate` | gadget `G` row 639, constraint 28 (`out_C`) | 3.0 / 4.1 / 21.0 / 77.6 s |
| `addport` | bus 1 (`ADDTOP`) | 3.5 / 4.0 / 20.9 / 76.4 s |
| `nibport` | bus 3 (`NIB`) | 3.1 / 4.2 / 21.1 / 76.8 s |
| `gouttag` | bus 5 (`GOUT`) | 3.1 / 4.0 / 21.1 / 76.8 s |
| `fixed` | fixed (height `2^17 + 1`) | 2.2 / 3.2 / 20.1 / 77.2 s |
| `nolast` | gadget `G` row 479, constraint 6 (`rho_last`) | 3.2 / 3.8 / 21.0 / 75.8 s |
| `selpin` | gadget `S0` row 3, constraint 9 (`nf`) | 3.0 / 4.1 / 21.4 / 76.3 s |
| `pairport` | bus 2 (`PAIR`) | 3.0 / 4.2 / 21.1 / 77.5 s |

### Files changed in the fix pass

| file | lines |
|---|---|
| `harness/gen-chain-layout.py` | 862 |
| `harness/check-chain.py` | 645 |
| `harness/render-layout.py` | 146 |
| `harness/render-controls.sh` | 33 |
| `harness/README.md` | 117 |
| `harness/CHAIN-LAYOUT.md` §7 | 249 total |
| `harness/examples/` (regenerated) | — |
| `RecursionFast/Controls/ChainData.lean` (re-rendered) | — |
| `RecursionFast/Controls/Chain.lean` | — |
| `docs/DESIGN-AMENDMENTS.md` (S6-A7 … S6-A11) | — |

**Logs.** `logs/S6a/fix/`, `logs/S6a/fix-build.log`, `logs/S6a/fix-harness-python.log`.

**Open.**
- The review's probes still target the old interfaces. `probes/s6a/attacks.py` calls
  `witness --secret HEX` and needs `--secret-file -` to re-run. `fidelity/Fidelity.lean`'s A6
  renders the old 35-column `PUBG`; its fixed-harness re-check is `logs/S6a/fix/A6Data.lean`.
  Updating them is left to the reviewer, since the probes are theirs.
- Everything in the original "Open questions" stands, with S6-A7 settling question 3.

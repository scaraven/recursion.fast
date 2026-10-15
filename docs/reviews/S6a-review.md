# S6a review: the benchmark leaf layout `L_chain(n)`

Adversarial review of Stage 6a (DESIGN §7.1–§7.2, O-3), 2026-10-15. Read-only on `RecursionFast/`
and `harness/`. Probes are in `probes/s6a/`, listed at the end.

**Reviewed versions** (sha256 prefix):

| file | sha256 |
|---|---|
| `harness/gen-chain-layout.py` (811 lines) | `dd231f0cc03101d1` |
| `harness/check-chain.py` (631 lines) | `a12e506d30971bb4` |
| `harness/render-layout.py` | `ca530cc5a077a9dc` |
| `harness/render-controls.sh` | `e83450fcd7768620` |
| `RecursionFast/Controls/ChainData.lean` | `237b7e813bbbd0f2` |
| `RecursionFast/Controls/Chain.lean` (mtime 23:37, before the golf pass) | `f8bf7039945becaa` |

## Verdict

**Accept after one major fix.** The fix is to the kernel control and to the wording that
describes it. The benchmark itself needs no change.

- **The benchmark is sound as far as I can find.** I tried to under-constrain `L_chain(n)`: a
  short chain, an intermediate digest presented as `y`, a chain restarted through silent
  selectors, a wrong rot-7 wrap bit aliasing into `y`, and a 33-bit secret word. Every attempt
  is rejected (Pass A), and I found no witness of `L_chain(n).rel` with `y ≠ blake2s256^n(s)`.
  - Three of these attacks are accepted by a layout with exactly one mechanism removed. Those
    mechanisms are load-bearing, and the RESULT's five mutants do not cover them (S6a-m2).
- **The Python oracle is faithful.** I diffed it against `Layout.lean` clause by clause and
  found no divergence. Nine tiny cases fed to both Python and `decide +kernel` agree, including
  five that fail in exactly one named clause.
- **The cell count is reproduced.** `9,225·n + 786,505`, `k_min = 24` and the largest chain at
  class 24, `n = 1,733`, all check out.
- **The kernel control overclaims (S6a-M1).** The one-G-call harness accepts statements that are
  not `G`. The kernel checks this: `A6_rel_not_mix`.

---

## Findings

### S6a-M1 (major): the one-G-call harness does not "compute G"; the kernel control overclaims

**Where.**
- The `Controls/Chain.lean` header says "`LG0_mix`, `LG79_mix`: the harness's statement is the
  contract's `Blake2s.mix` … on its inputs: **the layout computes `G`**".
- S6-A5 says "The statement agrees with the contract's `Blake2s.mix`". The §7.2 wording it
  proposes is "the kernel checks one G-call of the generated layout".
- `gen-chain-layout.py`, `mini_layout`: the public chip `PUBG` sends the inputs and receives
  the outputs without decomposing them.

**Problem.**
- `LG0_mix` is a fact about the *honest* statement only. No theorem ties `rel` to `mix`.
- The natural soundness reading, `∀ x w, LG0.rel 20 x w → MixStmt x`, is **false**.
  - The output `b'` is `B = Σ X^{8j+1}(Q ⊕ C')_{j+1} + (1 + X^32)·W`, with `W` checked only as
    a nibble.
  - In `L_chain`, a wrong `W` is caught by the *next* decomposition of `b`: the next G-call's
    `in_B`, or `FINAL`'s byte check.
  - The harness has no next decomposition.
- So for every input the harness accepts 15 wrong values `b' ⊕ (1 + X^32)·e`, for `e ∈ 1..15`.
  Each has bits at 32–35, so it is not a word.
- Consequence: the kernel never exercises the rot-7 wrap or the `NIB` mechanism in the
  soundness direction. Neither does any of the three kernel negatives.

**Witness (kernel-checked).**
- Probe `probes/s6a/fidelity/Fidelity.lean`, theorem `A6_rel_not_mix`:
  `A6.rel 20 A6_stmt A6_wit ∧ ¬ MixStmt A6_stmt`.
- `A6` is `harness/examples/gcall0.layout.json`, rendered by `render-layout.py`. `A6_layout`
  shows it is `rfl`-equal to the rendering of the example.
- The witness is the honest one with these changes: G row 1 `W := W ⊕ 1`, `B ⊕= 1 + 2^32`,
  `PUBG` `x7 ⊕= 1 + 2^32`. The resulting statement has `x7 = 0x000000017bd5d391`.
- The axioms are `propext`, `Classical.choice` and `Quot.sound`. In Python,
  `probes/s6a/attacks.py` A6 accepts `e = 1, 2, 15`.

**Fix.**
1. **Wording (required).**
   - Replace "the layout computes `G`" with "the harness accepts `G`'s inputs and outputs on
     two calls (completeness), and rejects three single-cell faults; its soundness is tested in
     Python on whole chains, where the next decomposition range-checks every output".
   - Amend S6-A5 and the proposed §7.2 sentence the same way.
2. **Harness (recommended).**
   - Decompose the four output words in `PUBG` like `FINAL` does: 16 byte cells, the 4 packing
     constraints `x_{6+i} = Σ X^{8j}·E_{i,j}`, and 8 `PAIR` receive ports. `PUBG` has 2 ports
     now, so this fits the cap of 16.
   - The harness then satisfies `rel → MixStmt` on the wrap mechanism.
   - Add the A6 witness as a fourth kernel negative, `LG0_neg_wrap`. It should fail only on bus
     2 (`PAIR`).
   - This is the only kernel exercise of the `NIB` and wrap mechanism.

### Minor findings

**S6a-m1: the harness G chip is not linked to the benchmark's G chip in the kernel.**
- `harness_G` shows only that the three harnesses share one G chip.
- **Measured** (JSON diff, `probes/s6a/GchipLink.lean`). `LG0_chip1` and `Lchain_chip1` have
  the same columns, ports, shape, term and gate matrix. Their linear matrices differ in exactly
  one entry, index 13: `rho_last`'s constant, `γ` versus `γ^{160·1024−1}`.
- **Fix.** Add `G_link` from the probe to `Chain.lean`. It decides in under 5 s and depends on
  `propext` only. Then "the kernel checks one G-call of *the generated layout*" is literally
  true.

**S6a-m2: three load-bearing mechanisms have no layout mutant.** The RESULT says "one layout
mutant per mechanism". Each mutant below accepts a wrong chain claim that the real layout rejects
(`probes/s6a/attacks.py`, n = 4):

| mutant (removed) | wrong claim it accepts | real layout rejects by |
|---|---|---|
| `nolast`: `rho_last` (G) and every `kappa_last` | the n = 3 witness with statement `(blake2s^3(s), n = 4)`: `d1 = n` is unbound | gadget `G` row 479, `rho_last` |
| `selpin`: the `nf` (S0) and `nl` (FINAL) gadget rows | a chain restarted at compression 3 from a fresh `s'` by setting `nl`, `nf := X` (silent): `y = blake2s(s')` claimed as `n = 4` | gadget `S0` row 3, `nf` |
| `pairport`: FINAL's 8 `PAIR` ports | last compression's rot-7 wrap `W ⊕ 1`: `y₂ ⊕ (1 + X^32)` (S6-A3's aliasing, now witnessed) | bus 2 `PAIR` |

- **Fix.** Add these as `mutant --kind nolast|selpin|pairport`. The probe builds each wrong
  witness. Add them to experiments (c).
- The `selpin` row is the concrete instance of S1-A11 (a): a selector that is not constrained
  to 0/1 silences a required message.

**S6a-m3: the kernel negatives name their clause only in docstrings.**
- `LG0_neg_byte`, `_sum` and `_out` prove `¬ rel`. The clause attribution comes from Python
  (`lean-negatives-python.log`).
- `LG0_neg_byte`'s docstring says "`in_A` fails", but bus 0 fails too.
- **Fix (cheap).** State each negative as the vector of the six conjunct verdicts, as the probe
  does with `Clauses`, e.g. `Clauses F3 2 6 … = [true, true, true, false, true, true]`. The
  kernel then pins the failing clause.

**S6a-m4: the secret is passed on the command line.**
- `witness --secret HEX` puts `s` in `/proc/<pid>/cmdline`, which every process on the host
  can read unless `/proc` is mounted with `hidepid`.
- DESIGN §6.3 item 1 says "Secrets are never written to the sandbox the verifier runs in".
- **Fix.** Read the secret from a file or stdin (`--secret-file`). Document that
  `*.witness.json` is secret material (S0 row 0 holds `s`). Stage 7 places it.

**S6a-m5: the witness schema has three readings.**
- The README gives `{"rows": R, "cells": …}` and says "a cell outside the listed rows … is 0",
  which suggests `R > len(cells)` is allowed.
- `check-chain.py` (`table_of`) rejects `R ≠ len(cells)`.
- `render-layout.py` (`table_lean`) ignores `R` and renders `len(cells)` rows.
- `render-layout.py` also does not validate K strings (it parses any `int(h, 16)`), whereas the
  checker requires exactly 16 lowercase hex digits (`kel`).
- **Fix.** The renderer asserts `R == len(cells)` and the K format. The README states that.

**S6a-m6: the rendered `Lchain` cannot be traced back to a file in the repository.**
- `render-controls.sh` renders `Lchain` from the fixed path `/tmp/chain-n1024.layout.json`,
  which other users can clobber or plant.
- The JSON is not kept, so its sha in `ChainData.lean`'s header can be checked only by
  regenerating it.
- **Fix.** Use `mktemp -d`, or write it to `harness/examples/`.

**S6a-m7: build cost.**
- `Controls/Chain.lean` is in the default target `RecursionFastControls`: 128 s and 3.8 GB.
  The CLAUDE.md quotes about 40 s for a warm default build.
- It rebuilds whenever `Contract/Layout` or `Library/Layout` changes.
- This is acceptable for CI. A cheaper split is possible:
  - keep the admissibility controls (under 1 s) in the default target;
  - move `LG0_rel`, `LG79_rel`, `LGF_rel` and the negatives (about 125 s) to a CI-only
    `lean_lib`.
- Orchestrator's call.

**S6a-m8: hygiene.**
- `check-chain.py`, `load_instance`: a dead loop (`for … : if …: pass`).
- `S6a-RESULT.md` says the generator has 802 lines; it has 811.
- `Chain.lean` lines 98, 147 and 152 are over 100 characters (101–111).
- **Wording.** The RESULT's open question 3 estimates the 4-bit option at "about 1.5×" the
  cells; my count is about 1.8× (see the advice below).

### What found nothing

- **No under-constraint of `L_chain(n)`.** Attempts and argument are in Pass A.
- **No divergence** between `check-chain.py` and `Layout.lean` (Pass B).
- **No arithmetic error** in the cell formula, the caps or `k_min` (Pass B).
- **Determinism.** Two runs of `layout --n 1024` and `witness --n 4` give identical sha256, and
  `examples/chain-n4.witness.json` is reproduced byte for byte.
- **Shared code.** `gen-chain-layout.py` and `check-chain.py` share no code: no import, and
  `kmul` and `add8` are written independently in each, and a third time in Lean.

---

## Pass A: the benchmark's meaning (independent reconstruction)

I reconstructed the constraint system from `gen-chain-layout.py` and the JSON (`chain-n4`), not
from `CHAIN-LAYOUT.md`. I then checked each claim of S6-A2…A4 against it.

**G chip, per row.**
- **Constant cells.** `one = 1`, `zero = 0`, `ψ = φ + 1`, and `φ' = φ + 1` on every row
  including the wrap, with `φ_0 = 0`. So `φ` alternates over `{0, 1}` and the height is even.
  Both phase gates are therefore boolean.
- **Tag.** `ρ_0 = 1`, `ρ' = γρ` off the last row, and `ρ_last = γ^{2·calls−1}`. `γ = X` has
  order `2^64 − 1`, which `report` checks with the correct factorisation. So the height is
  exactly `160n`.
- **Additions.** The 12 lookups per row have `sel = one`. Byte 0 has `cin = zero`. Each carry
  cell is the `cout` of byte `j` and the `cin` of byte `j + 1`. Byte 3 is a projection port of
  the same table. Each slot therefore computes `z = x + y mod 2^32` exactly, with every operand
  byte, result byte and carry range-checked.
- **Phase 0.**
  - `in_A`, `in_B`, `in_C`, `in_X` pin the packed inputs to range-checked bytes.
  - `in_D` pins `D = a₁ ⊕ rotl(d₁, 16)` with `D'` and `A'` range-checked, so `d₁` is
    determined.
  - `a1_j` and `c1_j` copy into the next row. `in_Y` decomposes `Y` into the next row's `M`.
  - `d2_j` gives `D'_next = rotr(d₁ ⊕ a₂, 8)`.
  - `b1` gives `packed(Q_next) = rotr(b ⊕ c₁, 12)` up to `(1 + X^32)·e`, which is impossible
    for range-checked `Q_next`.
- **Phase 1.** `out_A`, `out_C`, `out_D` pack range-checked bytes, and `X = Y = 0`. `out_B` is
  the only output not packed from checked bytes (S6a-M1).
- **Next-row references.** Only phase 0 uses the next row, which is phase 1 of the same call.
  The wrap row is phase 1, so no constraint reads across calls or across the wrap.
- **Routing.**
  - Every eq-bus message carries a tag cell pinned per row. The tag sets of senders and
    receivers are equal and duplicate-free on every eq bus:
    - `GIN`: `γ^{2q}`;
    - `GOUT`: `γ^{2q+1}`;
    - `MSG`: `γ^{160i+8s}`, with `FINAL` filling `s = 19`;
    - `OUT`: one message.
  - So multiset equality is a bijection that preserves position. Nothing can be swapped,
    reused or permuted.
  - The `S_s` and `FINAL` heights are pinned by `κ_last`. `γ^160` has order `(2^64−1)/5`, far
    above `2^28`.
  - `PUB` has exactly one row, because `OUT` is sent once and received on every `PUB` row.
  - Each `S_s` receives all 16 words from half-round `s − 1` and sends the same cells to
    half-round `s`. The quads partition the 16 words in both the column and the diagonal step.
- **Schedule.** I checked the message schedule in the JSON for S18 and S19 against σ₉. Indices
  ≥ 8 read `zero`.
- **Every word is range-checked where it matters:**
  - b-words are only ever `B` inputs or `FINAL`'s `H₄…H₇`;
  - d-words are packed from `D'`;
  - a- and c-words are add outputs;
  - message words are decomposed by `in_X` or `in_Y` in every compression, since each σ row
    uses all 16 indices;
  - `H₀…H₃` are XORs of checked words;
  - `H₄…H₇` are checked by `PAIR`.
- **The statement** is
  - `x_k = H_{2k} + X^32·H_{2k+1}`, which is the little-endian 64-bit limb because both halves
    are below `2^32` (S2-A1);
  - `x₄ = n`;
  - `x₅…x₃₁ = 0`.

  This matches DESIGN §5.1: `d0 = y`, `d1 = n` as one element, and the rest 0.
- **Constants.** `INIT = (IV ⊕ 0x01010020, IV₀₋₃, IV₄ ⊕ 32, IV₅, IV₆ ⊕ ~0, IV₇)` agrees with
  `Blake2s.blake2s256` on 32-byte inputs: one block, `t = |d| = 32`, `f0 = ~0`.

**Attacks** (`probes/s6a/attacks.py`, Python oracle, n = 4, example secret; `attacks.log`,
`out/results.json`):

| attack | claim | verdict | failing clause |
|---|---|---|---|
| A1a | n = 3 witness, statement `n = 4` | rejected | gadget `G` row 479 (`rho_last`) |
| A1b | n = 3 witness, statement `n = 3` on `L_chain(4)` | rejected | gadget `PUB` (`x₄ = n`) |
| A2a | `y := blake2s^3(s)` in `PUB` | rejected | bus 7 `OUT` |
| A2b | the same, with `la`/`nl` moved to row 2 | rejected | gadget `FINAL` (`nl`), bus 6 `MSG` |
| A3 | silent selectors (`nl`, `nf := X`) restart the chain from `s'` | rejected | gadget `S0` (`nf`) |
| A4 | last compression's rot-7 wrap `⊕ 1`, aliasing into `y₂` | rejected | bus 2 `PAIR` |
| A5 | a 33-bit secret word, consistent across the S rows and G inputs | rejected | gadget `G` row 0 (`in_X`) |
| A1a / A3 / A4 against the mutants of S6a-m2 | — | **accepted** | — (load-bearing) |
| A6 | the harness `LG0`, `b' ⊕ (1 + X^32)·e`, e = 1, 2, 15 | **accepted** | S6a-M1 |

## Pass B: fidelity of `check-chain.py` to `Layout.lean`

| clause / definition (`Contract/Layout.lean`) | `check-chain.py` | agrees? |
|---|---|---|
| `rowDot` (l.130): filter the entries of row `r`, `Σ v·z c`, duplicates summed, list order | `load_layout` builds `by_row`, keeping every entry in order (l.166–172); `holds_at` sums them (l.222–226) | yes. F1: two entries `X·a` at one position cancel |
| `Gadget.holds` (l.134): `∀ r : Fin cons, Σ_i c i · prod (S i).map …` with `List.prod = foldr` | `holds_at` (l.215–230): `for r < cons`, `reversed(S_i)` foldr, `kmul(c_i, p)`, xor-sum | yes. F1: `S = [0, 0, 1]`, `c = X^63`. F7 is a negative |
| `view` (l.139): row, `(r + 1) % rows`, then `1`, `[r = 0]`, `[r + 1 = rows]` at `2·cols`, `+1`, `+2` | `view` (l.210–212), same order, `Tab.row` pads with 0 or truncates to `cols` | yes. F1 (1-row table: flags both 1, next = self), F2 (wrap) |
| `Table.msgs` (l.149): rows `< rows` with `cell r sel = 1`, message `msg.map cell` | `msgs` (l.233–235) | yes. F2: `sel = X` is silent on a row whose message is not in the table |
| `traffic` (l.153): over `zip chips w`, ports with `bus == b && send == s` | `traffic` (l.242–251), `zip`, same filter | yes |
| `Balanced` (l.158): `.eq` multiset equality in ℕ; `.sub` `∀ m ∈ r, m ∈ s` | `balanced` (l.254–258): `Counter ==`; `set` membership | yes. F3 (eq multiplicity), F2 (sub, a value looked up twice) |
| bus kind beyond the list | `bus_kind` (l.183): `"eq"`; the renderer uses `getD b .eq` | yes. F8 / F8n: duplicated receive fails, so `.eq` |
| `∀ b` balanced | only buses some port uses (`all_buses`, l.238); the others carry nothing (`traffic_eq_zero`) | yes |
| `rel` conjunct 1: `w.length = chips.length` | `res["length"]` (l.265) | yes |
| conjunct 2: fixed height, cells `r < rows`, `c < cols` | `res["fixed"]` (l.266–281), row-wise compare truncated to `cols` | yes. F5 |
| conjunct 3: gadget on every row `< rows` | `res["gadget"]` (l.284–295); chips with `cons = 0` skipped (vacuous `Fin 0`) | yes |
| conjunct 4: buses | `res["bus"]` (l.297–303) | yes |
| conjunct 5: `∃ T ∈ w[pub]?, 1 ≤ rows ∧ cells 0..31 = x` | `res["public"]` (l.304–306) | yes. F4 |
| conjunct 6: `Σ rows·cols ≤ 2^k` | `res["cells"]` (l.307–308) | yes. F6 at classes 5 and 6 |
| `Admissible` (l.188–209): chips, public `≥ 32` columns, entries `≤ 2^(k+4)`, fixed cells `≤ 2^(k−4)` (ℕ subtraction), per-chip caps | `admissible` (l.187–205); `2 ** max(k−4, 0)` matches ℕ subtraction | yes |
| `K` `+`, `*` (`Field.lean` l.32–49): xor; 64-step `clmul`, then two folds by `0x1B` | `clmul`, `kmul` (l.33–55), checked against `kmul_ref` (l.58) | yes. F1: `X^63 · (2^64 − 1)^2` needs both folds; Lean and Python agree (`0x36e`) |
| statement / limb encoding | `kel`: exactly 16 lowercase hex digits; `stmt_y`: limbs LE | yes (renderer: S6a-m5) |
| `Incremental` (single-cell path) | rechecks rows `r − 1` and `r`, the chip's buses, fixed and public | equivalent by reading; the author cross-checks 40 mutations against full `rel` |

**Probe P2** (`probes/s6a/fidelity/`).
- **How it was run.** `mk.py` writes nine cases as JSON. Each is evaluated by `check-chain.py`
  (`python.log`) and rendered by `render-layout.py` into `Fidelity.lean`. The kernel decides
  that file in **45 s** (`lean.log`), with standard axioms only.
- **Positives:** `F1_rel`, `F2_rel` (class 6), `F8_rel`.
- **Negatives in exactly one clause** (`Clauses … = [..]`):

  | case | failing clause |
  |---|---|
  | F3 | bus |
  | F4 | public |
  | F5 | fixed |
  | F6 | cells (F2 at class 5) |
  | F7 | gadget |
  | F8n | bus kind `.eq` by default |

- **Agreement.** Python's per-clause verdicts in `python.log` agree on all nine cases.
- **Note.** Python's `relK 6` line for F2 is `False` because F2 is not admissible (fixed cells
  6 > `2^(6−4)`). Its `rel` clauses are all true, as in Lean.

**Caps and cells** (`probes/s6a/report.log`, `gen … report`).
- **Cells.** They reproduce `9,225·n + 786,505`:
  - `G` 160·53 = 8,480;
  - `S0` 32, `S1…S19` 35 each, so 697;
  - `FINAL` 48;
  - fixed `ADD8` 2^17·6 = 786,432, `NIB` 32, `PUB` 41.
- **The largest chain at class 24.** n = 1,733 has 16,773,430 cells and fits; n = 1,734 does
  not.
- **The fixed cap at 24.** `2^20 − 786,464 = 262,112` cells are free (25 %). That is enough
  for a `2^16 × 3` table, not for `2^16 × 4`.
- **The other caps** (from the JSON):
  - ports: at most 15 (G), 14 (FINAL), 10 (S);
  - message length at most 9;
  - `t = 2`, `q = 1`, degree 2;
  - `cons` at most 33;
  - `cols` at most 53;
  - 1,163 entries.

  `Lchain_admissible` and `Lchain_not_admissible_23` decide these for n = 1024. `k_range` is
  20–28, so class 26 is allowed for n = 2^12.

## Pass C: kernel control and code

- **Which layout the kernel checks.**
  - `Chain.lean` checks `rel` on the *rendered* generator output, not on a hand copy.
  - The harness G chip differs from `L_chain`'s in one constant only (S6a-m1).
  - The S chips, `FINAL`, `PUB`, the tags and the `MSG` chain never meet the kernel on a
    witness. This is acknowledged, and S6a-m2 strengthens the Python side.
- **The `add8` certification is sound.** `add8_sub` and `mem_traffic` certify `LGF_rel`'s
  lookups row by row; `LG0_trim` shows the trimmed tables consist of `add8` rows.
- **Axioms.** `logs/S6a/axioms.log` lists standard axioms only. There is no `sorry`,
  `native_decide` or `admit` (grep).
- **Build time.** 128 s per the log, not re-measured, because the golf agent is editing
  `Chain.lean`. Acceptable (S6a-m7).
- **JSON readers.** The README schema matches `render-layout.py`'s reader, apart from S6a-m5.
- **Determinism.** The generator is deterministic, with no RNG. `check-chain.py experiments`
  is seeded (`--rng 20261014`).

## Advice: the 4-bit-limb option (not a finding)

**Do not pursue it.**

- **No byte-or-narrower table puts n = 2^12 in class 24.**
  - Class 24 at n = 2^12 leaves `(2^24 − 786,464)/(4096·80) ≈ 49` cells per G-call, routing
    included.
  - Any arithmetisation whose adds are table lookups needs per G-call:
    - `6 adds × (4 result bytes + 3 carries) = 42` lookup-output cells;
    - plus the non-add-result operand words `b`, `d₁`, `b₁`, `d₂`: 16 bytes.
  - That is **at least 58 cells per G-call** with perfect cell sharing, before message bytes,
    tags or packed words.
  - With nibbles the floor is `6 × (8 + 7) = 90`.
  - A wider table cannot fit: `(x, y, cin)` over 8 bits is already `2^17` rows × 6 columns, 75 %
    of the class-24 fixed cap.
- **What 4-bit limbs would cost** (my estimate; not built):
  - **Table.** The add table shrinks to `2^9 × 6 = 3,072` cells, so the fixed floor drops from
    k = 24 to 16.
  - **Rotations.** `rotr 16`, `12` and `8` become free (nibble-aligned); `rotr 7` still needs
    one wrap cell.
  - **Rows.** Each half-G needs 24 lookups, so 4 rows per G-call under the 16-port cap.
  - **Cells.** About 97 cells per half-G (40 operand nibbles, 24 result nibbles, 21 carries,
    11 fixed columns, 1 wrap), so about 16.4 k per compression against 9,225.

  | n | now | with 4-bit limbs |
  |---|---|---|
  | 2^8 | 24 | 23 |
  | 2^10 | 24 | 25 (16.8 M > 2^24) |
  | 2^12 | 26 | 27 |

  It helps only the smallest leaf and hurts the recursion tree's n = 2^10.
- **Recommendation.** Keep the 8-bit table and the orchestrator's S6-A1 decision: 2^8 and 2^10
  at class 24, 2^12 optional at class 26. If 2^12 at class 25 is ever wanted, the RESULT's own
  savings list is the place to look (the bound above leaves room). Class 24 is out of reach for
  it.

## Probes

| probe | what | result |
|---|---|---|
| `probes/s6a/attacks.py` (`attacks.log`, `out/results.json`) | P1: 13 hand-built wrong witnesses on `L_chain(4)`, 3 new mutants, the harness attack. Run: `python3 -I probes/s6a/attacks.py REPO OUT`, 17 s. Large outputs pruned; re-running regenerates them | all `L_chain` attacks rejected; the 3 mutants accept (S6a-m2); the harness accepts A6 (S6a-M1) |
| `probes/s6a/fidelity/mk.py`, `json/`, `python.log`, `Fidelity.lean`, `lean.log` | P2: Python against the kernel on 9 cases, plus `A6_rel_not_mix` and `A6_layout`. Run: `lake env lean probes/s6a/fidelity/Fidelity.lean`, 45 s | full agreement; `A6_rel_not_mix` holds |
| `probes/s6a/GchipLink.lean` (`GchipLink.log`) | P3: `G_link`, the harness G chip against `Lchain_chip1` up to entry 13, `decide +kernel` in under 5 s | holds (S6a-m1) |
| `probes/s6a/report.log` | P4: the cell report for n = 256, 1024, 1733, 1734, 2048, 4096 | formula reproduced |
| (inline) | P5: determinism. Two runs of `layout --n 1024` and `witness --n 4` (sha256 identical); the example witness regenerated byte for byte | deterministic |

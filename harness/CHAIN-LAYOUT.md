# The benchmark leaf layout `L_chain(n)` (Stage 6a, DESIGN §7.1–§7.2, O-3)

`L_chain(n)` is a `Layout K` (`RecursionFast/Contract/Layout.lean`). It holds with statement
`x = (y₀, y₁, y₂, y₃, n, 0, …, 0)` iff the prover knows a 32-byte `s` with
`blake2s256^n(s) = y` (the limbs `y_j` are bytes `8j … 8j+7` of `y`, little-endian, as S2-A1). It is
produced by `harness/gen-chain-layout.py`. The generator asserts every compression against
`hashlib.blake2s` and every G-call against RFC 7693 `G`. `harness/check-chain.py` evaluates the
contract's `rel` on it independently.

## 1. What is computed

One chain link hashes a 32-byte message: **one** BLAKE2s compression with
- the chaining value `h = IV ⊕ (0x01010020, 0, …)` (digest 32, no key, fanout and depth 1);
- the counter `t = 32`;
- the last-block flag `f0 = 0xFFFFFFFF`, and `f1 = 0`;
- the message words `m₀ … m₇` (the previous digest, or `s`), with `m₈ … m₁₅ = 0`.

The initial working vector is a constant:
`v = (h₀ … h₇, IV₀ … IV₃, IV₄ ⊕ 32, IV₅, IV₆ ⊕ 0xFFFFFFFF, IV₇)`.

Ten rounds give 20 half-rounds `s = 2r + h`: the column step (`h = 0`) and the diagonal step (`h = 1`).
Each half-round has four G-calls. The digest is `h'_k = h_k ⊕ v_k ⊕ v_{k+8}`, and it becomes the next
message. So the chain is `80n` G-calls, numbered `q = 80i + 4s + g`.

## 2. Representation over K = GF(2^64)

- **Words.** A 32-bit word `w` is the K element with `bits = w`.
  - **XOR is free.** `w ⊕ w'` is `w + w'` in K.
  - **Bytes.** The bytes `w_j` are K elements below `2^8`, and `w = Σ X^{8j}·w_j`. The coefficient
    `X^{8j}` is a shift: there is no reduction below degree 64.
- **Additions mod 2^32** use the **`add8` lookup table**. Its rows are
  `(sel = 1, x, y, cin, z, cout)` for all `x, y < 2^8` and `cin ∈ {0, 1}`, where
  `x + y + cin = z + 256·cout`. That is `2^17` rows and 786,432 cells. A 32-bit add `z = x + y` is four
  lookups, one per byte, with the carries `c₁, c₂, c₃` as cells (`c₀` is a zero cell).
  - Byte 3 is looked up on bus `ADDTOP`, which `add8` serves through a second port that omits
    `cout`. So the discarded carry `c₄` is never a cell.
  - Every operand byte of an add is range-checked by its lookup. Every byte of every word in the
    chain is an add operand somewhere, so every byte is range-checked.
- **Rotations.**
  - `rotr 16` and `rotr 8` permute the bytes, so they are free (linear).
  - `rotr 12` and `rotr 7` cross bytes. On the **packed** value, the cut cancels everywhere except at
    the 32-bit boundary:
    - `rotr(u, 12) = Σ_j X^{8j+4}·u_{j+2} + (1 + X^32)·W`, where `W = hi4(u₁)`;
    - `rotr(v, 7) = Σ_j X^{8j+1}·v_{j+1} + (1 + X^32)·W`, where `W` is bit 7 of `v₀`.
  - So each of these rotations is **one wrap cell `W`**, range-checked as a nibble (bus `NIB`, table
    `0 … 15`). The other split cells cancel in the packed sum.
  - **Why this is sound.**
    - For a `W` that is a nibble but not the true one, the packed result has a bit at position 32
      or above.
    - Every packed word is later decomposed into range-checked bytes, so such a value has no
      decomposition: the next G-call decomposes `b`, and FINAL decomposes the output words. The
      `in_D` constraint forces the packed `d` input below `2^32` the same way.
    - Without the nibble check, `W` could make the result *any* 32-bit value. The `nibport` mutant
      shows this (§7).

## 3. Chips and buses

| # | chip | rows | cols | constraints | ports | role |
|---|---|---|---|---|---|---|
| 0 | `PUB` (public) | 1 | 41 | 33 | 1 | `x`, the received digest `H₀ … H₇`. Constraints: `y_k = H_{2k} + X^32 H_{2k+1}`, `x₄ = n`, `x₅ … x₃₁ = 0` |
| 1 | `G` | `160n` | 53 | 33 | 15 | one G-call per **two** rows (§4) |
| 2 | `ADD8` (fixed) | `2^17` | 6 | 0 | 3 | `add8`; sends `(x,y,cin,z,cout)` on `ADD`, `(x,y,cin,z)` on `ADDTOP`, `(x,y)` on `PAIR` |
| 3 | `NIB` (fixed) | 16 | 2 | 0 | 1 | nibbles `0 … 15` on `NIB` |
| 4–23 | `S0 … S19` | `n` | 32 / 35 | 26 / 13 | 6 / 10 (`S19`: 9) | `S_s` row `i`: the 16 state words before half-round `s` of compression `i`, and `m₀ … m₇` (§5) |
| 24 | `FINAL` | `n` | 48 | 22 | 14 | receives half-round 19; `H_k = h_k ⊕ V_k ⊕ V_{k+8}`; byte range check of `H₄ … H₇`; chain link |

Bus kinds are listed in the JSON (`"bus"`). Buses 0–3 are `sub` (lookups), buses 4–7 are `eq`:

| bus | name | message | senders → receivers |
|---|---|---|---|
| 0 | `ADD` | `(x, y, cin, z, cout)` | `ADD8` → `G` (bytes 0–2 of each add) |
| 1 | `ADDTOP` | `(x, y, cin, z)` | `ADD8` → `G` (byte 3) |
| 2 | `PAIR` | `(x, y)` | `ADD8` (every byte pair) → `FINAL` (range check of `H₄ … H₇`) |
| 3 | `NIB` | `(W)` | `NIB` → `G` (wrap cell) |
| 4 | `GIN` | `(τ, A, B, C, D, X, Y)` | `S_s` → `G` phase 0: the call's inputs, packed |
| 5 | `GOUT` | `(τ, A', B', C', D')` | `G` phase 1 → `S_{s+1}` / `FINAL`: the outputs, packed |
| 6 | `MSG` | `(τ, m₀ … m₇)` | `S_s` → `S_{s+1}`; `FINAL` row `i` → `S0` row `i+1` (the chain) |
| 7 | `OUT` | `(H₀ … H₇)` | `FINAL` last row → `PUB` |

Gadgets have one uniform form: constraint `r` is `gate_r(z) · lin_r(z) = 0`. This is CCS with `t = 2`
matrices (gates, linear parts), one term `c = 1`, `S = [0, 1]`, so degree 2. The gates are linear
forms of the view:

| gate | expression | meaning |
|---|---|---|
| always | the view's `1` | every row |
| first | `[r = 0]` | the first row |
| last | `[r + 1 = rows]` | the last row |
| not-last | `1 + [r + 1 = rows]` | every row but the last |
| phase 0 | `1 + φ` | the phase-0 rows of `G` |
| phase 1 | `φ` | the phase-1 rows of `G` |

The whole layout has 1,163 matrix entries.

## 4. The G chip (two rows per G-call)

**Why two rows.** One G is six 32-bit additions, i.e. 24 byte lookups. A chip has at most `2^4` ports
(§2.2), so a one-row-per-G chip is inadmissible. A one-row-per-round chip is too, more so. G is
therefore split into its halves:

| phase | computes |
|---|---|
| 0 | `t = a + b`; `a₁ = t + x`; `d₁ = rotr(d ⊕ a₁, 16)`; `c₁ = c + d₁`; `b₁ = rotr(b ⊕ c₁, 12)` |
| 1 | `t₂ = a₁ + b₁`; `a₂ = t₂ + y`; `d₂ = rotr(d₁ ⊕ a₂, 8)`; `c₂ = c₁ + d₂`; `b₂ = rotr(b₁ ⊕ c₂, 7)` |

Both halves use the same three add slots: slot 1 is `P + Q → T`, slot 2 is `T + M → A'`, slot 3 is
`Cb + D' → C'`. The columns are therefore shared, and the phase gates select the linear constraints.

**Columns (53).**

| columns | content |
|---|---|
| `one`, `φ`, `ψ = 1+φ`, `ρ`, `zero` | constants, phase, tag |
| `A B C D X Y` | packed: received inputs (phase 0); sent outputs `A' B' C' D'`, with `X = Y = 0` (phase 1) |
| `P Q M Cb D'` | operand bytes. Phase 0: `a, b, x, c, d₁`. Phase 1: `a₁, b₁, y, c₁, d₂` |
| `T A' C'` | result bytes. Phase 0: `t, a₁, c₁`. Phase 1: `t₂, a₂, c₂` |
| `k1₁…₃ k2₁…₃ k3₁…₃` | the carries into bytes 1–3 of each slot |
| `W` | the wrap nibble: rot 12 in phase 0, rot 7 in phase 1 |

**Constraints (33).**

| gate | constraints |
|---|---|
| always | `one = 1`; `ψ = 1 + φ`; `zero = 0`; `φ' = φ + 1` (cyclic, so the height is even) |
| first | `φ = 0`; `ρ = 1` |
| last | `ρ = γ^{160n-1}` |
| not-last | `ρ' = γ·ρ` |
| phase 0 | `in_A`, `in_B`, `in_C`, `in_X`: the packed input is `Σ X^{8j}·bytes` |
| phase 0 | `in_D`: `D + Σ X^{8j}A'_j + Σ X^{8j}D'_{j+2} = 0` (`d ⊕ a₁ = rotl(d₁, 16)`) |
| phase 0 | next `P = A'` (4) and next `Cb = C'` (4): the dups of `a₁`, `c₁` |
| phase 0 | `b₁`: next `Q` packs `rotr(Q ⊕ C', 12)` through `W` |
| phase 0 | `in_Y`: next `M` packs `Y` |
| phase 0 | `d₂`: next `D'_j = D'_{j+1} + next A'_{j+1}` (4) |
| phase 1 | `A = Σ X^{8j}A'_j`; `C = Σ X^{8j}C'_j`; `D = Σ X^{8j}D'_j` |
| phase 1 | `B = rotr(Q ⊕ C', 7)` through `W` |
| phase 1 | `X = 0`; `Y = 0` |

**Ports (15).**

| ports | sel | bus | messages |
|---|---|---|---|
| 12 add lookups | `one` | `ADD`, byte 3 on `ADDTOP` | per slot: `(x₀,y₀,zero,z₀,c₁)`, `(x₁,y₁,c₁,z₁,c₂)`, `(x₂,y₂,c₂,z₂,c₃)`, `(x₃,y₃,c₃,z₃)` |
| 1 range check | `one` | `NIB` | `(W)` |
| receive | `ψ` | `GIN` | `(ρ, A, B, C, D, X, Y)` |
| send | `φ` | `GOUT` | `(ρ, A, B, C, D)` |

## 5. Routing, tags and boundaries

**Tags.**
- **Why.** Tags make every `eq`-bus message unique.
- **Values.** Row `r` of `G` has `ρ = γ^r` with `γ = X`. `X` is a generator of `K*`, so it has order
  `2^64 − 1`; `gen-chain-layout.py report` checks this. G-call `q` therefore receives with tag
  `γ^{2q}` and sends with tag `γ^{2q+1}`.
- **S rows.** `S_s` row `i` has `κ = γ^{160i + 8(s−1)}`, pinned at row 0 by `[r = 0]` and stepped by
  `κ' = γ^160·κ`. Its tag cells are `κ·γ^{2g+1}` for the receives from half-round `s − 1` and
  `κ·γ^{8+2g}` for the sends to half-round `s`.
- **MSG link.** `S_{s−1}`'s send tag for slot 0 is `S_s`'s `κ`.
- **FINAL** has `κ = γ^{160i+152}`. This is also `S0`'s `κ` at compression `i + 1`, which closes
  the chain.

**Heights.**
- Every tag chain is pinned at both ends: `[r = 0]` fixes the first value, `[r + 1 = rows]` the last.
  So the heights are forced: `G` has `160n` rows, `S_s` and `FINAL` have `n`, `PUB` has 1.
- A prover cannot drop, add or reorder compressions or G-calls.
  - `PUB` receives `OUT` on every row, and `FINAL` sends it only on its last row.
  - `S0` receives `MSG` with `sel = 1 + [r = 0]`. Its row 0 holds the free start `s`.
  - `FINAL` sends `MSG` with `sel = 1 + [r + 1 = rows]` and `OUT` with `sel = [r + 1 = rows]`.

**Routing.**
- `S_s` reads its message cells in the order of the shuffle. Column step: G-call `g` takes words
  `(g, 4+g, 8+g, 12+g)`. Diagonal step: `(g, 4+(g+1)%4, 8+(g+2)%4, 12+(g+3)%4)`.
- The message words of G-call `g` are `m[σ_r[8h+2g]]` and `m[σ_r[8h+2g+1]]`, or the zero cell for
  indices ≥ 8.
- So the shuffles and the schedule cost no constraints.

**Range check of the output.**
- `FINAL` decomposes `H₄ … H₇` into bytes, checked pairwise on `PAIR`.
- These words contain the `b`-words of the last round, whose `rot 7` wrap is otherwise checked only
  by the next compression.
- Without this check, a wrong wrap bit `e` would add `e·(1 + X^32)` to `H_{2k}`, and the packing of
  `y` would carry it into `H_{2k+1}`.
- `H₀ … H₃` are XORs of add outputs, so they are range-checked already.

**The witness is unique** given `s`.
- Every cell is a constant, a pinned counter, a received value, a lookup output, or the unique
  byte decomposition of a value below `2^32`.
- `check-chain.py` (b) confirms this: every sampled single-cell change is rejected.

## 6. Cell counts (`gen-chain-layout.py report`)

| part | cells per compression |
|---|---|
| `G` | 8,480 |
| `S0 … S19` | 697 |
| `FINAL` | 48 |
| **total** | **9,225** |

Fixed: `ADD8` 786,432 and `NIB` 32, so 786,464 fixed cells. `PUB`: 41.

| n | cells | least class by cells | fixed-table floor | `k_min` |
|---|---|---|---|---|
| 2^8 | 3,148,105 | 22 | 24 | **24** |
| 2^10 | 10,232,905 | 24 | 24 | **24** |
| 2^11 | 19,679,305 | 25 | 24 | **25** |
| 2^12 | 38,572,105 | 26 | 24 | **26** |

- **The table floor.** `786,464 > 2^19` fixed cells force `k ≥ 24` for every `n`; at class 24 the
  cap is `2^(k−4)`.
- **The largest chain at class 24** is `n = ⌊(2^24 − 786,505) / 9,225⌋ = 1,733`.
- **Measured.** `check-chain.py` measures the cells of real witnesses (n = 4: 823,405; n = 16:
  934,105; n = 256: 3,148,105), and they agree with the formula `9,225·n + 786,505`.

**n = 2^12 does not fit class 24** (O-3).
- It would need at most `(2^24 − 786,505)/4,096 ≈ 3,904` cells per compression, i.e. about 49 per
  G-call.
- The 24 add lookups alone produce 24 result bytes and 18 carries per G-call.
- At class 25 it would need about 7,999 per compression; this layout has 9,225 (13 % more).

## 7. What is tested

**`check-chain.py experiments`** (log in `docs/stages/S6a-RESULT.md`):
- **(a)** random secrets: `rel` holds, `y = blake2s256^n(s)` by `hashlib`, `Admissible 24` holds
  and `Admissible 23` fails.
- **(b)** single-cell mutations, every chip and then uniform: all rejected.
- **(c)** one mutant per mechanism. Each admits a wrong witness (`y ≠ blake2s256^n(s)`) that the real
  layout rejects:

| mutant | what is removed | the wrong chain it accepts |
|---|---|---|
| `gate` | the gate of `out_C` dropped (one matrix entry) | a wrong `c₂` in the last G-call |
| `addport` | one `ADDTOP` port dropped | a wrong top byte of `a₂` |
| `nibport` | the `NIB` port dropped | `W` makes `b₂` arbitrary |
| `gouttag` | the tag column dropped from the `GOUT` link | two G-calls' outputs swapped |
| `fixed` | `ADD8` no longer fixed | a false row appended |
| `nolast` | the last-row pins (`rho_last`, every `kappa_last`) | the `(n−1)`-chain claimed as `n` |
| `selpin` | the selector pins `nf` (`S0`) and `nl` (`FINAL`) | the last compression restarted from a fresh `s'` through silent selectors |
| `pairport` | `FINAL`'s `PAIR` ports | a wrong rot-7 wrap bit aliasing into `y₂` |

**The kernel** (`RecursionFast/Controls/Chain.lean`):
- **Completeness of the one-G-call harness.** `rel` is decided for G-calls 0 and 79, and proved
  with the real `add8` table, its lookups certified row by row. The honest statements agree with
  `Blake2s.mix`.
- **Named faults.** A wrong input byte (gadget), a wrong add byte (the add lookups), a wrong output
  (`GOUT`), and the review's rot-7 wrap attack (only `PAIR` rejects it; the harness's `PUBG`
  range-checks its four outputs as `FINAL` does).
- **Structure.** `G_link`: the harness's G chip is `L_chain`'s up to the last-row pin's
  constant. `L_chain(16)` is admissible at 24 and not at 23.
- **Not proved.** The kernel does not prove that the harness computes G (`rel → MixStmt`), and
  nothing about whole chains. That is the Python oracle's job above.

# harness/: the benchmark leaf layout `L_chain(n)` (Stage 6a)

The relation of the leaf benchmark is `R_chain(y, n; s) : blake2s256^n(s) = y` (DESIGN §7.1).
`L_chain(n)` arithmetises it as a contract `Layout K`. The design is in [`CHAIN-LAYOUT.md`](CHAIN-LAYOUT.md);
the results are in `docs/stages/S6a-RESULT.md`.

| file | what |
|---|---|
| `gen-chain-layout.py` | generator: the layout, the honest witness and statement, the one-G-call harness, the mutants, the cell report |
| `check-chain.py` | independent pure-Python evaluator of `Layout.rel` / `Layout.Admissible` (the differential oracle) and the experiments (a)–(c) |
| `render-layout.py` | JSON → Lean definitions (`Layout K`, `List (Table K)`, `Fin 32 → K`) |
| `render-controls.sh` | regenerates `examples/` and `RecursionFast/Controls/ChainData.lean` (deterministic) |
| `examples/` | `chain-n{1,4,16}.layout.json` (`chain-n16` is the source of the rendered `Lchain`); witnesses and statements for n = 1 and 4; the one-G-call harnesses `gcall0`, `gcall79` (trimmed add table) and `gcall0-add8` (full table). Example secret: bytes `00 01 … 1f` (public; an example only) |

All scripts take paths as arguments. Run them with `python3 -I` (no third-party modules).

## Generate, check, render

```sh
python3 -I harness/gen-chain-layout.py layout  --n 1024 L.json              # L_chain(1024)
python3 -I harness/gen-chain-layout.py witness --n 1024 --secret-file SECRET W.json X.json
python3 -I harness/check-chain.py check L.json W.json X.json --k 24        # Admissible 24 and rel, per clause
python3 -I harness/gen-chain-layout.py report --n 256 1024 2048 4096       # cells per chip, least class
python3 -I harness/check-chain.py experiments --gen harness/gen-chain-layout.py --dir "$(mktemp -d)" \
    --n 4 16 256 --seeds 5 --mutations 300 --log LOG                       # the differential tests
harness/render-controls.sh                                                 # examples + ChainData.lean
python3 -I harness/render-layout.py OUT.lean "doc" NAME=L.json[,W.json,X.json] ...
```

Notes on the commands:

- **The secret** (`--secret-file F`, or `-` for stdin) is a file of 64 hex digits. It is never a
  command-line argument, which other processes could read (S6a-m4). A **witness file is secret
  material**: row 0 of `S0` holds the start `s`. The experiments pass secrets on stdin.
- **`check --flip T R C` / `--xflip I`** xor `1` into one witness cell or statement cell before
  checking; **`--xor T R C HEX` / `--xxor I HEX`** xor a K element. They replay the Lean negative
  controls and the review's wrap attack.
- **`mutant --kind KIND`** writes a layout with one mechanism removed, together with a wrong
  witness that it admits. The experiments check both halves of the claim: the mutant accepts the
  witness and the real layout rejects it. The kinds are `gate`, `addport`, `nibport`, `gouttag`,
  `fixed`, `nolast`, `selpin` and `pairport` (`CHAIN-LAYOUT.md` §7).
- **`mini --secret-file F --call Q [--full-table]`** writes the one-G-call harness. Its public chip
  `PUBG` sends the inputs of G-call `Q` of the chain from the secret and receives the outputs,
  which it decomposes into bytes checked on `PAIR`, as `FINAL` does. Its statement is
  `(a, b, c, d, x, y, a', b', c', d', 0, …)`.

## JSON schemas

K elements are strings of **16 lowercase hex digits**: the 64-bit word `K.bits` in ordinary
(big-endian digit) notation, polynomial basis (bit `i` is the coefficient of `x^i`).

**Layout** (`"schema": "recursion.fast/layout/1"`) is the `Layout K` of
`Contract/Layout.lean`, field by field:

```
{ "schema": "recursion.fast/layout/1", "name": str, "params": {...informational...},
  "chips": [ { "name": str, "cols": int, "colnames": [str] (informational),
               "gadget": { "cons": int, "t": int, "q": int,
                           "M": [ [ [row, col, K], ... ]  x t ],   // sparse, entries at a position add up
                           "S": [ [j, ...]  x q ],                 // multiset of matrix indices, |S_i| = degree
                           "c": [ K  x q ],
                           "names": [str] (informational: one per constraint) },
               "ports": [ { "bus": int, "send": bool, "sel": int, "msg": [int] } ],
               "fixed": null | {"kind": "add8"} | {"kind": "explicit", "rows": [[K]]} } ],
  "bus": ["sub" | "eq", ...],      // kind of bus b for b < len; "eq" beyond
  "busnames": [str] (informational), "pub": int }
```

- **Typing.** `row < cons` and `col < 2·cols + 3` (the view: the row, the next row, then `1`,
  `[r = 0]`, `[r + 1 = rows]`). Every `S` entry is `< t`, and `|M| = t`, `|S| = |c| = q`. The
  checker rejects JSON that would not typecheck as a Lean `Layout K`.
- **Table kinds.** `add8` is the closed-form table of `CHAIN-LAYOUT.md` §2, with `2^17` rows and 6
  columns: row `r` is `(1, r mod 2^8, ⌊r/2^8⌋ mod 2^8, ⌊r/2^16⌋, sum mod 2^8, ⌊sum/2^8⌋)`.
  `explicit` lists its rows.

**Witness** (`"schema": "recursion.fast/witness/1"`):
`{"tables": [T, ...]}`, one per chip. `T` is one of:

- `{"rows": R, "cells": [[K]]}`, where `R` **must equal** the number of listed rows;
- `{"kind": "add8"}`, the `add8` table itself;
- `{"kind": "add8", "extra": [[K]]}`, `add8` followed by extra rows (used only by the `fixed`
  mutant).

One reading, enforced by both readers: the checker (`table_of`) and the renderer (`table_lean`)
reject `R ≠ len(cells)` and any K string that is not exactly 16 lowercase hex digits. A row may
list fewer cells than the chip has columns; a cell outside the listed cells is `0`, which is also
the Lean rendering (`tabOf`).

**Statement** (`"schema": "recursion.fast/statement/1"`): `{"x": [K x 32], ...informational}`.
For `L_chain(n)` the statement is `x = (y₀, y₁, y₂, y₃, n, 0, …)`, where `y_j` is bytes `8j … 8j+7`
of `blake2s256^n(s)`, little-endian.

**Lean** (`render-layout.py`):

- **Notation.** Elements are written `kx 0x…` and explicit tables `tabOf [[…]]`. `add8` is a
  closed-form `Table K`.
- **Definitions.** Each chip is a `def NAME_chipI : Chip K`, the layout is
  `def NAME : Layout K`, the witness `NAME_wit` and the statement `NAME_stmt`.
- **Copying only.** The renderer copies numbers and evaluates nothing.
- **Not yet in the challenge renderer.** `scripts/render-challenge.py` (v0.3) has no layout
  placeholder yet. A `{{layout:KEY}}` that calls this renderer is the Stage 7 integration.

## Cell counts

These come from `gen-chain-layout.py report`, and the measured witnesses agree:

| n | cells | k by cells | `k_min` (with the fixed-table cap) |
|---|---|---|---|
| 2^8 | 3,148,105 | 22 | 24 |
| 2^10 | 10,232,905 | 24 | 24 |
| 2^11 | 19,679,305 | 25 | 25 |
| 2^12 | 38,572,105 | 26 | 26 |

- **Per compression:** 9,225 cells (`G` 8,480, `S0 … S19` 697, `FINAL` 48).
- **Fixed:** 786,464 cells (`ADD8` 786,432, `NIB` 32). These need `k ≥ 24` (cap `2^(k−4)`).
- **Matrix entries:** 1,163, against the cap `2^(k+4)`.
- **The largest chain at class 24** is n = 1,733.

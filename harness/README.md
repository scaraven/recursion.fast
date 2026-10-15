# harness/: the benchmark layout `L_chain(n)` (Stage 6a) and the badge path (Stage 6b)

The relation of the leaf benchmark is `R_chain(y, n; s) : blake2s256^n(s) = y` (DESIGN §7.1).
`L_chain(n)` arithmetises it as a contract `Layout K`. The design is in [`CHAIN-LAYOUT.md`](CHAIN-LAYOUT.md);
the results are in `docs/stages/S6a-RESULT.md`. The badge path (the compiled `verify` and `index`,
the benchmark runner, DESIGN §6.3, §6.4, §7.4) is [below](#the-badge-path-stage-6b); its results
are in `docs/stages/S6b-RESULT.md`, the reference machine in [`reference-machine.md`](reference-machine.md).

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
- **In the challenge renderer** (Stage 6b). `scripts/render-challenge.py`'s `{{layout:KEY}}`
  placeholder validates a layout JSON strictly (below) and renders it with this file's emitter
  (`layout_lean`); `RecursionFast/Challenge/R.lean.in` renders the submitted `C_V` this way. A
  fixed table may carry an informational `"note"` (the trimmed tables of `gcall0`/`gcall79` do).

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

## The badge path (Stage 6b)

DESIGN §7.4 step 3: after the comparator and the gate, the organiser builds the compiled verifier
and indexer against the submission, indexes, and runs the benchmark (§6.3) with the agent's native
prover. Every command takes paths as arguments; Python runs with `-I`.

| file | what |
|---|---|
| `lean/RecursionFastHarness/Driver.lean` | `verifyMain` (`verify VKC STMT TAPE`: exit 0 `ACCEPT` iff `NARG cfg P` accepts, 1 `REJECT`, 2 malformed key/statement) and `indexMain` (`index LAYOUT.json VKC_OUT`: writes `VKc.toBytes` of `index cfg P L`, prints `VKc.digest cfg` in hex) |
| `lean/RecursionFastHarness/Twin.lean` | `harness_twin P' cfg' := S`: the executable twin of a submission whose `ε` (or prover) is noncomputable; same `n`, `shape`, `vkLen`, `VK`, `idxShape`, `IDX`, `verify` terms |
| `lean/RecursionFastHarness/LayoutJson.lean` | layout JSON → `Layout K`, the renderer's checks and table constructions; CI checks reader = renderer (`probes/s6b/layout/check.sh`) |
| `lean/Main.lean.in`, `badge-main.py` | the executables' main module: imports the submission module, defines the twin, states (kernel-checked `rfl`) that the twin's `NARG` and `index` are the submission's |
| `lean/LinkCheck.lean` | `harness-linkcheck`: imports every organiser library; `scripts/org-build.sh` builds it (prebuilding every object file a badge executable links) and runs it (start-up cost of the organiser modules) |
| `badge-build.sh` | builds `harness-verify`/`harness-index` against a module in a fresh sandboxed tree (the gate tree's stage 3a without comparator and gate) |
| `mk-tree.py` | a fresh tree's `lakefile.toml` and `lake-manifest.json` (the organiser package by path; challenge, submission, badge mains), shared by `scripts/harness.sh` (with the module-root freshness check) and `badge-build.sh` |
| `run-benchmark.py` | the benchmark runner: `run`, `compare`, `record`, `selftest` |
| `smoke/` | the NOT SECURE smoke protocol (`cmpToy`, O-10; `RecursionFastSmoke.lean`), its generated mains (`SmokeVerify.lean`, `SmokeIndex.lean`; lake exes `smoke-verify`, `smoke-index`) and its "native prover" `toy_prover.py` |
| `reference-machine.md` | the measurement policy (§6.4) as the organiser's per-season checklist, and the first noise measurement |

### Building the executables

```sh
scripts/org-build.sh .lake/org                       # organiser package, incl. RecursionFastHarness + harness-linkcheck
# production (gate tree, after comparator and gate; scripts/harness.sh stage 3a):
scripts/harness.sh --org .lake/org --gate RecursionFast.Challenge.certified \
  --computable RecursionFast.Challenge.submission --badge-build RecursionFast.Challenge.submission \
  [--bench BENCH.json --claim CLAIM.json --stub RecursionFast/Challenge/R.lean.in] \
  CHALLENGE.lean SOLUTION_DIR CONFIG.json
# a module outside the harness (smoke test, local checks):
harness/badge-build.sh --org .lake/org --work DIR [--certified-c LAYOUT.json] SRC_DIR MODULE SUBMISSION
python3 -I harness/badge-main.py OUT.lean MODULE SUBMISSION verify|index [--certified-c C.lean]   # the main module only
lake build smoke-verify smoke-index                                             # the smoke protocol, in this tree
```

- **The source rule before everything** (`scripts/source-rule.py`, S6b-M3, S9D-M1). In each
  fresh tree, before anything of the submission is built, the harness rejects submission sources
  that use elaboration-time code (`run_meta`, `#eval`, `elab`, `macro`, `initialize`, `unsafe`,
  `persistentEnvExtensionsRef`, `import Lean`, `open Lean`, Qq's `by_elabq`, …; the list is the
  script's docstring). It raises the bar against forging the emitted code
  (`probes/s6b/gate/ForgeRaw.lean`, which no gate rule sees); the sound fix is O-12. **Two nets**,
  each binding: a lexer that follows Lean's (raw strings only for `r#…"`, every string read both
  plainly and as an interpolation, nested comments, character literals; **fail closed**: anything
  open at the end of the file, and a string whose end depends on interpolation, is a finding), and
  a raw word scan of the bytes, comments and strings included (no lexer can desynchronise it; a
  rejected word in a comment is a finding too, reword it). Allowed are `#check`, `#print`,
  `#reduce`, `#guard_msgs`, the literals `#[…]` and `#v[…]` (Clean's vectors), notation,
  attributes such as `simp` and `elab_as_elim`, and Library names such as `run_mono`; Mathlib's
  `#s` is not (write `s.card`), nor a string inside `{…}` of an interpolation.
  `tests/source-rule/check.sh` (CI step 1) holds one fixture per rejected form (each net alone
  must report every code-level one), the S9 review's lexer bypasses and the forgeries (each net
  alone must catch them), and a file of allowed forms; `scripts/TokenSweep.lean` with
  `tests/source-rule/sweep.py` (CI step 6) requires every keyword of the allowed closure's token
  table to be rejected or listed in `tests/source-rule/reviewed-tokens.txt`. `--source-rule off`
  exists only for the layer regressions in `tests/pipeline/`.
- **The claim binds the benchmark** (S6b-M2). With `--bench`, `--claim` and `--stub` are required:
  the harness copies the claim and its files into the work directory, re-renders the stub with it
  and requires the challenge to be that rendering, byte for byte; then it writes the benchmark
  configuration's `k`, `cfg.hash`, `claim` (digests) and `layouts.C` from that claim (so `C` is the
  very file rendered into the certified `C`), and the sandbox (`--landrun`), whatever the bench
  file says. **One reader for the recursion key** (S9D-m4): for a board-R claim the harness renders
  the claim's `C` with the challenge renderer (stub line `{{layout:C}}`) into `harness-index`
  (`badge-main.py --certified-c`), and the runner indexes that compiled `C`
  (`harness-index --certified-C VKC_OUT`, `index_C = "certified"`), not a parse of the file.
  **Secrets** (S9I-m4): `--secrets` is refused; the runner draws fresh chain starts from the OS for
  every evaluation and holds them itself.
- **External tools** (S9F-m2): `scripts/tools.env` (sourced by `harness.sh` and `ci.sh`) gives
  `COMPARATOR_HOME` (leanprover/comparator at `d03acab`, built) and `COMPARATOR_NANODA`
  (ammkrn/nanoda_lib at `3a24072`, `cargo build --release`) their defaults; without them the
  harness stops with a message naming the variables.
- **The gate before them** (`scripts/Gate.lean`). Rule 4 requires compiled code for the badge-path
  fields only (S6-A12). Rules 3, 6, 7 (S7-M1) keep a submission away from the compiler: no
  code-substituting or compiler-changing attribute (`implemented_by`, `extern`, `export`, `init`,
  `csimp`, `cpass`, `computed_field`); no import outside `scripts/import-allowlist.txt` (the import
  closure of `Mathlib`, the contract, the library and the controls; written by `gate --closure` in
  `scripts/org-build.sh`, checked current by CI); no definition that refers to the compiler's or
  the environment's API. The Clean frontend (S6b-A11, S6b-A17) may be imported for circuit proofs
  (`scripts/import-frontend.txt`), but never on the badge path: the executables import only the
  module of the badge root (board L: `RecursionFast.Challenge.submission`; board R:
  `RecursionFast.Challenge.leaf`), whose imports must stay in the compiler-free closure (rule 8),
  and no badge-path field may call Clean code (rule 9). `scripts/harness.sh` passes
  `--allowed-imports`, `--frontend-imports` and (with `--badge-build CONST`) `--badge-root CONST`
  by default, and requires `--org`.
- **How the gate tree builds them.** With `--badge-build SUBMISSION`, `scripts/harness.sh` writes
  `badge/HarnessVerify.lean` and `badge/HarnessIndex.lean` (from `lean/Main.lean.in`, importing
  the solution module `solution_module` of the comparator config) and two `[[lean_exe]]` blocks
  into **both** fresh trees, so the comparator's and the gate's trees have the same lakefile;
  neither the comparator nor the gate's `lake build <solution>` builds them. After the gate
  passes, stage 3a runs `lake build harness-verify harness-index` in the gate tree under the
  sandbox (only the tree's `.lake` is writable; `TMPDIR` inside it for the linker) and checks that
  every artifact bound to the comparator-verified build (A7-M3) is unchanged. The executables run
  the solution's compiled code from that bound build.
- **Object files.** Linking needs the object file of every module in the executable's import
  closure. The organiser package and the shared packages are read-only in the sandbox, so
  `scripts/org-build.sh` prebuilds the organiser closure's objects (`harness-linkcheck`), and the
  reference machine prebuilds all of Mathlib's once (`lake build mathlib/Mathlib:static`, S6b-A18,
  `reference-machine.md`): a submission may import any Mathlib module.
- **Start-up.** A compiled executable evaluates every closed term of every imported module when
  it starts. `harness-linkcheck` fails `org-build.sh` if the organiser modules are expensive to
  initialise; the submission's own closed terms are timed with it (they are inside the timed
  region of every run).

### The benchmark runner

```sh
python3 -I harness/run-benchmark.py run --config BENCH.json --out RESULT.json [--workdir DIR] [--keep]
python3 -I harness/run-benchmark.py record NEW.json STANDING.json [--margin 0.03]   # screening: exit 0 iff a TENTATIVE record
python3 -I harness/run-benchmark.py compare --standing STD.json --challenger NEW.json [--pairs 5] [--margin 0.03] \
    --out CMP.json [--workdir DIR]                            # the paired confirmation (one session); exit 0 iff RECORD
python3 -I harness/run-benchmark.py compare --calibrate --standing CFG.json --pairs 10 --out CAL.json   # sigma, pairs needed
python3 -I harness/run-benchmark.py selftest --lean-data RecursionFast/Controls/RecursionData.lean --gen harness/gen-chain-layout.py
```

**Config** (JSON; every key but the first six has the default shown):

```
{ "k": 24,                                                 // the declared class (from the claim, S6b-m2)
  "verify": [exe], "index": [exe], "prover": [argv...], "gen": "harness/gen-chain-layout.py",
  "layouts": {"C": "C_V.layout.json"},                       // board R
  "claim": {"digestC": hex64, "digestL": hex64},             // board R: the declared key digests
  "boards": ["L", "R"], "cfg": {"hash": "blake2s"},          // no arity: the submission's (S6b-m5)
  "tree": {"n": 1024, "leaves": 64}, "leafboard": {"256": 16, "4096": 16}, "repeats": 3,
  "classes": {"256": 24, "1024": 24, "2048": 25, "4096": 26},   // least class of L_chain(n), S6-A1
  "budgets": {"index_total_s": 3600, "leaf_s": 120, "step_s": 600, "root_s": 60, "verify_s": 60,
              "mem_kb": 48000000, "prover_build_s": 3600, "overhead_s": 600, "per_process_s": 2},
              // no eval_s: the whole-evaluation cap is DERIVED from these (S9F-M5; `budget` in the result)
  "caps": {"tape_R": 1048576, "tape_L": 131072},
  "dos": {"tapes": 1000, "max_len": 1048576, "seed": null},     // alternately leaf key and recursion key
  "canaries": {"per_kind": 8},                               // S9I-m3: canaries of 8 proofs per kind and run
  "index_C": "json" | "certified",                           // S9D-m4: harness.sh forces "certified" for board R
  "hardware_id": "…", "submitter": "…",                      // S9I-m5, S9I-M3 (the season's id; the entrant)
  "sandbox": "scripts/bwrap-landrun.sh",                     // REQUIRED: `run` refuses to start without it (S6b-M1)
  "sandbox_ro": [paths...],                                  // what a step may read besides /usr, /etc (S6b-m3)
  "prover_build": null | {"cmd": [argv...], "dir": "..."} }
```

**Ranked board** (S9I-M1, S9I-M2). **R is the only ranked board**, scored by `S_rec`, the slowest
level group: the max over level 2, level 3 and levels 4–6 (pooled, 7 steps) of the median over
runs of the per-run median step time; the per-level medians are published (`S_by_level`). L
(`S_leaf`) and W (`S_wrap`) are published, unranked (`"ranked": false`): a leaf's witness is its
32-byte start, so on L no proof-size cap separates "send the start, recompute the chain" from a
SNARK; and a median over all levels ≥ 2 would be decided by level 2, whose children are the
unranked wrap steps' proofs (wrap proofs expensive to prove and cheap to verify would make level
2 cheap without lowering the steady-state step).

**Classes and boards** (S6-A1, S7-M2). A declared `k` below the class of `L_chain(tree.n)` (24)
is rejected up front. A leaf-board size whose layout needs a class above `k` is skipped, not
failed: by default the leaf board is `n ∈ {2^8, 2^10}` (the 64 tree chains are its `2^10`
instances), and `2^12` (class 26) runs only at `k ≥ 26`. Boards are judged separately: a failure
only board L depends on (a leaf-board chain, the `2^17`-byte cap) rejects board L; one only the
tree depends on (`C_V`'s key, the declared digests, a step, the root) rejects boards R and W; a
failure of a tree chain's leaf, of indexing `L_chain`, of a canary, of the budget or of the DoS
column rejects every board. The run exits 0 iff at least one requested board is accepted.

**Canaries** (S9I-m3). Untimed, for the first `canaries.per_kind` proofs of each kind (leaf, wrap,
node, root) in each run, `verify` must reject the proof with one byte appended, with its last
byte removed (the tape grammar, for every protocol), under the statement with one bit flipped
(`y` of a leaf, `d2` of a node) and under the other key (by soundness). An accepted canary
rejects the evaluation: it catches an accept-all or input-blind executable, not a keyed forgery
(only O-12 does). The DoS tapes alternate between the leaf key and the recursion key.

**Budgets** (S9F-M5). The per-step caps (`leaf_s` 120 s, `step_s` 600 s, `index_total_s` 1 h,
…) are the policy; the whole-evaluation cap is derived: every process the evaluation may start
at its cap, plus `overhead_s` and `per_process_s` per process (`budget.eval_s` and its
`derived_from` in the result). An entry that keeps every per-step cap is never rejected by the
whole-evaluation cap. `budgets.eval_s` in a config is an error.

**Isolation and memory** (fix pass, S6b-M1, S6b-m1, S6b-m3). `run` refuses to start without the
sandbox and without a memory cgroup (`systemd-run --user --scope`). Every step runs in its own
cgroup with `MemoryMax` = `mem_kb` and `OOMPolicy=continue` (the whole process tree; its
`memory.peak` is reported, and any `oom_kill` in it rejects: "killed at the memory cap"), inside
`bwrap-landrun.sh --minimal-root`: readable are only `/usr`, `/etc`, a fresh `/tmp`, the
executables' directories, the files the prover's argv names and `sandbox_ro`; writable only the
step directory; no network; own PID namespace. The wall time is the sandboxed process's (measured
by an organiser shell in the cgroup, outside the sandbox).

**Prover interface** (S6b-A9). `PROVER... leaf|node`: the mode is the **last** argument (the
runner appends it to the configured argv). It runs in a fresh step directory (the only writable
path; no network; the run directory, with every other chain's secret, is hidden: `bwrap-landrun.sh --hide`),
and must write `proof.bin`:

- `leaf`: `layout.json` (`L_chain(n)`, schema `recursion.fast/layout/1`), `vkc.bin` (the leaf
  key bytes from the organiser's indexer: `8·vkLen` bytes of `VK L`, then the 32-byte index root),
  `stmt.bin` (256 bytes: 32 elements, 8 bytes little-endian each) and `secret.hex` (the chain's
  start `s`: 64 lowercase hex digits and a newline). The prover generates the witness tables from
  `s` itself, **inside the timed region**: witness generation is part of proving, the same for
  every entry (the tables are a function of `s`, S6-A4). No witness file is provided.
- `node`: `layout.json` (`C_V`), `vkc.bin` = `vkC.bin` (the recursion key), `vkL.bin`, `stmt.bin`
  (the aggregate statement `nodeStmt`, computed by the runner), `child1.stmt`, `child1.proof`,
  `child1.tag` (`leaf` or `node`), and the same for `child2`.

**Verifier interface.** `VERIFY vkc.bin stmt.bin proof.bin` in a fresh directory holding only
those three files (never a secret); exit 0 = accept, 1 = reject (anything else is a crash).

**Result** (`--out`): `verdict` (`ACCEPT` iff some board is accepted), `accepted_boards`,
`reason`, `ranked` (board R's `S_rec` and verdict), `scores` (per board: `ranked`, `verdict`,
`reason`, and `L.S_leaf` with per-`n` medians and the skipped sizes, `W.S_wrap`, `R.S_rec` with
`S_rec_by_group` and `S_by_level`; `DoS` by key; `canaries`), `runs` (every leaf and step: prover
and verifier wall time, proof size, peak memory), `instances` (with `secrets_sha256`), `indexing`
(times, digests, the source of `C`'s key), `budget` (the derived cap), and what it was measured
under (S9I-m5): `config_sha256` (the season's configuration: everything but the entry's keys),
`hardware_id`, `machine`, `entry` (sha256 of `verify`, `index`, the prover's files and build
directory; the claim; the layout of `C`) and `entry_id`. `record` and `compare` refuse to compare
results or configurations whose `config_sha256` or `hardware_id` differ, and an entry with
itself (except `compare --calibrate`).

**Records** (S9I-M3, `reference-machine.md` §4). `record NEW.json STANDING.json` only screens: a
`S_rec` at most `0.97 ×` the standing one is a *tentative* record. It is confirmed by `compare`:
the standing entry and the challenger in **one session**, on **one fresh set of instances**,
interleaved run by run (standing, challenger, …), **5 pairs**; a record iff the median over pairs
of `S_rec(challenger) / S_rec(standing)` is at most `0.97`. `compare --calibrate` runs self-pairs
of one entry and reports `sigma_log_ratio` and `pairs_needed_for_margin` = `⌈(3.75·σ/m)²⌉`.

### Challenges

`RecursionFast/Challenge/L.lean.in` (board L) and `R.lean.in` (board R), rendered by
`python3 -I scripts/render-challenge.py STUB claim.json OUT.lean`. Claim keys: L `k`, `hash`,
`arity`, `image` (`{"code", "data"}` paths); R also `C` (layout JSON path), `C.chips`,
`C.entries`, `digestC`, `digestL`. Definition names: L `submission`; R `leaf` (the protocol part,
in a module that does not import Clean) and `submission`, with `submission.toSubmission = leaf`. `scripts/dummy-claim.py STUB OUT` writes a dummy claim;
`scripts/test-render.sh [OUTDIR]` runs the renderer's 50+ malformed-claim cases;
`python3 -I scripts/toy-solution.py OUTDIR` re-makes the v2 toy comparator pair in `audit/`.
`python3 -I scripts/source-rule.py [--net lexer|raw|both] DIR` runs the source rule on the `.lean`
files under `DIR` (exit 1 and one line per finding); `tests/source-rule/check.sh` runs its
fixtures; `(cd ORG && lake env lean --run SCRIPTS/TokenSweep.lean import-allowlist.txt
import-frontend.txt) > TOKENS` and `python3 -I tests/source-rule/sweep.py scripts/source-rule.py
TOKENS tests/source-rule/reviewed-tokens.txt` run the keyword sweep.

### The olean manifest (S9F-M2)

`scripts/olean-manifest.sha256` covers exactly the trusted closure: the toolchain's files, the
package modules of the organiser's import allowlist and of the frontend closure (both written by
`scripts/org-build.sh`), and the contract and vendored modules of the organiser build. Regenerate
it after a trusted change, on the machine of record, from a clean organiser build:

```sh
scripts/org-build.sh .lake/org
python3 -I scripts/olean-manifest.py gen --org .lake/org --closure .lake/org/import-allowlist.txt \
  --closure .lake/org/frontend-closure.txt scripts/olean-manifest.sha256
```

CI step 3 regenerates it into a scratch file and requires it to equal the committed one.

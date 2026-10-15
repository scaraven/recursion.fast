# S5 RESULT: recursion (verifier as a circuit) and the certificate types

Stage 5 is DESIGN §5 (statement format, `aggOK`, the fixed point, `RecursionEntry`) and the
submission/certificate types of §3.3 and §8 (§11 step 6). One agent implemented it on
2026-10-14/15. Nothing is committed.

- **New files:** `Contract/Recursion.lean`, `Contract/Certificate.lean` (trusted);
  `Library/Recursion.lean`; `Controls/RecursionData.lean`, `Controls/Recursion.lean`,
  `Controls/RecursionNode.lean`, `Controls/Certificate.lean`; `probes/s5/recursion_ref.py`
  (independent Python reference).
- **Appended:** two imports to `RecursionFast/Contract.lean`, four to `Controls.lean`, one to
  `Library.lean` (each re-read before appending); S5-A1 … S5-A6 to `docs/DESIGN-AMENDMENTS.md`.
- **Not touched:** `harness/`, `Controls/Chain*.lean` (Stage 6a), `docs/DESIGN.md`, every
  earlier contract file.

## Headline

(Superseded in part by the **Decision pass** at the end: `RecursionEntry.live` (S5-A7) removes the
vacuous certificate of S5-A2, and `d2` follows `cfg.hash` (S5-A8).)

- **Trusted lines:** `Recursion.lean` **44** code lines (target ≤ 70), `Certificate.lean` **23**
  (≤ 40). The contract without `Compile.lean` and `Hash/` is now **518** code lines (budget 850).
- **Checks:** `lake build` green (113 s wall incl. replays; the two kernel files build in
  parallel, 58 s and 85 s); `lake build RecursionFastBridge gate axiomaudit` green; axiom audit
  **PASS**; `check-hygiene.sh` OK; `check-vendor.sh` OK. `#print axioms` on all 56 Stage 5
  declarations: within `propext`, `Classical.choice`, `Quot.sound` (`logs/S5/axioms.log`).
- **`aggOK` is satisfiable** (S1-A12(c)), shown three ways on `cmpToy`: a two-leaf node, a node
  with a node child, and through compile completeness (`aggOK_sat_of_complete` instantiated).
- **Two deviations in the trusted definitions** (S5-A1: `aggOK` also requires 32-byte key roots,
  else `complete` is unsatisfiable; S5-A3: the key digests are declared but not certified, the
  kernel cannot commit a real index) and **one finding** (S5-A2: a `SubmissionR` with a
  `CertificateR` exists for which no node can be proved; the benchmark is the backstop).

## Files

Code lines from `scripts/loc.py` (`logs/S5/loc-s5.log`, `logs/S5/loc-contract.log`); build times
from `lake build` (`logs/S5/build-final.log`), memory from `lake env lean` under `/usr/bin/time`.

| File | Status | Code | Total | Thm | Build | Contents |
|---|---|---:|---:|---:|---:|---|
| `Contract/Recursion.lean` | **TRUSTED, new** | 44 | 126 | 0 | 3.0 s | `digestToSlot`, `Stmt.slot`, `Stmt.ofSlots`, `Tag`, `NodeWitness`, `nodeStmt`, `child`, `aggOK`, `rootOK`, `RecursionEntry` |
| `Contract/Certificate.lean` | **TRUSTED, new** | 23 | 75 | 0 | 3.3 s | `Submission`, `SubmissionR`, `Declared`, `DeclaredR`, `Certificate`, `CertificateR` |
| `Library/Recursion.lean` | untrusted, new | 149 | 253 | 22 | 12 s | slot and digest round trips, `aggOK_iff`, `child_iff`, `aggOK_leaves`/`_nodes`, satisfiability, root lemmas |
| `Controls/RecursionData.lean` | controls, new | 134 | 208 | 2 | 5.6 s | literals (tapes, statements, node witnesses), `Cbad`, `#guard`s against Python and `prove` |
| `Controls/Recursion.lean` | controls, new | 60 | 145 | 21 | 58 s, 5.6 GB | two leaves, negatives, root check, `Cbad`, `unsat` |
| `Controls/RecursionNode.lean` | controls, new | 37 | 81 | 7 | 85 s, 7.0 GB | node child, key negatives, satisfiability via `narg_complete` |
| `Controls/Certificate.lean` | controls, new | 33 | 73 | 7 | 4.1 s, 2.6 GB | toy certificate, the vacuous recursion-board submission |
| `probes/s5/recursion_ref.py` | probe | — | 91 | — | < 1 s | independent reference (`hashlib.blake2s`), output `logs/S5/python-ref.log` |

## The trusted definitions

### `Contract/Recursion.lean`

- **`digestToSlot d j := K.ofBytes (d.drop (8j))`**: limb `j` is digest bytes `8j … 8j+7`,
  little-endian. `K.ofBytes` (`Compile.lean`, S3-A5) is reused, not redefined.
- **`Stmt.slot x i j := x (4i + j)`, `Stmt.ofSlots s i := s (i / 4) (i % 4)`**: slot `d_i` is
  elements `4i … 4i+3` (cells `0 … 31` of row 0 of the public chip).
- **`D` is `VKc.digest cfg`** (S3-A8), used as is; no new definition.
- **`Tag := leaf | node`; `NodeWitness vkLen := {vkC vkL : VKc vkLen, t₁ t₂, x₁ x₂, π₁ π₂}`.**
  The key length is a parameter (the type `VKc` depends on it); `aggOK` takes `NodeWitness P.vkLen`.
- **`nodeStmt cfg vkC vkL x₁ x₂`**, the aggregate statement: `d0 = D vkC`, `d1 = D vkL`,
  `d2 = blake2s256 (stmtBytes x₁ ++ stmtBytes x₂)`, **`d3 … d7 = 0`** (decided: a node statement
  carries no free bits). It is a function, so the harness can recompute the statement tree with it
  (S5-A4).
- **`child cfg P vkC vkL x' tag x π`**: node ⇒ `x.d0 = x'.d0 ∧ x.d1 = x'.d1 ∧ NARG cfg P vkC x π`;
  leaf ⇒ `NARG cfg P vkL x π`. Exactly §5.2.
- **`aggOK cfg P x' nw`** = `x' = nodeStmt cfg nw.vkC nw.vkL nw.x₁ nw.x₂` ∧ both keys' roots are
  32 bytes (**S5-A1**) ∧ both children accepted. `aggOK_iff` unfolds it to the §5.1 table.
- **`rootOK cfg P C L x`** = `x.d0 = digestToSlot (D (index cfg P C)) ∧ x.d1 = digestToSlot
  (D (index cfg P L))`. `index` (trusted, `Compile.lean`) is the honest `VKc` of a layout
  (`(P.VK L, commit cfg ⟨P.idxShape, P.IDX L⟩)`), reused.
- **`RecursionEntry P cfg := {C, fits : C.Admissible k, decode, sound, complete}`**, exactly §5.3.
  The docstring says that `complete` is what bounds the cells of `C_V` (S1-A6), that it excludes a
  `C` with unsatisfiable `rel` once some node is accepted, that both are vacuous if `NARG cfg P`
  accepts nothing (S5-A2), and "see also: no positive entry in the controls; arithmetising `NARG`
  is the submitter's work (§7.3)".

### `Contract/Certificate.lean`

- `Submission k := {P, cfg, secure : P.Secure}`; `SubmissionR k extends Submission k` with
  **`entry`** `: RecursionEntry P cfg` (the requested name `rec` clashes with the auto-generated
  recursor `SubmissionR.rec`).
- `Declared := {k, hash, arity}`; `DeclaredR extends Declared` with `chips`, `entries` (static
  size of `C_V`: chip count and matrix-entry count) and `digestC`, `digestL` (declared, **not
  certified**, S5-A3).
- `Certificate D (S : Submission D.k)`: `S.cfg.hash = D.hash ∧ S.cfg.arity = D.arity`.
  `CertificateR D (S : SubmissionR D.k)` extends it with `S.entry.C.chips.length = D.chips ∧
  (S.entry.C.chips.map Chip.entries).sum = D.entries`. The class is pinned by the type.
- Why the digests are not certified: `D (index cfg P C)` commits the index oracle (up to
  `2^(k+8)` elements); a kernel proof of it by evaluation is infeasible beyond toys. The harness
  computes the digests with the compiled indexer (untimed indexing, §6.3 step 2), compares them
  with the claim and uses them in `rootOK`.

## Library (`Library/Recursion.lean`, 22 theorems)

| Theorem | Statement |
|---|---|
| `aggOK_iff` | `aggOK = true` ↔ `d0 = D vkC`, `d1 = D vkL`, `d2 = H(x₁ ‖ x₂)`, `∀ i ≥ 3, d_i = 0`, 32-byte roots, and for each child: tag node ⇒ `d0`, `d1` equal the parent's and `NARG` under `vkC`; tag leaf ⇒ `NARG` under `vkL` |
| `child_iff`, `aggOK_nodeStmt_iff` | the child condition as a `Prop`; at its aggregate statement a node is accepted iff roots and children are |
| `nodeStmt_slot`, `eq_nodeStmt_iff` | the slots of the aggregate statement |
| `digestToSlot_bytes`, `bytes_digestToSlot` | round trips with `K.bytes` (`= K.toBytes` as `UInt8`s): slot of four elements' bytes = the elements; bytes of a 32-byte digest's slot = the digest |
| `digestToSlot_inj` | on 32-byte digests, a slot determines the digest |
| `K.bytes_ofBytes` | every 8-byte string encodes an element (`K.ofBytes` inverts `K.bytes`) |
| `aggOK_leaves`, `aggOK_nodes` | two accepted leaves (resp. two accepted aggregate statements with the same keys) make an accepted node at the aggregate statement |
| **`aggOK_sat_of_complete`** | honest tapes `prove … = some π_i` that the IOP verifier accepts on their Fiat–Shamir transcripts give, with the indexer's keys for `C` and `L`, an accepted two-leaf node (from `narg_complete`) |
| **`aggOK_sat_of_secure`** | the same for a secure `P` on two instances of `relK k` (from `narg_complete_of_secure`; needs the honest tapes to fit the cap) |
| `rootOK_iff`, `rootOK_nodeStmt` | the root check; a node built with the indexer's keys passes it |
| `keys_of_root` | at a root passing `rootOK` and `aggOK`, the node's keys have the indexer's digests |
| `Stmt.slot_ofSlots`, `Stmt.ofSlots_slot`, `Stmt.ext_slot`, `Stmt.eq_ofSlots_iff` | slots of statements |

## Controls (all kernel-checked)

The protocol is `cmpToy : Protocol 20` at arity 2 (`Controls/CompileToy.lean`; not secure, tiny
shapes, as S1-A12(b) prescribes). `cmpToy` ignores the layout, so its recursion key and leaf key
are the same key `vkc2`; the tags are told apart by the statements. Statements: `x0`, `x1` (S3);
`xN = nodeStmt x0 x1`; `xR = nodeStmt xN x0`; `xD0`, `xD1` = `xN` with one bit of `d0` / `d1`
flipped. Every tape and statement literal is `#guard`ed against the Python reference and against
`prove` (compiled), and every `aggOK` value below is also `#guard`-evaluated directly
(`RecursionData.lean`).

| Control | Kind | What it shows |
|---|---|---|
| `aggOK_two_leaves` | positive (a) | the two-leaf node `⟨vkc2, vkc2, leaf, leaf, x0, x1, tape2, tapeX1⟩` at `xN` |
| `toy_aggOK_sat` | positive | `∃ x' nw, aggOK cfg2 cmpToy x' nw = true` (S1-A12(c)) |
| `aggOK_node_child` | positive | level 2: node child `xN` (its honest tape under `vkC`) and leaf `x0`, at `xR` |
| `toy_sat_via_complete` | positive | `aggOK_sat_of_complete` is not vacuous: `prove cfg2 cmpToy L0 x0 [] = some tape2` and the IOP verifier accepts its FS transcript (`completeRuns`) |
| `child_tape_flip` | negative (b) | bit 0 of byte 40 of `π₂` (a leaf of oracle 1): Merkle path fails |
| `wrong_d1` | negative (b) | one bit of `d1` |
| `nonzero_d3` | negative (b) | element 12 (`d3`'s first limb) = 1 |
| `node_child_d0`, `node_child_d1` | negative (b) | node child whose `d0` (resp. `d1`) differs in one bit; its own tape is accepted (`#guard`), the statement and roots are right, so the key check alone rejects |
| `rootOK_xN` | positive (c) | `xN` passes the root check for `(L0, L0)` (from `rootOK_nodeStmt`, `index_eq`) |
| `rootOK_leaf`, `rootOK_other_key` | negative (c) | a leaf statement is not a root; another protocol key (`cmpToyK`, `VK = 0x1235`) fails |
| `cbad_admissible`, `cbad_rel`, `cbad_good` | (d) | `Cbad` (one public chip of 51 columns, no constraint; `decodeBad` reads `π₂` from cells `32…50`) is admissible at 20 and satisfied by every one-row table; `wGood` decodes to the accepted node |
| `cbad_not_sound`, `cbad_no_entry` | negative (d) | `wBad` (zero cells: `π₂` = 152 zero bytes) satisfies `Cbad` and its node is rejected: `¬ sound`, so no entry has `(Cbad, decodeBad)` |
| `unsat_sound`, `unsat_not_complete`, `unsat_no_entry` | negative (d) | `unsat` (`Controls/Layout.lean`, gadget `1 = 0`, admissible): `sound` holds vacuously for every decoder, `complete` fails for every decoder (`nwN` is accepted), so no entry has `C = unsat` |
| `nodeStmt_kat`, `nodeStmt_kat_R`, `digestToSlot_kat` | KAT (e) | below |
| `toy_certificate`, `toy_certificate_arity` | certificate | the toy (secure) at class 20, BLAKE2s, arity 2 has a leaf-board certificate for `⟨20, blake2s, 2⟩`, none for arity 4 |
| `toy_narg`, `toy_aggOK`, `vacuousEntry`, `vacuous_certificate` | **finding** | S5-A2 below |

### Kernel cost (measured, `logs/S5/kernel-times*.log`)

| Kernel evaluation | Time |
|---|---:|
| one honest `NARG` run of `cmpToy` | 24.1 s |
| `x1Runs`: `NARG` on `x1` honest, flipped, zero tape (they share the sponge seed) | 30.8 s |
| `nodeStmt_kat` (`D vkc2` and the 8-block `d2` hash) | 16.9 s |
| `nodeRuns`: `xR` KAT and the node child's `NARG` | 31.9 s |
| `completeRuns`: `prove = some tape2` and `specVerifier` accepts | 39.3 s |
| `rootRuns` (two root checks, an index commit each) | 10.2 s |

**How the budget was met.** A first version evaluated every `aggOK` by `decide +kernel` in one
theorem of eight conjuncts: 175 s and 19.7 GB. The kernel's cache did not share the `NARG` runs
across conjuncts, because the runs' arguments were different expressions (`nwN.x₁`,
`(decodeBad wBad).x₁`, …). Now each hash-heavy fact is evaluated once, on literal arguments
(`tape2` under `x0` is `Controls/Compile.lean`'s `runs.1`, not re-run), and `aggOK` is derived
through the library lemmas. The two kernel files build in parallel: 58 s (5.6 GB) and 85 s
(7.0 GB). A direct `decide +kernel` of `aggOK_two_leaves` alone costs 63.8 s.

## KATs (e): `digestToSlot` and the aggregate statement against Python

`probes/s5/recursion_ref.py` (run as `python3 -I`; written from DESIGN §5.1 and the
`Compile.lean` grammar; `hashlib.blake2s`, limbs by `struct.unpack('<4Q', digest)`), output in
`logs/S5/python-ref.log`:

```
D(vkc2)             0f4c678bba7ae53087aadea2ae14e944fcd2ba44945b68c601b9a1f6229556d3
digestToSlot D      30e57aba8b674c0f 44e914aea2deaa87 c6685b9444bad2fc d3569522f6a1b901
blake2s(x0||x1)     82c5e67e29931895e57d372e09b4f67e79cc59073e86387af5a211bc0eaca64e
digestToSlot d2     951893297ee6c582 7ef6b4092e377de5 7a38863e0759cc79 4ea6ac0ebc11a2f5
xN = d0 ‖ d1 ‖ d2 ‖ 0^20   (d0 = d1 = digestToSlot D)
xR: d2 = 27a305f90bfeca81 28ff2160edc40601 ef8036dacb1f33f6 917219e2a42b3911
tape x1 / xN / xD0 / xD1: 152 bytes each (index challenges 3, 0, 0, 3)
```

Kernel-checked: `digestToSlot_kat` (`D vkc2`'s bytes, `digest_kat`, to the four limbs above),
`nodeStmt_kat` (`nodeStmt cfg2 vkc2 vkc2 x0 x1` is the 32 words of `xN`), `nodeStmt_kat_R` (`xR`).
`#guard`ed (compiled): the four tapes equal the Python hex, and `prove cfg2 cmpToy L0 x [] = some
tape` for each. The honest tape of `x0` equals S3's `tape2` (Python reproduces it).

## Axioms

`logs/S5/axioms.log` (`#print axioms`, 56 declarations) and `logs/S5/axiomaudit.log` (`lake exe
axiomaudit`: **PASS**, 186 axiom-free theorems overall).

- `digestToSlot`, `nodeStmt`, `decodeBad_good`, `decodeBad_bad`: `[propext, Quot.sound]`.
- `cbad_admissible`: `[propext]`.
- Everything else (`child`, `aggOK`, `rootOK`, `RecursionEntry`, the certificate types, every
  library theorem incl. `aggOK_sat_of_complete`/`_of_secure`, every other control):
  `[propext, Classical.choice, Quot.sound]`. (`aggOK`'s `Classical.choice` comes from the proofs
  inside Mathlib's `Fintype.decidablePiFintype`, the decidable equality of `Stmt`; the code is
  computable, as the `#guard`s show.)

## Deviations from DESIGN (and amendments S5-A1 … S5-A6)

1. **S5-A1: `aggOK` requires 32-byte key roots.** Without it, `complete` asks `C_V` to decode every
   `vkC` with the right digest, including arbitrarily long preimages (`VKc`'s root is a list).
2. **S5-A3: the certificate.** Split by board; static size of `C_V` (chips, matrix entries)
   instead of its cells; key digests declared, not certified; field `entry`, not `rec`.
3. **S5-A4: the statement format.** `nodeStmt` as a trusted function; `d3 … d7 = 0`; `d2` uses
   `blake2s256` for every `cfg` (as §5.1); tags are not hashed (argued).
4. **S5-A5: the root check** checks `d0`, `d1` only; the statement tree is the harness's
   (`nodeStmt`); `keys_of_root` shows the check pins the keys.
5. **S5-A6: controls.** On `cmpToy`, as S1-A12(b) prescribes. No positive `RecursionEntry` (§7.3).
   The positive controls are derived through the library lemmas from kernel-evaluated `NARG` runs
   and KATs, not by one `decide` of `aggOK` (cost, above); the compiled `#guard`s evaluate `aggOK`
   directly.

## Finding (S5-A2): a vacuous recursion-board submission

`Controls/Certificate.lean`. The toy protocol is secure (`toy_secure`) but its one message is plain,
`8·2^30` bytes at class 20, beyond `tapeCap = 2^20`: `NARG cfg2 (toy 20)` accepts no tape
(`toy_narg`), so `aggOK` accepts no node (`toy_aggOK`), `complete` is vacuous, and with `C = unsat`
so is `sound`. `vacuousR : SubmissionR 20` and `vacuous_certificate : CertificateR ⟨⟨20, blake2s,
2⟩, 1, 0, [], []⟩ vacuousR` are kernel-checked. This is the residual case of S1-A12(c) (compile
completeness needs the honest tapes to fit the cap, S3-A13): a certified recursion entry need not
be able to prove any node, and "`C_V` fits class `k`" is vacuous for it. The benchmark run rejects
it (§6.3). Option (S5-A2): a field `live : ∃ x' nw, aggOK cfg P x' nw = true`, which a real
submitter proves with `aggOK_sat_of_secure` and a tape-size bound for its own proof format.

## Open questions for the orchestrator

1. **S5-A2:** add `live` to `RecursionEntry` (closes the vacuous certificate in Lean), or keep the
   benchmark as the only backstop (current design)?
2. **S5-A4:** should `d2` follow `cfg.hash` once the hash menu grows (one hash gadget per `C_V`)?
3. **Stage 6b:** the gate's `--computable` table needs `Submission: [P]` and
   `RecursionEntry: [decode]`; the renderer pins `DeclaredR` (`digestC`/`digestL` are compared by
   the harness, not proved); the R stub's theorem is `CertificateR declared submission`.
4. **`aggOK_sat_of_secure` has no instance in the repository** (the only `Protocol` proved secure,
   the toy, has tapes beyond the cap). A secure protocol with small tapes is a real SNARK, i.e. the
   first board-R entry; until then non-vacuity rests on `aggOK_sat_of_complete` with `cmpToy`.

## Decision pass (orchestrator, 2026-10-15)

Applied the three decisions; appended S5-A7, S5-A8, S5-A9 to `docs/DESIGN-AMENDMENTS.md`.

1. **S5-A7 (S5-A2 → yes): `RecursionEntry.live : ∃ x' nw, aggOK cfg P x' nw = true`**, with the
   requested docstring ("the compiled argument accepts at least one node; without it `complete` is
   vacuous for a protocol whose proofs exceed the tape cap; a submitter proves it with
   `aggOK_sat_of_secure` plus a bound on its own proof size"). The `RecursionEntry` docstring now
   says `live` keeps `sound`/`complete` from being vacuous.
   - **Negative control** (`Controls/Certificate.lean`): `vacuousEntry`, `vacuousR` and
     `vacuous_certificate` are gone. `toy_vacuous_fields`: with `unsat`, `fits`, `sound` and
     `complete` hold for the toy, for any decoder. `toy_no_entry : RecursionEntry (toy 20 _) cfg2 →
     False`: `live` fails (`toy_aggOK`). `toy_no_submissionR`: no `SubmissionR` has the toy and
     `cfg2`.
   - **Positive side.** There is no positive `RecursionEntry` (§7.3). `live` itself holds for
     `cmpToy` (`toy_aggOK_sat`, now documented as such), and `aggOK_sat_of_secure` is the general
     route; it has no instance in the repository (the toy's tapes exceed the cap).
   - `cbad_no_entry` and `unsat_no_entry` are unchanged (they use `sound` and `complete`).
2. **S5-A8: `d2 = digestToSlot (cfg.hash.run (stmtBytes x₁ ++ stmtBytes x₂))`**, the hash of `D`
   and of the sponge (one hash gadget per `C_V`). Changed in `nodeStmt` and in the library's
   `nodeStmt_slot`, `eq_nodeStmt_iff`, `aggOK_iff`. Nothing changes numerically (`cfg2.hash.run =
   blake2s256`): `nodeStmt_kat` and `nodeStmt_kat_R` pass unchanged against the same literals, and
   `probes/s5/recursion_ref.py` (docstring updated) prints byte-identical output (`diff` empty).
3. **S5-A9 (Stage 6b):** the gate's `--computable` table must include `Submission.P` and
   `RecursionEntry.decode`; `digestC`/`digestL` are harness-compared, not proved.

**Re-run** (`logs/S5/build-decision.log`, `build-rest-decision.log`, `axiomaudit-decision.log`,
`hygiene-decision.log`, `axioms.log`, `loc-decision.log`): `lake build` green (kernel files 59 s
and 82 s, in parallel); `lake build RecursionFastBridge gate axiomaudit` green; axiom audit
**PASS**; hygiene OK; `#print axioms` on 57 declarations within the standard three.
`Contract/Recursion.lean` is now **45** code lines (130 total), `Contract/Certificate.lean` 23;
the contract without `Compile.lean` and `Hash/` is **519** lines. `Controls/Certificate.lean`: 37
code lines, 9 theorems.

The open questions 1–3 above are answered by S5-A7, S5-A8 and S5-A9; question 4 stands.

## Fix pass (after `docs/reviews/S5-review.md` and `S5-golf.md`, 2026-10-15)

Every file was re-read after the golf (proofs only, −28 lines) before editing. The S5 review's
probes in `probes/s5/review/` are kept as they were; they no longer compile against the new
signatures (`nodeStmt` with tags, `live`, `rootOK`), and their content is adopted below.
Amendments S5-A10 … S5-A13 are appended to `docs/DESIGN-AMENDMENTS.md`.

### Findings

| Finding | Decision | Done |
|---|---|---|
| **S5-M1** (major): `live` met under a key no layout has | fixed | **S5-A10**: `live : ∃ L x' nw, nw.vkC = index cfg P C ∧ nw.vkL = index cfg P L ∧ aggOK cfg P x' nw = true`, with the review's residual in the docstring. `magic_not_live`, `magic_no_entry` (negative): `Controls/MagicKey.lean`, the review's `toyCM` (secure, meets the S5-A7 form via `magic_old_live`, accepts no node with indexer keys). Positive: `cmpToy_live`. `live_of_secure` (library) gives the field from one instance of `relK k` whose honest proof fits the cap. |
| S5-m1: tags not bound | fixed | **S5-A11**: `d3 = tagSlot t₁ t₂ = (tagK t₁, tagK t₂, 0, 0)`, `tagK leaf = 0`, `tagK node = 1`, `d4 … d7 = 0`. `mistag_rejected` (the review's `mistag`, now rejected); `nonzero_d3` moved to limb 2 of `d3`, `nonzero_d4` added; `tagSlot_inj`. |
| S5-m2: `complete` ranges over every key | wording (a) | `RecursionEntry` docstring: "`complete` ranges over every accepted node, whatever its keys: `verify` must bound its own work and its tape on every key (e.g. reject keys outside the format of `VK`)". |
| S5-m3: no Lean spec of the statement tree | fixed | **S5-A12**: trusted `pairUp`, `treeRoot` (level 1 over leaves tagged `leaf`, above over nodes tagged `node`; `none` unless `2^d` leaves); `rootOK cfg P C L d xs x` = `treeRoot … = some x`, pinning `d0 … d3`. Kept in `Recursion.lean` (67 code lines ≤ 90). Library: `rootOK_iff`, `treeRoot_one/_two/_node`, `keys_of_root` (depth `≥ 1`). Controls: `rootOK_xT`, `rootOK_leaf`, `rootOK_other_key`, `rootOK_odd`; KAT `treeKat`. |
| S5-m4: a node child's own slots | wording | module header and `child`'s docstring: a node child's statement is pinned by its parent's `d2` and by its own proof, not by `aggOK`. |
| S5-m5: declared digests | harness note | **S5-A13** (compute from the submitted `C` and from `L_chain(2^10)`, reject on mismatch, use own values); `digestC`/`digestL` and the module docstrings updated. |
| S5-m6: `decode` may read unpaid cells | wording (a) | `complete`'s docstring: "every accepted node is decoded from a satisfying witness, so every accepted statement has a witness of at most `2^k` cells (`decode` may also read cells outside `rows × cols`)". |
| S5-m7: controls cannot tell `vkC` from `vkL`, nor 32-byte roots | fixed | `distinct_keys` (positive: leaf key `vkK`, the indexer key of `cmpToyK` = element `0x1235` with its honest prover, recursion key `vkc2`) and `leaf_under_vkC` (negative: leaf proofs valid only under `vkc2`); `keyRuns` also shows `tapeK` is rejected under `vkc2`, so the swap mutant flips both. `root33_rejected`: a 33-byte root is rejected with everything else right. |
| S5-m8: `aggOK_sat_of_secure` has no instance | stated | `hit` (`Controls/Hit.lean`) is stated over `Security.lean`'s strategies and is not a `Protocol`, and the only `Protocol` proved secure, the toy, has tapes beyond the cap (as has the review's `toyCM`), so `aggOK_sat_of_secure` and `live_of_secure` have no instance in the repository; no new protocol was added. |
| S5-m9: DESIGN stale | orchestrator | none |
| Golf note: `K.bytes_ofBytes` 7.4 s | left | a quick attempt (simp with a discharger instead of `interval_cases`) was not faster to write correctly; unchanged. |

### Numbers

- **Python** (`probes/s5/recursion_ref.py`, `logs/S5/python-ref.log`; the pre-fix output is kept
  as `logs/S5/python-ref-prefix.log`): `xN` unchanged (tags `leaf, leaf`); `xR` now has
  `d3 = (1, 0, 0, 0)` (`d2` unchanged: `27a305f90bfeca81 …`); the depth-2 tree root `xT` has
  `d2 = 5ce274c0fa10b1fc 8403b5aa0b092ade a6c6453e15ff1c13 8afda1dd0197ce41` and `d3 = (1, 1, 0, 0)`;
  `D(vkK) = e1b14323…4111f189`; `tapeK` (152 bytes, index challenge 1) equals
  `prove cfg2 cmpToyK L0 x0 []` (`#guard`). Kernel KATs: `nodeStmt_kat`, `nodeStmt_kat_R`,
  `treeKat`, `digestToSlot_kat`.
- **Build** (`logs/S5/build-fix.log`): `lake build` green, 123 s wall; kernel files in parallel:
  `Controls/Recursion.lean` 71 s, `Controls/RecursionNode.lean` 115 s (adds `keyRuns`, about
  30 s), `Controls/MagicKey.lean` 20 s. `lake build RecursionFastBridge gate axiomaudit` green.
- **Checks:** axiom audit **PASS** (`logs/S5/axiomaudit-fix.log`); hygiene OK; `#print axioms` on
  48 declarations (`aggOK`, `rootOK`, `treeRoot`, `RecursionEntry`, every new or changed control,
  `magic_not_live`): within `propext`, `Classical.choice`, `Quot.sound`
  (`logs/S5/axioms-fix.log`).
- **Lines** (`logs/S5/loc-fix.log`): `Contract/Recursion.lean` **67** code lines (≤ 90),
  `Contract/Certificate.lean` 23; the contract without `Compile.lean` and `Hash/` is **541**
  (budget 850). Library 187 (27 theorems); controls: `RecursionData` 186, `Recursion` 72 (26),
  `RecursionNode` 44 (10), `Certificate` 32 (9), `MagicKey` 161 (15).

### Open questions

1. The S5-A10 residual (a protocol special-casing the key of a trivially satisfiable layout) is
   closed only by the benchmark; a `live` at `L_chain` needs a whole-chain completeness theorem.
2. The review's probes in `probes/s5/review/` are stale against the new signatures; delete them
   or keep them as the record of the findings (the orchestrator's choice).

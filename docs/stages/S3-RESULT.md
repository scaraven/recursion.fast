# S3 RESULT: the compiled argument (BCS + Fiat–Shamir), `Contract/Compile.lean`

Stage 3 is DESIGN §11 step 4. One agent implemented it on 2026-10-14. Nothing is committed.

**Edits to existing files.** One import was appended to each root file:
- `RecursionFast/Contract.lean`: `Contract.Compile`;
- `RecursionFast/Library.lean`: `Library.Compile`;
- `RecursionFast/Controls.lean`: `Controls.CompileToy`, `Controls.Compile`, `Controls.CompileFS`.

**Docs.** Seven amendments, S3-A1 to S3-A7, are appended to `docs/DESIGN-AMENDMENTS.md`.

## Headline

- **Trusted code: 159 lines** in `Contract/Compile.lean`, against a budget of 350 and a hard cap
  of 400. It imports only `Contract.Protocol` and `Contract.Hash.Blake2s`. Every declaration has
  a docstring, and the module header gives the byte orders and the tape grammar.
- **Completeness of the compilation is proved in general**, with no `sorry`, in
  `Library/Compile.lean`. It holds for every protocol, every `Cfg` (BLAKE2s, arity 2, 4, 8 or 16)
  and every instance. Two forms:
  - `narg_complete`: `prove cfg P L x w = some t` and the IOP verifier accepts the Fiat–Shamir
    transcript ⟹ `NARG cfg P (index cfg P L) x t = true`.
  - `narg_complete_of_secure`: if `P.Secure` and `((L, x), w) ∈ relK k`, every tape that `prove`
    outputs is accepted. `prove_isSome` adds that `prove` then fails only by exceeding the tape
    cap.
- **Locality.** `narg_local` says what an accepted tape gives you:
  - it fixes the Fiat–Shamir challenges;
  - on those challenges, the query program accepts every oracle list consistent with the roots,
    the plain oracles and the tape's authenticated openings.

  This is the deterministic core of BCS soundness.
- **Kernel controls: one positive and nine negatives, all decided by `decide +kernel`.** They run
  on `cmpToy : Protocol 20` at arity 2. A tenth negative, `oversize`, follows from the general
  lemma `narg_oversize`.
  - **Cost.** An honest run costs about 15 BLAKE2s compressions, which is **≈ 35 s and 5.3 GB**
    in the kernel on its own.
  - The control files take **70 s and 56 s**. They build in parallel, and the default build
    finishes in ≈ 76 s wall time.
- **Cross-checks against an independent Python reference.** `probes/s3/compile_ref.py` is written
  from the documented grammar only and uses `hashlib.blake2s`. It reproduces byte for byte:
  - the honest tapes at arity 2 (152 bytes) and arity 4 (248 bytes);
  - both index roots;
  - both 4-leaf Merkle roots;
  - the cheating tape.
- **Axioms.** Only the standard three. `lake exe axiomaudit` reports **PASS**, including all five
  new modules, and `scripts/check-hygiene.sh` reports OK.
- **Builds.** `lake build RecursionFastBridge gate axiomaudit` is green. The full `lake build`
  fails only in `RecursionFast.Controls.Extractor`, which belongs to a concurrent stage
  (in-progress, untracked, not mine). Every Stage 3 module builds (`logs/S3/build-full.log`).
- **Decisions to confirm:**
  - **S3-A1:** a one-leaf prover oracle is sent in the clear. These are the "plain words" of the
    task.
  - **S3-A2:** Merkle leaves carry **no** domain-separation tag. This deviates from the
    instruction.
  - **S3-A3:** the sponge starts from `D(VKc)`, not from the raw `VK` bytes.

## Files

Code lines are from `scripts/loc.py` (`logs/S3/loc-s3.log`).

| File | Status | Code | Total | What it is |
|---|---|---:|---:|---|
| `Contract/Compile.lean` | **TRUSTED by review, new** | 159 | 334 | `HashId`, `Cfg`, byte encodings, Merkle (`node`, `commit`, `climb`, `verifyPath`), `index`, sponge (`absorb`, `squeeze`, `seed`), challenge decoding, tape readers, `pass`, `View`, `runQ`, **`NARG`**, honest prover (`fsPrefixes`, `fsTranscript`, `pathOf`, `record`, **`prove`**) |
| `Library/Compile.lean` | untrusted, new | 511 | 658 | 47 theorems: byte round trips, Merkle correctness, replay, FS transcript, pass, `narg_complete*`, `prove_isSome`, `narg_local`, `narg_oversize` |
| `Controls/CompileToy.lean` | controls, new | 91 | 174 | `cmpToy`, tapes, `cheat`, five `#guard`s (prover output, Python agreement, arity 4), two `#eval`s, `index_eq` |
| `Controls/Compile.lean` | controls, new | 27 | 48 | `runs` (honest plus six tamperings, one kernel evaluation), its named projections, `oversize` |
| `Controls/CompileFS.lean` | controls, new | 12 | 29 | `fsRuns` (three Fiat–Shamir tamperings), its named projections |
| `probes/s3/compile_ref.py` | probe | 80 | 90 | independent Python reference of the grammar (`python3 -I`) |
| `probes/s3/OneRun.lean`, `TwoRuns.lean` | probes | — | — | kernel cost of one run, and of two runs sharing the cache |

The trusted budget (`logs/S3/loc.log`): §8's 850-line budget excludes `Compile.lean` and `Hash/`.
The contract files of Stages 1–2 are unchanged. `Contract/Extractor.lean` and `Machine.lean`
belong to the concurrent stage.

## Build and elaboration times

Times are wall-clock, from `/usr/bin/time -v lake env lean <file>` with the imports built
(`logs/S3/time-*.log`). Another agent was building in the same tree, so expect ±10 %. User CPU
times (Compile 65 s, CompileFS 53 s) are in the same logs.

| Module | Time | Peak memory | Note |
|---|---:|---:|---|
| `Contract.Compile` | 5.5 s | 1.9 GB | |
| `Library.Compile` | 11.3 s | 2.7 GB | `wordOfBytes_bytes` (64 bit cases, `interval_cases`) ≈ 5 s |
| `Controls.CompileToy` | 9.8 s | 2.4 GB | `index_eq` 4.5 s kernel (3 hashes); `#guard`s are compiled-code evaluation |
| `Controls.Compile` | 70 s | 8.2 GB | `runs`: 57 s kernel |
| `Controls.CompileFS` | 56 s | 7.4 GB | `fsRuns`: 50 s kernel |
| one honest run alone | 35–39 s CPU | 4.7–5.3 GB | `probes/s3/OneRun.lean`, for reference |

In the default `lake build` (`logs/S3/build-full.log`), `Controls.Compile` (68 s) and
`Controls.CompileFS` (53 s) build in parallel. The whole build takes 76 s wall time, of which the
Stage 3 files are about 70 s.

**Kernel cost model.**
- One BLAKE2s compression costs about **2.2 s** in the kernel.
- An honest run of `cmpToy` costs 15 compressions:
  - 1 for the key digest;
  - 5 to absorb `x`, which is 289 bytes;
  - 2 for the root absorb;
  - 1 for the squeeze;
  - 1 for the plain absorb;
  - 3 + 2 for the openings.
- Putting all the runs in one theorem lets the kernel's cache compute the shared hashes once.
  - `probes/s3/OneRun.lean`, one honest run: **39 s** user CPU, 4.7 GB
    (`logs/S3/probe-one-run.log`).
  - `probes/s3/TwoRuns.lean`, the honest run and `leftover` in one theorem: **43 s**, 4.9 GB
    (`logs/S3/probe-two-runs.log`).
  - The wall times in those two logs (75 s and 96 s) are inflated by olean page-ins after the
    page cache was evicted: 11–15 k major faults.
  - An earlier, now superseded design ran ten runs in one theorem in 111 s.
- The verifier checks the plain answer first, so the Fiat–Shamir negatives reject before any
  Merkle hashing.

## Design (as implemented; the module header is the reference)

### Bytes

| Object | Encoding |
|---|---|
| element of `K` | 8 bytes, little-endian (`K.toBytes`, Rust `u64::to_le_bytes`); `K.bytes`, `K.ofBytes` (`wordOfBytes`, Rust `u64::from_le_bytes`) |
| element of `E` | 24 bytes: limbs `c0, c1, c2`, each 8 bytes little-endian (`E.ofBytes`) |
| vector, leaf, statement | its elements in order (`x`: 32 elements, 256 bytes) |
| digest | the 32 bytes the hash outputs |
| compiled key `VKc` | the `VK L` elements, then the 32-byte index root (`VKc.toBytes`) |

There is no length field anywhere, because every length is fixed by the protocol's shape.

### Merkle tree (S3-A2)

- **Shape.** Oracle `o` has `2^(logLen − logLeaf)` leaves (`Oracle.leaf`). They are padded with
  the zero digest (32 zero bytes) to `A^depth` positions, where `depth` is the least `d` with
  `2^(logLen − logLeaf) ≤ A^d`.
- **Hashes.** A leaf's digest is `H(leaf bytes)`. Node `p` at height `h + 1` is
  `H(node_h(A·p) ‖ … ‖ node_h(A·p + A − 1))`. The root is `node_depth(0)`.
- **Path.** At each level, from the leaf up, the path holds the `A − 1` siblings in increasing
  position. `climb` inserts the current digest at `p mod A`.
- **Index oracle.** It is always committed, by `index`.

### Sponge and Fiat–Shamir (S3-A3)

```
s ← H(VKc bytes)                       -- = D of DESIGN §5.1
s ← H(0x00 ‖ s ‖ x bytes)
for each round, in order:
  msg o:       b ← the round's tape bytes (8·2^logLen plain bytes, or the 32-byte root)
               s ← H(0x00 ‖ s ‖ b)
  chal nE idx: ⌈(24nE + 8|idx|)/32⌉ times: s ← H(0x01 ‖ s), output s
               keep the first 24nE + 8|idx| bytes:
                 E element j  = bytes 24j … 24j+23  (c0, c1, c2)
                 index j      = (LE word at 24nE + 8j) mod 2^b   (low b bits; exact, no rejection)
```

### Tape grammar

```
tape     ::= rounds openings                     |tape| ≤ 2^20, no bytes left over
rounds   ::= for each prover round in order: its plain elements (one-leaf oracle) | its root
openings ::= for each query (j, l) the run of P.verify vk x chal makes, in order:
               nothing           if oracle j ≥ 1 is plain (the leaf is its elements)
               leaf path         otherwise
leaf     ::= the 2^logLeaf elements of leaf l of oracle j
path     ::= depth levels, leaf level first; each level the A − 1 sibling digests, in increasing
             position (the current node omitted)
```

Oracle 0 is the index oracle, with root `vkc.2`. Oracle `j ≥ 1` is the `j`-th prover oracle in
round order (`FullTranscript.oracles`), exactly as in `Protocol.specVerifier`. A query outside
the range, a short or malformed opening, a failed path, an oversize tape and leftover bytes all
reject. A repeated query is opened again (S3-A4).

### `NARG` and `prove`

`NARG cfg P vkc x t` works in three steps:
1. Check `|t| ≤ tapeCap`.
2. `pass` runs the sponge over `List.ofFn P.shape`, reading the rounds section, and records every
   round's bytes in an `Array`.
3. Run `P.verify vkc.1 x (chals P.shape es)` with `runQ` against the views (`views`: root or plain
   elements per oracle) and the remaining tape. Accept iff the result is `some true` and no bytes
   are left over.

Every function is total and structural (`kList.go`, `squeeze.go` and `takeN` are tail-recursive
and safe on 1 MiB tapes). Array indexing is O(1) per query. `prove` is computable whenever
`P.prover` is: `#eval` and `#guard` run it on `cmpToy`.

## What is proved (`Library/Compile.lean`, all general)

| Theorem | Statement (informal) |
|---|---|
| `narg_complete` | `prove cfg P L x w = some t` and `P.specVerifier (L, x) (fsTranscript …) = some ()` ⟹ `NARG cfg P (index cfg P L) x t = true` |
| `narg_complete_of_perfect` / `_of_secure` | `PerfectComplete` (or `P.Secure`), `((L, x), w) ∈ relK k`, `prove … = some t` ⟹ `NARG … t = true` |
| `prove_isSome` | under `PerfectComplete` and the relation, `record` succeeds and `prove` is `some` of the honest tape iff that tape fits the cap |
| `fsTranscript_eq` | the Fiat–Shamir transcript is `P.prover.transcript (L, x) w (chalOf fsTranscript)`, so `PerfectComplete` applies to it |
| `pass_honest`, `chals_honest`, `views_honest` | on the honest rounds section, the verifier's pass re-derives the honest challenges and views |
| `runQ_record` | on the honest openings, `runQ` equals `QProg.eval` on the honest oracles (query replay) |
| `climb_pathOf`, `verifyPath_pathOf`, `readOpening_honest` | Merkle path correctness for honest trees at every arity, and the opening parses back |
| `K.ofBytes_bytes`, `kList_flatMap`, `takeN_append'`, `readMany_flatten` | byte round trips |
| `narg_local` (`runQ_local`) | `NARG … t = true` ⟹ the cap holds, `pass` succeeds with some `es`, and on `chals P.shape es` the query program accepts every oracle list `Consistent` with the views and the `opened` leaves |
| `narg_oversize` | `tapeCap < |t|` ⟹ `NARG … t = false` |

**Is `narg_complete` general?** Yes. It holds for any `Protocol k`, any `Cfg` (all four arities),
any `L`, `x`, `w` and any tape. Nothing is specialised to arity 2.

**Remaining gap.** `narg_local` is the deterministic part of soundness. The binding of openings
to roots (collision resistance) and the random-oracle step are not Lean statements, as DESIGN §5.4
says.

## Controls

The control protocol `cmpToy : Protocol 20` is not secure (S1-A12(b)).
- **Index oracle.** 2 leaves of 1 element.
- **Round 0.** A 4-leaf committed oracle `p ↦ p + 7`.
- **Round 1.** One `E` element `e` and one 2-bit index `i`.
- **Round 2.** One plain element `m = e.c0 + vk 0 + x 0`.
- **Verifier.** It reads `m` first and rejects on a mismatch. It then reads leaf `i` of oracle 1
  and leaf `i mod 2` of the index, and accepts iff they are `i + 7` and `i mod 2 + 100`.

**Honest tape at arity 2** (152 bytes):

| Bytes | Content |
|---|---|
| 0–31 | root of oracle 1 |
| 32–39 | the plain element |
| 40–47 | leaf `i = 2` of oracle 1 |
| 48–111 | its path |
| 112–119 | the index leaf |
| 120–151 | its path |

| Control | Kind | Check | What it shows |
|---|---|---|---|
| `honest_accepted` | positive | kernel (`runs`) + `index_eq` | the honest tape is accepted under the indexer's key |
| `#guard prove cfg2 … = some tape2` | positive | compiled evaluation | the honest prover outputs exactly that tape (152 bytes) |
| `#guard` arity 4 | positive | compiled evaluation | at arity 4 the honest tape (248 bytes: 3 siblings per level, the index tree padded with two zero digests) is accepted and equals Python's |
| `leaf_flip` | negative | kernel | bit 0 of byte 40 (the leaf of oracle 1) changed: the path does not climb to the root |
| `path_flip` | negative | kernel | bit 0 of byte 48 (a path digest) changed: rejected |
| `plain_flip` | negative | kernel | bit 0 of byte 32 (the plain word) changed: rejected |
| `idx_leaf_flip` | negative | kernel | bit 0 of byte 112 (the index leaf) changed: rejected against the key's root |
| `leftover` | negative | kernel | one extra byte: rejected |
| `truncated` | negative | kernel | one byte short: rejected |
| `oversize` | negative | `narg_oversize` | `tape2 ++ replicate 2^20 0`: rejected by the cap |
| `root_flip` | negative | kernel (`fsRuns`) | bit 0 of the root of oracle 1 changed: the challenges change and the answer fails |
| `stmt_flip` | negative | kernel | bit 0 of `x 31`, which the verifier never reads, changed: rejected. Only Fiat–Shamir binds it. |
| `fs_binding` | negative | kernel | a prover that commits to `p ↦ p + 1000`, with valid openings under its own root, but answers the honest root's challenges: rejected |

**Recorded evaluations** (`logs/S3/time-Controls-CompileToy.log`). The honest tape's length is
152 (`#eval tape2.length`). The 4-leaf Merkle roots of `p ↦ p + 7` are:

```
Lean  #eval (arity 2, arity 4):
("6004bdd30cf006e92ec966da6a257f20f6f42ba1caddb6ecfb162e2f698a6aef",
 "f9620879795033a7756ce7c76b8b71ba3a318bae44a0d912b7d5c90befcc5d9b")
Python (probes/s3/compile_ref.py, hashlib.blake2s; logs/S3/python-ref.log):
arity 2: msg root   6004bdd30cf006e92ec966da6a257f20f6f42ba1caddb6ecfb162e2f698a6aef
arity 4: msg root   f9620879795033a7756ce7c76b8b71ba3a318bae44a0d912b7d5c90befcc5d9b
arity 2: index root 09b90c7db05d859d133d2712992ba0617501cc91470afce1ed8c99a99553d6f8   (= vkc2.2)
arity 4: index root adb4d583edbb11bc140ccc0e74f1ef2a3d67400658d2ab02fe571572922e6e79
arity 2: tape (152 bytes) 6004bdd3…6e35b8595b   (= tape2, = Lean prove)
arity 4: tape (248 bytes) f9620879…00000000     (= Lean prove, #guard)
cheat:                    ceac3a7c…6e35b8595b   (= Lean cheat, #guard)
```

The Python reference builds leaves as `H(le64(a))` and nodes as `H(c0‖c1)` (or `H(c0‖c1‖c2‖c3)`),
with no tags and zero-digest padding. A native prover reproduces exactly these.

## `#print axioms` (`logs/S3/print-axioms.log`)

Each of the following uses `[propext, Classical.choice, Quot.sound]`:
- the theorems `narg_complete`, `narg_complete_of_secure`, `narg_local`, `prove_isSome`, `runs`,
  `fsRuns`, `honest_accepted`, `oversize` and `index_eq`;
- the definitions `NARG` and `prove`. `NARG` inherits these through `Protocol`'s types (`ℝ≥0`).

`lake exe axiomaudit` (`logs/S3/axiomaudit.log`) reports PASS on every module:

| Module | Declarations |
|---|---:|
| `Contract.Compile` | 115 |
| `Library.Compile` | 123 |
| `Controls.CompileToy` | 27 |
| `Controls.Compile` | 9 |
| `Controls.CompileFS` | 4 |

`scripts/check-hygiene.sh` reports OK. There is no `sorry`, `native_decide`, `implemented_by`,
`extern`, `csimp`, `partial` or `unsafe`, and no `bv_decide`, whose proofs use
`Lean.ofReduceBool`.

## Deviations (recorded in `docs/DESIGN-AMENDMENTS.md`)

- **S3-A1. Plain oracles.** A one-leaf prover oracle is sent in the clear and absorbed, and a
  query reads it from the rounds section.
  - This is how the task's "plain words" and "flipped plain word" are realised. In the contract's
    shapes a prover round carries only an oracle, and `Round.tapeWords` gives the challenge words
    of the v0.3 tape, which the compiled argument derives instead of sending.
- **S3-A2. Merkle hashing without a leaf tag.** This deviates from the instruction.
  - **Why it is safe.** The depth is fixed, and sponge inputs (length `1 mod 8`) are separated
    from tree inputs (`0 mod 8`) by length.
  - **What a tag would cost.** One extra compression for every leaf of ≥ 8 elements.
- **S3-A3. Sponge seed.** It is `D(VKc) ‖ x` rather than `VK ‖ x`. This lets `C_V` reuse its `D`
  computation. Squeezing is a ratchet with no counter.
- **S3-A4. `Cfg` and proof format.** `Cfg` is `hash` (only `blake2s`) and `arity`. Leaf packing is
  `logLeaf`. There is no query batching (no multi-proof format yet).
- **S3-A5. Key and tape.** `VKc` holds the VK and the index root, and `D` should hash
  `VKc.toBytes` (this updates S2-A1).
  - `NARG` checks the 1 MiB cap and rejects leftover bytes.
  - v0.3's blow-up cap is dropped, because v2 measures prover time.
- **S3-A6. Completeness is a theorem.** This closes S1-A12(c) for the compilation layer.
- **S3-A7. Controls.** `cmpToy` instead of the toy. The design's "flipped challenge" is read as
  "flipped root or statement".

## Open questions for the orchestrator

1. **S3-A2 (leaf tag).** Confirm "no tag", or ask for `H(0x02 ‖ leaf)`. A tag is a two-line change
   to `leafHash` plus the Python reference. It costs one compression per leaf of ≥ 8 elements, in
   the timed verifier and in `C_V`.
2. **S3-A3 (seed).** `D` must be the same function in Stage 5. I wrote the seed as
   `cfg.hash.run (VKc.toBytes vkc)`, which equals `blake2s256 (VKc.toBytes vkc)` for the only menu
   hash.
   - Stage 5 could define `D cfg vkc := cfg.hash.run vkc.toBytes` in `Compile.lean`, or define
     `D` with BLAKE2s fixed in `Recursion.lean`.
   - If `D` always uses BLAKE2s while the sponge uses `cfg.hash`, the seed should call `D`
     explicitly.
3. **Kernel cost of Stage 5's controls.** A two-leaf node with `cmpToy` evaluates `NARG` twice
   plus the `D` hashes, so it will take about 2 × 35 s and 5–8 GB in the kernel. Sharing works
   only inside one declaration: put the runs in one conjunction.
4. **Query batching (S3-A4).** A pruned multi-opening, where shared path nodes are sent once, is
   the main proof-size and verifier-time lever for FRI-like protocols. It changes the grammar, so
   decide it before agents write native provers.
5. **Executed speed.** `NARG` was not benchmarked compiled (`lake exe verify` is Stage 7). Two
   per-query costs could be removed by precomputing them in `views`:
   - `Cfg.depth`, a `find?` over ≤ 39 candidates, is recomputed on every query;
   - `chals` decodes a round's bytes on every access.
6. **Concurrent stage.** `Controls/Extractor.lean` (another agent's, untracked) currently breaks
   the full `lake build`. Every Stage 3 target builds.

## Fix pass

Applies `docs/reviews/S3-review.md` (ACCEPT WITH FIXES) as the orchestrator decided, and the
golf notes of `docs/reviews/S3-golf.md`. The golfed `Library/Compile.lean` was the starting point.
The new amendments are S3-A8 to S3-A14 in `docs/DESIGN-AMENDMENTS.md`. Logs are
`logs/S3/fix-*.log`.

### Results

- **Trusted base: 128 code lines**, down from 159 (`logs/S3/fix-loc.log`). The file has 307 total
  lines and 0 theorems, and still imports only `Contract.Protocol` and `Contract.Hash.Blake2s`.
- **Builds.** The five Stage 3 targets build. So do the root modules (Stage 4's `Machine` and
  `Extractor` now included), `RecursionFastBridge`, `gate` and `axiomaudit`.
- **Checks.** `lake exe axiomaudit` reports **PASS** (`logs/S3/fix-axiomaudit.log`):

  | Module | Declarations |
  |---|---:|
  | `Contract.Compile` | 109 |
  | `Library.Compile` | 137 |
  | `Controls.CompileToy` | 28 |
  | `Controls.Compile` | 26 |
  | `Controls.CompileFS` | 17 |

  `scripts/check-hygiene.sh` reports OK.
- **Root imports present:**
  - `Contract.lean:12` imports `Contract.Compile`;
  - `Library.lean:9` imports `Library.Compile`;
  - `Controls.lean:8–10` import `Controls.CompileToy`, `Controls.Compile` and `Controls.CompileFS`.
- **Axioms.** `#print axioms` (`logs/S3/fix-print-axioms.log`) gives
  `[propext, Classical.choice, Quot.sound]` for:
  - `NARG`, `narg_complete`, `narg_complete_of_secure`, `NARG_eq_true_iff`, `narg_local`,
    `depth_spec` and `prove`;
  - `runs`, `fsRuns`, `index_eq`, `idx_path_flip`, `oob_rejected`, `toy_local`, `pfs_honest`,
    `pfs_cheat` and `oversize`.

  `VKc.digest`, `digest_kat` and `decode_kat` use only `[propext, Quot.sound]`.
- **Independent encoder.** `probes/s3/indep_encoder.py`, written by the reviewer from the header
  alone, still matches Lean byte for byte (`logs/S3/fix-indep-encoder-compare.log`):
  - tapes and index roots at arity 2, 4, 8 and 16 all agree;
  - the padded root equals the header's reading, under which all-padding internal nodes are
    hashed.

  Lean's `RevEncoder` output and the Python output are unchanged from the review (the only diff
  is timing lines).

### Times

Times are wall-clock (user CPU, peak RSS), from `/usr/bin/time -v lake env lean`
(`logs/S3/fix-time-*.log`).

| File | Before the fix | After |
|---|---|---|
| `Controls/CompileToy.lean` | 9.8 s | 12.3 s (10.1 s, 3.0 GB). Adds `digest_kat`; it now imports the library for `prove`. |
| `Controls/Compile.lean` | 70 s (62 s after the golf) | 70.2 s (66.7 s, 9.1 GB). It now also kernel-checks `idx_path_flip`, `oob_rejected`, the honest pass and the opened leaves (for `toy_local`). The byte literals saved the ≈ 11 s of `hex` decoding, which pays for these. |
| `Controls/CompileFS.lean` | 56 s | **48.7 s** (45.1 s, 6.9 GB), now with `pfs_honest`, `pfs_cheat` and `decode_kat` |
| `Library/Compile.lean` | 7.2 s (golfed) | 7.6 s |
| `Contract/Compile.lean` | 5.5 s | 5.3 s |

The two control files build in parallel.

### Mutant → killing control

The mutants are one-line mutants of the trusted verifier, from `probes/s3/RevMutants.lean`,
updated to mirror the fixed `NARG` (`logs/S3/fix-rev-mutants.log`). "Before" is the verdict on the
10 control tapes of the first submission.

| Mutant | One-line change | Before | Killed by (fix pass) |
|---|---|---|---|
| `NARGidx` | oracle-0 (index) openings are parsed but not authenticated | survives 10/10 | `idx_path_flip`: `NARG` false, mutant true |
| `NARGplain` | a plain message is read but not absorbed | survives 10/10 | `pfs_cheat` (mutant accepts) and `pfs_honest` (mutant rejects) |
| `NARGrange` | no `l < leaves` check before an opening | survives 10/10 | `oob_rejected`: the mutant accepts leaf 0's opening for query `l = 4` |
| `NARGoff` | index `j` decoded at element `j` (byte `8j`), not `3·nE + j` | survives 10/10, and also the new tapes | `decode_kat`: the true decoder gives index 0 = `0x18`, the mutant `0x00` (`#eval (24, 0)` in the log) |

### Changes, by finding

- **S3-M1. One key digest.** `VKc.digest cfg vkc := cfg.hash.run vkc.toBytes` (trusted, with a
  docstring) hashes the VK elements and the index root.
  - `seed` absorbs `x` into it.
  - The KAT `digest_kat` pins it: `vkc2.digest cfg2` = `0f4c678b…229556d3` =
    `hashlib.blake2s(le64(0x1234) ‖ root)`.
  - S3-A8 supersedes S2-A1's `D`. Stage 5 must use this function.
- **S3-M2. The two unguarded behaviours.** Both controls are in `Controls/CompileFS.lean`:
  - the reviewer's `pfs` protocol (plain `a`, `chal 1 []`, plain `m`; accept iff `m = e.c0 + a`)
    with `pfs_honest` and `pfs_cheat`. The tapes are byte literals, `#guard`ed against the
    encoder's hex and, for the honest tape, against `prove cfg2 pfs`;
  - `decode_kat`.

  `probes/s3/RevMutants.lean` is kept and updated.
- **S3-m1. The reason for "no tag".** The header and S3-A11 now give it correctly: fixed depth and
  per-level lengths. Absorb and squeeze inputs are `1 mod 8`; `D` is in the tree's length domain,
  which is harmless because the indexer fixes its input.
- **S3-m2. Isolating controls.** `idx_path_flip` (`flip tape2 120`) and `oob_rejected` (the
  reviewer's `oob`, with its tape as a literal `#guard`ed against `commit` and `pathOf`) are in
  `runs`.
- **S3-m3. Header gaps (a)–(e), all closed in the module header:**
  - (a) the key bytes;
  - (b) every internal node is hashed from its children, all-padding ones included (`H(0^(32A))`
    at height 1);
  - (c) the children are `A·p … A·p + A − 1`;
  - (d) the index tree uses the same `cfg`;
  - (e) an out-of-range oracle or leaf rejects, so padding is never opened.

  The encoder test above still passes.
- **S3-m4. The key's root.** `NARG` has the conjunct `vkc.2.length == 32`. Its docstring and the
  header say so, and the type is unchanged. `narg_complete` discharges the conjunct with
  `node_length`.
- **S3-m5. The honest prover is now untrusted.** These moved verbatim to `Library/Compile.lean`
  (section "The honest compiled prover"), with their docstrings: `Round.tapeBytes`, `fsPrefixes`,
  `fsTranscript`, `pathOf`, `record` and `prove`. `Controls/CompileToy.lean` imports the library.
- **S3-m6. Stage 5 interface.**
  - New theorem `NARG_eq_true_iff`: `NARG … = true ↔ |t| ≤ tapeCap ∧ |root| = 32 ∧ ∃ es rest,
    pass … = some (es, rest) ∧ runQ … rest = some true`. `narg_local` is now derived from it.
  - `toy_local`, `toy_consistent` and `views_T` are CI controls in `Controls/Compile.lean`. Their
    kernel facts (`pass … = some (esT, …)` and the opened leaves) are in `runs`.
  - **What `C_V` must compute** to force `NARG cfg P vkc x π = true` (the reviewer's list,
    confirmed):
    1. `|π| ≤ 2^20` and `|vkc.2| = 32`;
    2. `s₀ = VKc.digest cfg vkc`, the same value checked against `d0`/`d1`, then
       `s ← H(0x00 ‖ s₀ ‖ x)`;
    3. per round, in shape order: absorb a 32-byte root, or `8·2^logLen` plain bytes, or squeeze
       `24·nE + 8·|idx|` bytes;
    4. decode the challenges as in `decode_kat`;
    5. run `P.verify vk x chals`:
       - a Merkle query has `l < leaves` and an opening of `8·2^logLeaf + depth·(A−1)·32`
         bytes;
       - its leaf hash is climbed with `l`'s base-`A` digits and compared to that round's root,
         or to `vkc.2` for oracle 0;
       - a plain query reads the absorbed elements;
    6. no bytes left over.
- **S3-m7.** `prove cfg2 cmpToy L0 x0 [] = some tape2` stays compiled evidence in CI (`#guard`).
  The kernel version is the probe `probes/s3/RevKernel.lean` (`toy_prove`, 42.6 s CPU, 6.9 GB,
  `logs/S3/fix-rev-kernel.log`). It is kept out of CI for its cost.
- **S3-m8.** S3-A13 states the condition "provided the honest tapes fit `tapeCap`" and assigns
  the 128 KiB board-L cap to Stage 7.
- **S3-m9. Executed costs.**
  - `squeeze.go` `let`-binds the hash.
  - `Cfg.depth` is the closed form `(m + log₂A − 1) / log₂A`, via `Cfg.logArity`, a 4-case
    match. `depth_spec` (Library) proves it is the least `d` with `2^m ≤ A^d`.
  - The challenges are decoded once per round: `NARG` computes `ks = es.map (kList · |>.toArray)`
    once. `Round.decodeK` reads `E` element `j` from `ks[3j..3j+2]` and index `j` from
    `ks[3·nE+j]`, with the same bytes as before. `chals` takes these arrays, so an access is
    O(1) with no `drop`. `Round.decode b := decodeK (kList b).toArray` is kept for the prover
    and `decode_kat`.
- **S3-m10.** Every line of the Stage 3 files is ≤ 100 characters.
- **Golf notes.**
  - `tape2`, `cheatTape` and `vkc2`'s root are byte-list literals. Each is `#guard`ed equal to its
    former hex string, which is the Python output, before that string was removed from the
    definitions.
  - `Mathlib.Tactic.IntervalCases` is dropped.
  - `oversize` uses `decide +kernel` on `0 < tape2.length`, which is instant on a literal.

### Statements that changed, and why

- `narg_complete` and its corollaries are unchanged.
- `narg_local` gains the conclusion `vkc.2.length = 32`, and its challenges are
  `chals P.shape (es.map …)`. Both follow from the trusted changes S3-m4 and S3-m9, not from
  proof convenience.
- `chals_honest` changes in the same way.
- `leaves_le_pow_depth` is now a corollary of `depth_spec`.

### Where I deviated from the reviewer

- **S3-m9.** The reviewer proposed precomputing `Cfg.depth` in `views`. I made `depth` an O(1)
  closed form instead, proved equal to the header's "least `d`" (`depth_spec`). The effect is the
  same, and it avoids adding a field to `View`.
- **`toy_prove` stays a probe**, not a CI control (S3-m7, optional).

Otherwise every finding is applied as proposed.

### Probes touched

- `RevMutants.lean`: updated to mirror the fixed `NARG`, with the kill table added.
- `RevKernel.lean`: reduced to `toy_prove`; `toy_local` is now a CI control.
- `RevBinding.lean`, `RevKill.lean`, `RevEncoder.lean`, `RevAxioms.lean`, `OneRun.lean` and
  `TwoRuns.lean` compile unchanged.

## S9 fix pass

This pass applies S9F-M4 (`docs/reviews/S9-feasibility.md`) and S9D-m5/m6 (the `NARG` part;
`docs/reviews/S9-definitions.md`). The amendments are S9-A10 to S9-A13. Logs are
`logs/S3/s9-*.log`.

### What changed

- **Sparse Merkle commitment (trusted, +13 code lines, 128 → 141).**
  - `commit` computes the header's root with `nodeS`. A subtree that is all padding, or all leaves
    whose elements are all zero, takes its digest from a precomputed tower over the zero digest or
    over `H(all-zero leaf)`. Every other node is hashed.
  - The dense `node` is the specification, now in `Library/Compile.lean`.
  - `commit_eq_commitDense` (via `nodeS_eq` and `node_padding`) proves the sparse root equals the
    dense one for every oracle, configuration and depth.
  - `pathOf`, the honest prover's paths, uses `nodeS` too. `pathOf_eq_dense` proves that equal to
    the dense paths, so `narg_complete` and every other statement is unchanged.
- **Merkle binding in CI (S9D-m5).** `opening_binding` and its helpers are in the Library, and the
  header cites them.
- **`NARG` docstring (S9D-m6).** "`vkc` is any compiled key …".
- **Controls.** New `#guard`s in `Controls/CompileToy.lean` cover a mostly-zero, padded oracle
  (`sparseO`; 64 elements, leaves of 2) at arity 2, 4 and 16. The sparse root equals
  `commitDense` and the independent encoder's root (`logs/S3/s9-sparse-roots.log`).

### Checks

- **Byte-identical outputs:**
  - every existing KAT and `#guard`: honest tapes at arity 2 and 4, `index_eq`, `digest_kat`,
    `prove` outputs, `pfs`;
  - `compile_ref.py` (`logs/S3/s9-python-ref.log`, no diff);
  - `indep_encoder.py`: its output is unchanged, and Lean matches it byte for byte at arity 2,
    4, 8 and 16, padded root included (`logs/S3/s9-indep-encoder-compare.log`; `RevEncoder`
    output unchanged);
  - the mutant table (`logs/S3/s9-rev-mutants.log`) is unchanged.
- **Builds.** The five Stage 3 targets build, and the default `lake build` is green
  (`logs/S3/s9-build-default.log`).
- **Axioms.** `lake exe axiomaudit` reports PASS (`logs/S3/s9-axiomaudit.log`). Declaration
  counts: `Contract.Compile` 111, `Library.Compile` 163, `Controls.CompileToy` 30.
  `#print axioms` (`logs/S3/s9-print-axioms.log`):
  - `NARG`, `commit` and `index` use only `[propext, Quot.sound]`;
  - `commit_eq_commitDense`, `nodeS_eq`, `opening_binding` and `narg_complete` use the standard
    three.
- **Hygiene** reports OK.

### Index timings

`probes/s3/index-bench` (`run.sh`) builds `index` compiled. It indexes `L_chain(2^10)` (class 24)
under `cmpToy`'s rounds at class 24, with an index oracle of `2^m` elements in leaves of 16 that
holds the layout's serialisation (792,851 elements), then zeros.

| Index oracle | Dense (before) | Sparse (after) | Root |
|---|---:|---:|---|
| `cmpToy` (2 leaves) | 0.27 s | 0.31 s | same |
| `2^20` | 3.0 s | 2.5 s | same |
| `2^24` | 41.9 s | 5.3 s | same |
| `2^29` = `2^(k+5)` | 1,342 s | **105 s** | same |
| `2^32` = cap `2^(k+8)` | ≈ 3 h (extrapolated) | **861 s** | — |

Peak memory is 130 MB at every size, so the commitment streams and nothing is materialised. What
remains is one read of every index element, about 200 ns each. At the cap that is 14 min at
k = 24 and ≈ 3.7 h at k = 28. Removing it needs a `Protocol`-level support bound for `IDX`, which
is outside these files (S9-A10).

### Other files touched (necessarily)

The trusted `commit` no longer unfolds to `node`, so three proofs that used `node_length` for a
key's root now use `commit_length`:
- `Library/Recursion.lean` (two lines);
- `Controls/MagicKey.lean` (one line);
- `probes/s5/review/MagicKey.lean`. That probe already had 9 unrelated errors at `HEAD`.

The reviewer's probes `RevMutants.lean` and `RevKill.lean` are updated to Stage 4's `Protocol`
(the `extractor` field), and `RevEncoder.lean` drops its own `cfg16`.

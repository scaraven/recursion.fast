# S3 review: the compiled argument (`Contract/Compile.lean`)

**Verdict: ACCEPT WITH FIXES.** I found no forgery path in `NARG`. Every item of the
structural-soundness checklist below either holds by a kernel-checked theorem or has a stated
argument. In particular:

- Merkle binding at a fixed depth reduces to collision resistance **without** a leaf/node tag
  (`opening_binding`, kernel-checked, general in `cfg` and the shape).
- Every 8-byte string is a canonical element, so the tape has no malleable encodings.
- The openings cannot influence a challenge (`pass_extend`).
- An independent encoder, written from the module header alone, reproduces Lean's honest tapes
  byte for byte at arities 2, 4, 8 and 16.

`narg_complete` and `narg_local` say what the RESULT claims. Both are general, and both are
non-vacuous: `prove` returns `some` *in the kernel*, and the honest oracles are `Consistent`
(`probes/s3/RevKernel.lean`). Trust hygiene holds: there are no theorems in the trusted file, no
forbidden constructs, and the 23 Stage 3 declarations use only `propext`, `Classical.choice` and
`Quot.sound`.

There are two major findings:

- **S3-M1** (cross-stage soundness hazard). The key digest `D` is not a named definition. The
  applied DESIGN §5.1 still defines `D` over the VK elements **without** the index root.
  Implemented as written, a recursion node could verify a child under an index root of its own
  choosing.
- **S3-M2** (regression net). Two Fiat–Shamir-critical behaviours are guarded by no control and
  no theorem:
  - a plain message must be absorbed before the challenges that follow it;
  - the byte layout of the challenge decoding.

  One-line mutants of each pass the whole suite. I give the killing controls, kernel-checked.

There are ten minor findings, S3-m1 to S3-m10. On **S3-A2**, I recommend accepting "no tag", with
the justification corrected (S3-m1).

Date: 2026-10-14. Scope (sha256 at review time, `logs/S3-review/reviewed-sha256.txt`):

- `Contract/Compile.lean` `14cb6efd…`, unchanged during the review;
- `Library/Compile.lean`, under concurrent golf (`bcc62995…`, then `52e74032…`). Both elaborate,
  and I cite statements only, which golf does not change;
- `Controls/Compile.lean` `67965556…`, `Controls/CompileFS.lean` `dccad927…` and
  `Controls/CompileToy.lean` `61aa5a0f…`;
- `docs/stages/S3-RESULT.md`, `docs/DESIGN-AMENDMENTS.md` (S3-A1…A7), and DESIGN §3.1–§3.2,
  §5, §6.5 and §8.

Method: I formed the expectation from BCS (Merkle commitments at a fixed depth, openings bound to
the query position, the verifier replayed over the openings) and from a hash-chain Fiat–Shamir
transform, before reading the bodies. I wrote the encoder before opening `compile_ref.py`. The
probes are in `probes/s3/Rev*.lean` and `probes/s3/{indep_encoder,cmp_encoder,domains}.py`, and
the logs in `logs/S3-review/`.

## Findings

### S3-M1 (major): the key digest `D` must be one definition, shared by the seed and `aggOK`, and must include the index root

**Declarations:** `seed`, `VKc.toBytes`, DESIGN §5.1 (`D`), S2-A1 and S3-A5.

**Problem.**
- `seed` hashes `cfg.hash.run vkc.toBytes`, which covers the VK elements followed by the 32-byte
  index root.
- The applied DESIGN §5.1 defines `D vk := blake2s256 ((vk.flatMap K.toBytes).map
  UInt8.ofBitVec)`, which covers the VK elements only.
- S3-A5 says `D` "should" hash `VKc.toBytes`. Nothing in the code ties the two together, and
  `VKc.toBytes`'s docstring cites the §5.1 text, which disagrees with it.

**Failure if §5.1 is implemented as written.**
1. `aggOK` checks `D nw.vkC = x'.d0` and then `NARG cfg P nw.vkC x π`.
2. With `D` blind to `nw.vkC.2`, the node witness picks any index root `root'`, for example the
   commitment to the index of a layout that accepts everything.
3. The child's `NARG` then authenticates oracle-0 openings against `root'`. The seed changes,
   but the prover recomputes its challenges under it.
4. The organiser's root check `d0 = D(VK C_V)` still passes, so the recursion proves nothing
   about `C_V`.

S3-A3's cost argument ("`C_V` computes `D` anyway, so the seed reuses it") also holds only if
the two are the same function.

**Fix (three lines in the trusted file, plus DESIGN).**
1. Add the definition
   `def VKc.digest (cfg : Cfg) {vkLen} (vkc : VKc vkLen) : Digest := cfg.hash.run vkc.toBytes`.
   Its docstring: "the key digest `D` of DESIGN §5.1: VK elements, then the index root. It seeds
   the sponge, and a recursion statement's `d0`/`d1` hold it."
2. Write `seed` as `absorb cfg (vkc.digest cfg) (stmtBytes x)`.
3. Replace DESIGN §5.1's `D` with `VKc.digest cfg`:
   - `d0 = VKc.digest cfg (index cfg P C_V)`;
   - `d1 = VKc.digest cfg (index cfg P L_chain)`.

   Stage 5 must reuse the definition, not restate it.
4. Add a KAT control: `vkc2.digest cfg2` equals `hashlib.blake2s(vk ‖ root)`.

### S3-M2 (major): plain-message absorption and challenge decoding are not guarded

**Declarations:** `pass` (`.msg` case with `o.plain`), `Round.decode`, `chals`, and the
`cmpToy` suite.

**Problem.**
- In `cmpToy` the only plain message (round 2) comes **after** the only challenge round, so its
  absorption affects nothing.
- The toy's index challenge `i = 2` is also what the wrong byte offsets 0 and 8 give: the
  squeezed bytes `a2…`, `0a…` and `c6…` all have low bits `10`.
- The verifier never reads `e.c1` or `e.c2`.

**Probe.** `probes/s3/RevMutants.lean` (compiled evaluation, `logs/S3-review/rev-mutants.log`).
Two one-line mutants of the trusted verifier give **the same verdict as `NARG` on all 10 control
tapes**:
- `NARGplain`: `pass` reads a plain message but does not absorb it;
- `NARGoff`: index `j` is decoded at byte `8 j` instead of `24·nE + 8 j`.

No theorem catches them either, when the mutation is consistent:
- `NARGplain` applied to `pass` and `fsPrefixes` together keeps `narg_complete`, and
  `narg_local` has no Fiat–Shamir content;
- a mutation inside `Round.decode` is shared by `NARG` and `prove`.

**Both matter for soundness.**
- The first is exactly the case S3-A1 exists for, a sumcheck polynomial sent in the clear before
  its challenge. Without the absorb, the prover picks the polynomial after seeing the challenge.
- The second correlates the index challenges with the `E` challenges, and the IOP's RBR errors
  assume independent uniform challenges.

**Fix (both kernel-checked in the probes).**
- Add the control protocol `pfs`: rounds plain `a`, `chal 1 []`, plain `m`; the verifier accepts
  iff `m = e.c0 + a`. It has two tapes, pinned to the independent encoder (`pfs_tapes`):
  - honest `0500…0303`, accepted;
  - `pfsCheat` `0600…4d74`, rejected. This tape chooses `a = 6` after the challenge of a sponge
    that skips plain messages.

  `probes/s3/RevKill.lean` (`kill`) checks both, together with the index-path control of
  S3-m2, in one `decide +kernel`: 49 s CPU, 6.7 GB (`logs/S3-review/rev-kill.log`). The mutant
  accepts the cheat (`RevMutants.lean`).
- Add `decode_kat` (`probes/s3/RevBinding.lean`, no hashing, under a second). It checks
  `(chal 1 [8, 64]).decode (0…47)`: `E` limbs from bytes 0–7, 8–15 and 16–23, index 0 =
  `0x18`, index 1 = the word at byte 32. This pins the limb order too.

### Minor findings

**S3-m1: the stated reason for "no tag" is partly false; the real reason is fixed depth**
(module header, S3-A2, `seed`).
- The header says "sponge inputs have length `1 mod 8` while tree inputs have length
  `0 mod 8`". The seed's first hash `H(VKc bytes)` has length `8·vkLen + 32 ≡ 0 mod 8`.
- At `vkLen = 4(A−1)` that is a node input, and at `vkLen = 2^logLeaf − 4` a leaf input
  (`probes/s3/domains.py`, `logs/S3-review/domains.log`).
- `key_digest_is_node` (kernel) shows that at arity 2 with `vkLen = 4`, `H(VKc bytes) = climb …`
  over the key's 32 bytes and the index root.
- This is harmless. The input is fixed by the indexer, and a commitment whose root equals the
  seed is a commitment to a tree fixed before `x` is absorbed.
- Leaf and node inputs also coincide when `2^logLeaf = 4A`: `(A, logLeaf)` is `(2,3)`, `(4,4)`,
  `(8,5)` or `(16,6)`.
- Neither coincidence matters, because `readOpening` fixes the number of levels and the
  per-level input lengths. `opening_binding` proves that this alone gives binding.

Fix: reword the header and S3-A2: "binding at a fixed depth reduces to collision resistance
(the depth and the per-level lengths are fixed by the shape). Absorb and squeeze inputs have
length `1 mod 8`, tree inputs `0 mod 8`. The key digest `D` is in the tree's length domain, and
its input is fixed by the indexer."

**S3-m2: index authentication and the leaf-range check have no isolating control**
(`runQ`; `idx_leaf_flip`, `leaf_flip`).
- `idx_leaf_flip` and `leaf_flip` are also rejected by the toy verifier's value checks, so they
  do not show the Merkle check.
- No control flips an index-path digest, and no query is out of range: the toy's `i < 4` and
  `i % 2 < 2` are always in range.
- Two mutants survive all controls (`RevMutants.lean`):
  - `NARGidx` does not authenticate oracle 0;
  - `NARGrange` drops `l < leaves`, and then accepts leaf 0's opening for query `l = 4`, because
    `4 mod 2^2` has the same base-`A` digits.
- `runQ_local`'s case splits on `verifyPath` and on `l < leaves` would break under both mutants,
  as long as `opened` is not mutated in step. They are guarded only indirectly, which is why
  this is minor.

Fix:
- add `NARG cfg2 cmpToy vkc2 x0 (flip tape2 120) = false` (index path; kernel-checked in `kill`)
  to `runs`;
- add the control `oob`: `cmpToy`'s rounds with a verifier that reads leaf 4 of oracle 1, and a
  tape holding leaf 0's valid opening, which must be rejected (`RevMutants.lean`: `NARG` false,
  mutant true).

**S3-m3: the header's grammar leaves ambiguities for native provers** (module header). I
resolved each one by reading Lean, not the header:
- (a) "VKc bytes" is not defined in the header; only `VKc.toBytes`'s docstring defines it.
- (b) "padded with the zero digest … to `A^depth` positions" does not say that an internal node
  whose children are all padding is hashed from them (`H(0^(32A))` at height 1), not set to the
  zero digest. The two readings give
  different roots, for example 8 leaves at `A = 4` (`RevEncoder.lean` against `indep_encoder.py`).
  No existing guard or Python check exercises this, because the toy's trees have no all-padding
  internal node.
- (c) The children of node `p` are `A·p … A·p + A − 1`. This is implied, not stated.
- (d) The index tree uses the same `cfg` (hash and arity).
- (e) A query with `l ≥ leaves` rejects, so padding positions are never opened. This is in the
  RESULT, not the header.

Fix: add one sentence for each to the header.

**S3-m4: `VKc`'s root is an unconstrained `List UInt8`** (`VKc`, `Digest`).
- `NARG` accepts keys whose root is not 32 bytes. The seed is then defined, and every oracle-0
  query fails.
- Under S3-M1's `D` this is not exploitable: `vkLen` fixes the VK prefix, so `D` is injective up
  to collisions.
- But Stage 5's `decode` produces `VKc` values from witness cells, so the type should carry the
  length.

Fix: make the root `Vector UInt8 32`, or have `NARG` check `vkc.2.length = 32`, or document why
neither is needed.

**S3-m5: the honest prover is in the trusted file but no trusted statement uses it**
(`Round.tapeBytes`, `fsPrefixes`, `fsTranscript`, `pathOf`, `record`, `prove`; about 38 of the
159 code lines). Nothing in `Contract/` and no planned trusted statement in DESIGN §5.3 refers to
`prove`. Only `Library/Compile.lean` and the controls do, and Stage 5 needs it only in the Library.
Fix: move them to `Library/Compile.lean`, or keep them and mark them as "a specification, not in
the cone of any trusted statement".

**S3-m6: `narg_local` is the right core for the ROM argument but not what Stage 5 proves**
(`narg_local`, `runQ_local`).
- `narg_local` goes from `NARG = true` to an accepting IOP run. That is what the (non-Lean) BCS
  extractor needs, and it is non-vacuous (`toy_consistent`, `toy_local` in `RevKernel.lean`).
- `RecursionEntry.sound` needs the converse, "constraints ⇒ `NARG … = true`". Its useful library
  form is an unfolding `NARG_eq_true_iff`: cap, then `pass … = some (es, rest)`, then
  `runQ … rest = some true`.

Fix: add that lemma, and the "what `C_V` computes" list below, to the RESULT for Stage 5. Add
`toy_local` as a control: it is the only witness that `Consistent` is satisfiable.

**S3-m7: `prove` non-vacuity is checked only in compiled code** (`#guard prove cfg2 … = some
tape2`).
- The positive control's non-vacuity rests on the Lean compiler. `toy_kernel` checks it in the
  kernel (≈ 100 s CPU, 10 GB, together with `pass` and `opened`).
- The tapes are pinned to Python, so this is defence in depth.

Fix: optional. Either add the kernel theorem or say in the RESULT that this one is compiled
evidence.

**S3-m8: two claims are conditional or unowned** (S3-A6, DESIGN §6.5).
- "Completeness closes S1-A12(c)" holds only when the honest tapes fit `tapeCap`: `prove_isSome`
  says `prove` is `none` otherwise. A `P` whose honest proofs exceed 1 MiB still makes `aggOK`,
  and hence `RecursionEntry.complete`, vacuous.
- DESIGN §6.5's L-board cap of 128 KiB is not enforced by `NARG`, and no stage owns it yet.

Fix: reword S3-A6 to "…provided the honest tapes fit `tapeCap`". Assign the 128 KiB cap to the
certificate or the harness (Stage 7).

**S3-m9: executed-verifier costs** (`squeeze.go`, `chals`, `Cfg.depth`). These are not about
soundness:
- `squeeze.go` writes `cfg.hash.run (1 :: s)` twice; `let` it.
- `chals` re-decodes on every access, with an `O(j)` `drop` per element.
- `Cfg.depth` is recomputed on every query (RESULT question 5).

Fix: `let`-bind the hash; precompute the decoded challenges and depths in `views` and `chals`.

**S3-m10: style.** `Controls/CompileToy.lean`, line 114 of the reviewed version (the `tape2`
docstring), is 106 characters, over the limit of 100.

## Structural-soundness checklist (for the report's §13 threat table)

✓ means the structure excludes the attack. "Kernel" names a kernel-checked theorem in
`probes/s3/` or in the stage. Otherwise the argument is given in one line.

| # | Item | Verdict |
|---|---|---|
| MK1 | Merkle depth fixed by the shape | ✓ `readOpening` reads exactly `Cfg.depth o` levels of `A − 1` 32-byte digests (kernel: `readOpening_shape`). |
| MK2 | Internal node opened as a leaf | ✓ Excluded at every leaf size, including `2^logLeaf = 4A`. Kernel: `opening_binding` gives the same leaf or a hash collision. |
| MK3 | Leaf opened at the wrong position | ✓ The position is the query's `l`, consumed digit by digit (base `A`) in `climb`. The prover supplies no index. Binding per position: `opening_binding`. |
| MK4 | Sibling layout at arity 4, 8 and 16 | ✓ Current digest inserted at `p mod A`, siblings in increasing position. The independent encoder agrees at 2, 4, 8 and 16. |
| MK5 | Padding of non-full trees | ✓ `l < leaves` is checked before any opening, so padding is never opened as data. Padding siblings are not checked to be zero, which is harmless because they are bound by the root. An all-padding internal node is hashed from its children (`H(0^(32A))` at height 1), not set to the zero digest (S3-m3(b)). No control covers the range check (S3-m2). |
| MK6 | No leaf/node tag (S3-A2) | ✓ Sound at a fixed depth (kernel: `opening_binding`). The length coincidences `2^logLeaf = 4A` exist and do not matter. Recommend accepting, with S3-m1's wording. |
| MK7 | Second-preimage attack of variable-depth trees | ✓ Excluded: the path length is the shape's, never the prover's. |
| MK8 | Duplicate queries | ✓ Each is opened again (S3-A4) and both openings must verify. They agree unless there is a collision (`opening_binding`). |
| FS1 | Key and statement absorbed before anything | ✓ `s = H(0x00 ‖ H(VKc) ‖ x)`. `stmt_flip` shows `x` is bound even where the verifier never reads it. |
| FS2 | Index root in the seed | ✓ `VKc.toBytes` ends with `vkc.2`. `D` must be the same function (**S3-M1**). |
| FS3 | Every prover message absorbed before the challenges after it, in round order | ✓ by `pass`. The root case is controlled (`root_flip`, `fs_binding`); the plain case is **not controlled** (**S3-M2**, `pfs` kills it). |
| FS4 | Openings cannot influence a challenge | ✓ Kernel: `pass_extend`. Bytes after the rounds section leave the round bytes, and so the challenges, unchanged. |
| FS5 | Absorb and squeeze separated; injective absorb | ✓ Tags `0x00`/`0x01`. The state has a fixed 32 bytes and each round a fixed length, so an absorb input determines `(s, m)`. A squeeze equals an absorb only by a collision. |
| FS6 | Tree and sponge separated | ✓ for absorb and squeeze (`1 mod 8` against `0 mod 8`). ✗ for the key digest (`0 mod 8`, S3-m1), which is harmless because its input is fixed by the indexer. |
| FS7 | Squeezed bytes to `E` and to indices | ✓ `E`: a bijection from 24 bytes (limbs LE). Index: the low `b` bits of an LE word, exactly uniform for `b ≤ 64` (the shape cap). There are no `K` challenges and no modular bias. Decoding offsets are not controlled (**S3-M2**, `decode_kat`). |
| FS8 | Re-ordering and grinding | ✓ Re-ordering is impossible: each state hashes the previous one. Grinding (retrying prefixes) is possible and is priced by `ε ≤ 2^-128` per round. There is no nonce. |
| FS9 | The squeeze output is the next state | ✓ Harmless (public coin; BLAKE2s has no length extension). |
| RP1 | Each opening bound to its query `(j, l)`, in order | ✓ `runQ` consumes one opening per query and checks it against `vs[j]`'s root at `l`. |
| RP2 | A round's oracle checked against that round's root | ✓ `views` maps oracle `j ≥ 1` to the `j`-th message round's bytes in `es`. |
| RP3 | Oracle 0 is the index root from the key | ✓ `views P vkc.2 es` puts `View.root P.idxShape vkc.2` first. No isolating control (S3-m2: `flip tape2 120`). |
| RP4 | The `x` hashed is the `x` verified | ✓ The same `x` goes to `seed` and to `P.verify`. |
| RP5 | Out-of-range oracle or leaf rejects | ✓ `vs[j]? = none`, or `l ≥ leaves`, gives `none`. No control (S3-m2: `oob`). |
| PA1 | Leftover bytes | ✓ `runQ (.done _) (_ :: _) = none` (`leftover`). |
| PA2 | Truncation | ✓ `takeN` gives `none` (`truncated`). |
| PA3 | 1 MiB cap | ✓ Checked first (`narg_oversize`). The 128 KiB L cap is not here (S3-m8). |
| PA4 | Length fields, negative lengths | ✓ There are none: every length comes from the shape. |
| PA5 | Non-canonical `K` or `E` encodings | ✓ Every 8-byte string is canonical (kernel: `K.bytes_ofBytes`, `kList_bytes`). `E` never appears on the tape. |
| PA6 | Totality | ✓ Structural recursion everywhere, with no `partial`, `unsafe` or `implemented_by`. Runs on 1 MiB are tail-recursive (`takeN`, `kList.go`, `pass`, `climb`). `readMany` is bounded by `depth ≤ 38` and `A − 1 ≤ 15`. |
| PA7 | Well-formed key | ✗ Not checked: the root may have any length (S3-m4). Not exploitable once **S3-M1** is fixed. |

## Statements (`Library/Compile.lean`)

- **`narg_complete`** is general in `cfg` (all arities), `P`, `L`, `x`, `w` and `t`. Its
  section variables carry no hidden hypotheses.
  - Hypothesis `prove … = some t`: inhabited, in the kernel (`toy_kernel`).
  - Hypothesis `specVerifier` accepts the Fiat–Shamir transcript: not checked separately on the
    toy, but `toy_local` evaluates the same run on the honest oracles. For a secure `P` it is
    discharged by `narg_complete_of_secure`.
- **`prove_isSome`**: `prove` fails only by the cap, which is non-vacuous.
- **`narg_local`**: its hypothesis is inhabited (`honest_accepted`), and its conclusion
  quantifies over a satisfiable `Consistent` (`toy_consistent`). It is vacuous only for tapes
  that open one position with two different leaves, which needs a collision (`opening_binding`).
  That is the correct behaviour.
- **What `C_V` must compute (Stage 5).** `C_V` must force `NARG cfg P vkc x π = true`, which
  means all of the following:
  1. `|π| ≤ 2^20`;
  2. `s₀ = VKc.digest cfg vkc` (shared with the `d0`/`d1` check, S3-M1), then
     `s ← H(0x00 ‖ s₀ ‖ x)`;
  3. per round, in shape order: absorb a 32-byte root, or `8·2^logLen` plain bytes, or squeeze
     `24 nE + 8|idx|` bytes;
  4. challenge decoding as in `decode_kat`;
  5. the run of `P.verify vk x chals`. Each Merkle query has `l < leaves` and an opening of
     `8·2^logLeaf + depth·(A−1)·32` bytes. The leaf hash is climbed with `l`'s base-`A` digits
     and compared to that round's root, or to `vkc.2` for oracle 0. Each plain query reads the
     absorbed elements;
  6. no bytes left over.

  `narg_local` is not used for this direction (S3-m6).

## Independent encoder (interface for Stage 5 and native provers)

I wrote `probes/s3/indep_encoder.py` from the module header and the `cmpToy` docstring alone,
using `hashlib.blake2s`. I opened `compile_ref.py` only afterwards.

**Result:** byte-for-byte equality with Lean's `prove` output and index roots at **arity 2, 4, 8
and 16**:

| Arity | Tape length (bytes) |
|---|---:|
| 2 | 152 (= `tape2`) |
| 4 | 248 (= the `#guard`) |
| 8 | 504 |
| 16 | 1016 |

All four tapes are accepted by `NARG`. The evidence is in `logs/S3-review/rev-encoder.log`,
`indep-encoder.log` and `indep-encoder-compare.log` (`probes/s3/cmp_encoder.py`). Lean's padded
root (8 leaves, `A = 4`) equals the literal reading of the header, under which every internal
node is hashed.

**Ambiguities I resolved by reading Lean:** S3-m3 (a) to (e).

`compile_ref.py` builds trees with the same recursion as Lean's `node`, so it does not test (b)
independently.

**What Stage 5's `D` must be:** `D(vkc) = cfg.hash.run (VKc.toBytes vkc)`, that is the hash of
the VK elements (8 bytes LE each) followed by the 32-byte index root, as one named definition
that `seed` also uses (S3-M1). A digest becomes a statement slot as S2-A1 says: limb `j` is
bytes `8j … 8j+7`, little-endian.

## Amendments: wording or meaning

| Amendment | Kind | Recommendation |
|---|---|---|
| S3-A1 plain one-leaf oracles | Meaning (format; the security is the same, binding by the sponge) | Accept. Needs S3-M2's `pfs` control. |
| S3-A2 no leaf/node tag | Meaning (departs from the instruction) | **Accept.** `opening_binding` proves binding at a fixed depth without a tag. A tag costs one extra compression per leaf for `logLeaf ≥ 3` (8 elements: 1 → 2 compressions, `domains.log`), both natively and in `C_V`. Correct the justification (S3-m1). A zero-cost tag would need BLAKE2s personalization, i.e. an extension of the trusted hash spec: not now. |
| S3-A3 seed `D(VKc) ‖ x` | Meaning (byte level; binding is the same under collision resistance) | Accept, conditional on **S3-M1**. |
| S3-A4 `Cfg` = hash + arity, no batching | Meaning (the menu shrinks) | Accept. Decide on multi-opening before native provers exist (RESULT question 4): it changes the grammar. |
| S3-A5 `VKc`, cap, leftover reject, no blow-up cap | Meaning (key type; `D`'s input) | Accept with **S3-M1** and S3-m4. Update DESIGN §5.1 and §3.2's `VKBytes`. |
| S3-A6 completeness theorems | Wording (and new theorems) | Accept, with S3-m8's condition. |
| S3-A7 controls | Wording | Accept, and add S3-M2's and S3-m2's controls. |

## The three passes

- **Specification (Pass A).** The statements are general and non-vacuous (above). No statement
  restates its definition.
- **Fidelity (Pass B, against DESIGN §3.2 and standard BCS/FS).**
  - Every §3.2 item is present, or recorded as an amendment:
    - BCS per round;
    - the index committed once, its root in the key;
    - openings of the honest run;
    - a domain-separated sponge with the key and statement first;
    - `NARG` total and deterministic, with a 1 MiB cap.
  - §11 step 4's controls are present.
  - The deviations are the amendments above. The one fidelity defect is S3-M1, between Stage 3
    and §5.1.
- **Hygiene (Pass C).**
  - The trusted file has 159 code lines (`scripts/loc.py`) and 0 theorems.
  - It imports only `Contract.Protocol` and `Contract.Hash.Blake2s`.
  - Every declaration has a docstring that states its meaning.
  - There is no `sorry`, `native_decide`, `implemented_by`, `extern`, `csimp`, `partial`,
    `unsafe`, `bv_decide` or `set_option` in any Stage 3 file.
  - Header against code: it matches, except the `1 mod 8` claim (S3-m1) and the gaps of S3-m3.

**Lean4 review, Layer 1.**
- Build: `Contract/Compile` (5.5 s), `Library/Compile` (current golf version, 11.6 s) and
  `Controls/CompileToy` (10.7 s) elaborate without errors under `lake env lean`
  (`logs/S3-review/elab.log`). I did not rebuild `Controls/Compile` or `Controls/CompileFS`, to
  avoid racing the golf agent; their oleans load (`RevAxioms.lean`).
- `sorry`: 0.
- Axioms: `#print axioms` on `NARG`, `prove`, `index`, `narg_complete`,
  `narg_complete_of_perfect`, `narg_complete_of_secure`, `prove_isSome`, `narg_local`,
  `narg_oversize` and all 14 control theorems gives exactly
  `[propext, Classical.choice, Quot.sound]` (`logs/S3-review/axioms.log`).
- Style: one line over 100 characters (S3-m10).
- Golf is left to the golf agent.
- Layer 2 (mathlib style) is advisory and was not run: this is not a mathlib-targeted project.

## Probes

Run from the repository root with `lake env lean …` or `python3 -I …`. The logs are in
`logs/S3-review/`.

| # | Probe | Kind | What it shows | Cost |
|---|---|---|---|---|
| 1 | `probes/s3/indep_encoder.py`, `cmp_encoder.py` | Python | Independent tapes at arity 2/4/8/16; the padding reading; `pfs` tapes | < 1 s |
| 2 | `RevEncoder.lean` | compiled `#eval` | Lean's tapes, index roots and acceptance at arity 2/4/8/16; padded root; `Cfg.depth` table | 6 s |
| 3 | `RevBinding.lean` | kernel, general | `opening_binding` (MK2, MK3, MK6, MK8), `K.bytes_ofBytes`/`kList_bytes` (PA5), `key_digest_is_node` (S3-m1), `pass_extend` (FS4), `decode_kat` (S3-M2) | 13 s |
| 4 | `RevKernel.lean` | kernel evaluation | `toy_kernel` (`prove = some tape2`, `pass`, `opened`), `toy_consistent`, `toy_local` (non-vacuity) | 103 s CPU, 10.3 GB |
| 5 | `RevAxioms.lean` | `#print axioms` | 23 Stage 3 declarations: the standard three | 6 s |
| 6 | `RevMutants.lean` | compiled `#eval` | 4 one-line mutants (`NARGidx`, `NARGplain`, `NARGrange`, `NARGoff`) survive all 10 control tapes; the killing tapes | 7 s |
| 7 | `RevKill.lean` | kernel evaluation | `kill`: `idx_path_flip` rejected, `pfs` honest accepted, `pfsCheat` rejected | 49 s CPU, 6.7 GB |
| 8 | `probes/s3/domains.py` | Python | Hash input-length domains; leaf/node/key coincidences; tag cost | < 1 s |

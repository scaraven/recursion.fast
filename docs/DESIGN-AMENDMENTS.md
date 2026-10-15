# DESIGN amendments (for the orchestrator to patch into `docs/DESIGN.md`)

All items up to S2-A2 were applied to docs/DESIGN.md on 2026-10-14; the list is kept as the change log.

Each item is tagged with the stage that produced it. It gives the agreed change and the wording to
put into `docs/DESIGN.md`. The implemented Lean is the reference.

## Stage 1 (decision pass of 2026-10-14)

- **S1-A1 (sparse gadget matrices; §2.1, §2.2).**
  - **§2.1 draft:** `Gadget.M : Fin t → List (Fin cons × Fin width × K)` is an entry list
    `(row, column, value)`; entries at the same position are summed (the v0.3 `SpMat` convention).
    `rowDot M z r` is the sum of `v · z c` over the entries `(r, c, v)` of row `r`.
  - **§2.1 reading guide:** add "the index size is bounded by the caps independently of the row
    counts, because matrices are sparse".
  - **§2.2 table:** add the row `cols ≤ 2^10` per chip ("bounded index; dense views"). Add the row
    "matrix entries Σ over all chips and matrices `≤ 2^(k+4)`" ("a layout-independent index oracle
    of `2^(k+8)` K-elements suffices at every class; Stages 4 and 7 rely on this"). The gadget row
    keeps `t ≤ 2^6`, `cons ≤ 2^8`, `q ≤ 2^8`.
  - **Library:** `Gadget.holds_iff` (Library) is the bridge to Mathlib's dense `Matrix.mulVec`
    through the denoted matrix (`spToMat`, duplicates summed).
- **S1-A2 (class range; §2.2, §3.1).**
  - **§2.2:** remove the row `20 ≤ k ≤ 28` from `Layout.Admissible`. The relation and
    admissibility are defined at every `k`.
  - **§3.1:** add the field `k_range : 20 ≤ k ∧ k ≤ 28` to `Protocol k` ("the class is in range;
    stated once, in the protocol").
  - **§2.3:** add the control "a protocol whose verifier rejects everything is not `Secure`".
- **S1-A3 (statement location; §2.1, §2.2, §5.1).**
  - **§2.1:** the statement is cells `0…31` of row 0 of the public chip, not column 0 over 32
    rows. `Layout.rel` takes `x : Fin 32 → K`, and its clause is "the public table has a row, and
    `T.cell 0 i = x i` for `i < 32`".
  - **§2.2 table:** the statement row becomes "exactly 32 K-elements (8 digests); the public chip
    has `≥ 32` columns".
  - **§2.1 reading guide:** replace the R1CS sentence with "R1CS with public input `x` is one chip,
    one row, no ports, `pub = 0`, with `x` in the first 32 columns. This holds without
    qualification for `≤ 2^8` constraints and `≤ 2^10` columns. A larger R1CS is several one-row
    chips or a uniform gadget over rows. A flat AIR is one chip with `rows` rows and no ports. A
    multi-chip zkVM is the general case."
  - **§2.3:** `R1CS_iff_layout` now relates the layout to `R1CS A B C x w` with `z = (x, w)`.
  - **§3.1:** `relK` passes `x` directly (no `List.ofFn`).
- **S1-A4 (CCS multisets; §2.1, §2.2).**
  - **§2.1:** `Gadget.S : Fin q → List (Fin t)`, an ordered multiset. (`Multiset.prod` would need
    `CommMonoid`, which the trusted `K` does not have.)
  - **§2.1:** `holds` = `∀ r, (List.ofFn fun i => c i * ((S i).map fun j => rowDot (M j) z r).prod).sum = 0`.
  - **§2.2:** the degree cap is `(S i).length ≤ 8`.
- **S1-A5 (noted for Stage 5, O-1).** Witness tables are `ℕ → ℕ → K`, but `rel` reads them only
  inside `rows × cols` (`rel_trim_iff`). The extractor image's `WitMid` serialisation can therefore
  output trimmed tables; `Library/Codec.lean` (`decWit`, `trim_decWit_wOracle`) is a template.
- **S1-A6 (noted for Stage 6, §5.3).** The comment `fits : C.Admissible k -- includes cells ≤ 2^k`
  is inaccurate: cells depend on the witness and are bounded by `rel`, not by `Admissible`. The
  fixed point "`C_V` fits class `k`" is enforced by `complete`, since an honest node witness must
  satisfy `C.rel k`, which contains the cell bound.
- **S1-A7 (wording; §2.1 and §8, from the implementation).**
  - **§2.1:** the trusted relation is written with list folds over `Field.lean`'s `+`, `*`, `0`,
    `1`, not with Mathlib's `∑`, `∏`, `mulVec`, because the trusted `K` carries no ring structure.
    The library proves the equivalence.
  - **§2.1:** the fixed-table clause compares the height and the cells in `rows × cols`, not full
    function equality.
  - **§2.2:** `Admissible` also requires `1 ≤ cols` and ports that read their own columns.

## Stage 2 (fix pass of 2026-10-14)

- **S2-A1 (noted for Stage 5; §5.1, from S2-m3).** `D` hashes the VK's canonical bytes:
  `D vk := blake2s256 ((vk.flatMap K.toBytes).map UInt8.ofBitVec)`. `K.toBytes` gives `BitVec 8`;
  `UInt8.ofBitVec` is `UInt8`'s constructor, so the bridge is definitional. A digest becomes a
  statement slot `d_i` of 4 K-elements, limb `j` being digest bytes `8j … 8j + 7` read
  little-endian (Rust `u64::from_le_bytes`, the inverse of `K.toBytes`). `K.ofBytes` (or
  `Digest.toK`) is to be added in Stage 5, with a round-trip control and a KAT on `D`.
  `blake2s256_length` (`Library/Blake2s.lean`) gives the 32 bytes.
- **S2-A2 (wording; §3.2, §5.1–§5.2, §7.1, from S2-m10).** The design's one-argument `blake2s(·)`
  / `Blake2s(·)` is `RecursionFast.blake2s256` (unkeyed, 32-byte digest). `RecursionFast.blake2s`
  is the general keyed function `blake2s key nn msg` of RFC 7693 §3.3.

## Stage 1 fix pass (after the S1 review, 2026-10-14)

- **S1-A8 (S1-M1: the verifier is a query program; §3.1, §3.2).**
  - **§3.1:** add v0.3's adaptive `QProg α` (`done a`, `query j l cont`) and
    `QProg.eval : QProg α → List Oracle → Option α` (an out-of-range oracle or leaf gives `none`,
    i.e. reject).
  - **§3.1:** add `chalOf tr : Challenges sh`.
  - **§3.1:** replace the `verify` field by
    `verify : (Fin vkLen → K) → Stmt → Challenges shape → QProg Bool`.
  - **§3.1:** `specVerifier s tr` accepts iff
    `(P.verify (P.VK s.1) s.2 (chalOf tr)).eval (⟨P.idxShape, P.IDX s.1⟩ :: tr.oracles) = some true`.
    Oracle 0 is the index, then the prover's oracles in round order.
  - **§3.1 prose:** "the verifier sees an oracle's contents only through `query`, leaf by leaf;
    this is exactly what the compiled argument opens".
  - **§3.2:** compile opens the leaves that the run on the honest oracles reads, each with an
    authentication path. `probes/s1/VerifyNotLocal.lean` (`eval_local`) shows the result depends
    only on those leaves.
- **S1-A9 (S1-m8a: shape caps; §3.1, §6.5).**
  - **§3.1:** `Protocol k` gets the field `shape_ok`. Every round is `Round.Admissible k`: a
    message oracle has `logLeaf ≤ logLen ≤ k + 10`, an index challenge `≤ 64` bits. The index
    oracle has `logLeaf ≤ logLen ≤ k + 8`. These are v0.3's `OShape.Admissible`, `IdxAdmissible`
    and `Round.Admissible`, now stated once, as a field.
  - **§6.5 table:** add the rows "message oracle `≤ 2^(k+10)` elements", "index oracle
    `≤ 2^(k+8)`" and "index challenge `≤ 64` bits".
  - **Owner of the remaining v0.3 rules:** the tape cap and the blow-up cap of v0.3's
    `ShapeAdmissible` belong to `Compile`'s proof format.
  - **Cross-stage note:** the caps now live in `Protocol`, and Stage 4 and Stage 7 rely on
    `2^(k+8)` for the index.
- **S1-A10 (S1-m5: textbook R1CS; §2.3, S1-A3).**
  - **§2.3 and S1-A3:** R1CS is `z = (1, x, w)` with the constant wire. The `1` is the view's
    constant cell (S1-A11), `x` the public row's cells `0…31`, and `w` the remaining columns.
  - **§2.3:** `R1CS_iff_layout` is stated for `relK k`: one chip, one row, no ports, `pub = 0`,
    admissible for `≤ 2^8` constraints, `≤ 2^10` columns and `3·m·(32+n+1) ≤ 2^(k+4)` entries.
  - **S1-A3:** the earlier "`z = (x, w)`" wording dropped the constant wire, so every instance was
    homogeneous; S1-A10 replaces it.
- **S1-A11 (S1-m7, option (iii): contract cells in the view; §2.1).**
  - **§2.1:** the gadget's view has width `cols + cols + 3`. It holds the row, the next row (row 0
    after the last), then `1`, `[r = 0]` and `[r + 1 = rows]`, and `Chip.gadget : Gadget K (cols + cols + 3)`.
    A verifier computes these cells from the height.
  - **§2.1, documented:** (a) a port's selector is a witness cell compared with `1`, and any other
    value is silent, so a protocol that weights messages by the selector must have the layout
    constrain it to `0`/`1`; (b) fixed row patterns come from the flags or from a fixed table;
    (c) heights are arbitrary (not powers of two), and the wrap is modulo the height.
  - **§2.1 AIR sentence:** "an AIR with boundary constraints on the first or last row (the flags)
    and a transition on every row is one chip, many rows, no ports".
- **S1-A12 (S1-m8b, S1-m8c: cross-stage notes).**
  - **(b) compile stage (Stage 3 in the orchestrator's numbering; design §11 step 4).** Every
    `Protocol k` has `k ≥ 20` (S1-A2) and fixed shapes within S1-A9. A protocol that sends the
    witness (the toy, `P_triv`) therefore sends oracles of `2^(k+8)` to `2^(k+10)` elements, which
    the kernel cannot evaluate. The planned controls "honest compiled toy accepted" and "two-leaf
    node with the toy protocol" need either a small, non-`Secure` `Protocol 20` with tiny shapes
    (`Secure` is not required of a compile control) or general theorems. Say so in §11.
  - **(c) recursion stage (Stage 5; design §5.3).** S1-A6 enforces the cell bound of `C_V` through
    `complete`. That clause is vacuous if `aggOK cfg P` is never true, and compile completeness is
    not a theorem in the design. The benchmark run is what catches it (a node step must produce a
    verifying proof). Record this in §5.3.
- **S1-A13 (S1-m1 to S1-m4: controls; §2.3, §10).**
  - **§2.3:** add the controls for the cyclic wrap (`wrap_pos`/`wrap_neg`), `eq`-bus multiplicity
    (`eqMult_neg`), the fixed-table height (`fixedHeight_neg`), a boundary control for every cap,
    and Fibonacci pinned by the flags (`fib_garbage`, `fib_boundary_neg`).
  - **§10:** `Library/RbrSound.lean`, `Controls/Hit.lean` and `Controls/FieldSpec.lean` are carried
    over verbatim; `hit_secure` is the positive control with challenge rounds. `Library/Transfer.lean`
    is not carried over, because it imports the deleted `Accumulation.lean`; it should be dropped
    from the §10 keep list.

## Stage 3 (compiled argument, 2026-10-14)

The implemented reference is `RecursionFast/Contract/Compile.lean`; its module header holds the
byte grammar. These items change or complete DESIGN §3.2 (and §5.1, §6.5, §11).

- **S3-A1 (plain oracles; §3.2).** A prover oracle with a single leaf (`logLeaf = logLen`) is
  sent **in the clear**: its `8·2^logLen` bytes go in the rounds section in place of a root, they
  are absorbed, and a query of it reads them (no opening). Every other prover oracle, and the index
  oracle always, is Merkle-committed.
  - **Why.** A query of a one-leaf oracle opens the whole oracle anyway. Committing it costs a
    root (32 bytes), its absorption, and a leaf hash per query; sending it in the clear costs
    none of these. This is where small messages (sumcheck polynomials, a FRI final layer) go.
  - **§3.2 draft:** "a prover oracle with one leaf is sent in the clear and absorbed; any other is
    Merkle-committed".
- **S3-A2 (Merkle hashing; §3.2).** A leaf's digest is `H(leaf bytes)`. A node's digest is
  `H(child_0 ‖ … ‖ child_{A-1})`. Leaves are padded with the zero digest (32 zero bytes) to `A^depth`,
  where `depth` is the least `d` with `2^(logLen - logLeaf) ≤ A^d`. There is **no leaf/node tag**.
  - **Why no tag.** The depth is fixed by the shape, so a path has a known length, and binding at
    a fixed depth reduces to collision resistance. Tree inputs have length `0 mod 8`, and sponge
    inputs have length `1 mod 8` (they carry a tag byte), so the two are separated by length.
  - **Cost of a tag.** A one-byte tag would add one compression to every leaf whose size is a
    multiple of 64 bytes (every leaf of ≥ 8 elements). That doubles leaf hashing at 8 elements.
  - **Deviation:** this departs from the instruction "leaves hashed with domain separation".
- **S3-A3 (Fiat–Shamir; §3.2, §5.1).** The sponge is a hash chain. Its state is a digest.
  - **Start.** `s₀ = H(VKc bytes)`, which is the key digest `D` of §5.1. Then `x` (256 bytes) is
    absorbed.
  - **Absorb and squeeze.** Absorbing `m` sets `s ← H(0x00 ‖ s ‖ m)`. Squeezing `b` bytes runs
    `⌈b/32⌉` ratchet steps `s ← H(0x01 ‖ s)` and outputs the successive states, truncated to `b`.
  - **Rounds.** A prover round absorbs its root or its plain elements. A challenge round
    `chal nE idx` squeezes `24·nE + 8·|idx|` bytes. `E` element `j` is bytes `24j … 24j+23` (limbs
    `c0, c1, c2`, little-endian). Index `j` is the little-endian word at `24·nE + 8j` reduced mod
    `2^b` (its low `b` bits). That is exactly uniform for `b ≤ 64`, so no rejection sampling is
    needed.
  - **Deviation from "absorbing `VK ‖ x` first".** The seed absorbs `D(VKc) ‖ x`. A recursion
    circuit `C_V` computes `D(vk)` anyway (to compare it with `d0`/`d1`), so it never re-absorbs a
    VK of up to 8 KiB. The native cost is the same: one compression per 64 VK bytes.
- **S3-A4 (`Cfg` menu and proof format; §3.2).**
  - **Fields.** `Cfg` has `hash : HashId` and `arity ∈ {2, 4, 8, 16}`, nothing else.
  - **Hash.** `HashId` has the single constructor `blake2s`. `sha256`, `keccak256` and `blake3`
    are added only with a Lean specification, and every menu hash must have 32-byte digests.
  - **Leaf packing** is the declared `OShape.logLeaf`, not a `Cfg` field.
  - **Query batching is off.** Every query consumes one opening, in query order, and a repeated
    query is opened again. A multi-opening format is a later organiser PR (it changes the
    grammar).
  - **§3.2 menu:** replace "hash ∈ {blake2s, sha256, keccak256, blake3}, …, leaf packing, query
    batching on/off" with "hash ∈ {blake2s} (grows with Lean specs), arity ∈ {2, 4, 8, 16}".
- **S3-A5 (the key and the tape; §3.2, §5.1, S2-A1).**
  - **Key.** `NARG cfg P : VKc P.vkLen → Stmt → Tape → Bool`, where
    `VKc vkLen = (Fin vkLen → K) × Digest` holds the protocol key and the index root. It is
    produced by `index cfg P L` (the organiser's indexer).
  - **`D` (updates S2-A1).** The key bytes are the VK elements (8 bytes each, little-endian) then
    the 32-byte root (`VKc.toBytes`), and `D` should hash these (the index root included).
    `K.bytes` and `K.ofBytes` (8-byte little-endian) now exist in `Compile.lean` for Stage 5.
  - **Tape.** `|tape| ≤ tapeCap = 2^20` is checked by `NARG`, and **leftover bytes reject**.
  - **Caps.** v0.3's blow-up cap (S1-A9) is not adopted. It priced prover work under the static
    cost model, and v2 measures prover time. The message size is already capped at `2^(k+10)`.
- **S3-A6 (the honest prover; §3.2, S1-A12(c)).** `prove cfg P L x w : Option Tape` is the
  honest compiled prover (a Lean specification). It returns `none` only if the verifier's run on
  the honest oracles leaves its range or the tape exceeds the cap.
  - **Completeness is now a theorem** (`Library/Compile.lean`): `narg_complete`,
    `narg_complete_of_secure` (a secure protocol's honest tapes are accepted on every instance of
    `relK k`, every `cfg`), and `prove_isSome` (there `prove` fails only by the cap). This closes
    the vacuity concern of S1-A12(c) for the compilation layer.
  - **§5.3:** say so.
- **S3-A7 (compile controls; §11 step 4, S1-A12(b)).**
  - **Protocol.** The controls use `cmpToy : Protocol 20` (not secure): a 4-leaf committed
    oracle, one challenge round (one `E` element, one 2-bit index), one plain element, and a
    2-leaf index oracle.
  - **Kernel cost.** About 15 BLAKE2s compressions for an honest run, about 35 s and 5 GB in the
    kernel.
  - **Reading "a flipped challenge".** The design's "a flipped bit in a challenge" becomes "a
    flipped bit in the root or the statement", since challenges are derived, not sent.

## Stage 4 (the bounded extractor, Q1; design §11 step 5)

- **S4-A1 (the extractor's serialisation is the contract's; §3.1, §4 item 3, O-1).**
  - **Why.** A submitter-supplied `WitMid` encoder or decoder is unbounded Lean computation on
    the extractor's path, so it voids the fuel bound. Example: an encoder that appends a
    brute-forced hash preimage to the tape, and an image that copies it to the output. Requiring
    `dec ∘ enc = id` does not help; nor does a size bound, since a preimage is a few words.
  - **Witness type.** `Security.lean`'s `WitMid` is fixed by the contract to
    `Mid n j := List (Fin.cases (Table K) (fun _ => Word) j)`. Before round 0 it is the witness
    tables (`eqIn := rfl`); after round 0 it is a list of words. A submitter's `KSF` reads structure
    into those words as it likes, and its laws are about the words. `Protocol` loses its `WitMid`
    field (see S4-A8).
  - **Input tape.** `extractorTape j (L, x) rounds w` is `frame [[j], L.words, x, round₀, …, w]`.
    `frame` writes a directory first: the section count, then the start and length of each
    section. `L.words` is `Library/Codec.lean`'s `eLayout` read as words (`Layout.words_eq`).
    `x` is 32 words. A message round is its elements; a challenge round is its tape words (v0.3's
    `Round.tapeWords`). `w` is the witness after round `j`. `extractMid m` runs on
    `⟦m, s, tr, w⟧`; `extractOut` runs on `⟦n, s, tr, []⟧`.
  - **Output.** Before round 0 the output is decoded by `decTables`, the inverse of
    `Table.words`; it reads a missing word as `0` and ignores leftover words. After round 0 the
    output is the witness itself.
  - **Size bound (O-1).** An output longer than `witCap k = 2^(k+12)` words is discarded. A
    class-`k` witness has at most `2^k` cells and `2^8` heights, and a message oracle at most
    `2^(k+10)` elements.
  - **Failure.** A fault, a trap, fuel exhaustion or an over-long output yields the empty witness
    `[]`. Before round 0, `[]` fails `relK` (an admissible layout has a chip, and `rel` needs one
    table per chip).
  - **§4 item 3 wording.** "`extractMid m s tr w := decMid L m (run img ⟦m, s, tr, w⟧ B(k))`, the
    empty witness on failure or on an output of more than `2^(k+12)` words; the serialisation of
    the tape and of `WitMid` is the contract's (`Contract/Extractor.lean`)."
- **S4-A2 (image cap; §3.3, §6.5).**
  - **Cap.** `ExtractorImage.img_le : img.byteSize ≤ imageCap = 2^20` bytes, v0.3's image cap.
  - **Why.** Without a cap, `img.data` could be a lazily defined table of `2^64` precomputed
    preimages: computable, and never evaluated by a symbolic proof.
  - **Stage 6/7.** The image must be the literal rendered from the claim (`unpack`, as v0.3), and
    the comparator must check `P.extractor.img = rendered`. Otherwise a data word could still be
    defined by an expensive Lean term. That only helps for fixed statements, but rendering
    removes it.
  - **§6.5.** Add the rows "extractor image `≤ 2^20` bytes" and "extractor output
    `≤ 2^(k+12)` words".
- **S4-A3 (memory map of the trimmed machine; §8, §10).**
  - **Map.** The address space is all `2^64` bytes. The input tape is read-only from
    `TAPE_BASE = 2^63` (word `i` at `2^63 + 8i`, for `i < 2^60`). Data memory is `[0, 2^63)`, with
    the image's data words from address 0. `sp = 2^63`.
  - **Why.** An extractor reads the whole transcript prefix: up to `2^14` rounds of `2^(k+10)`
    elements, about `2^52` words at `k = 28`. v0.3's 1 MiB tape and `2^36`-byte memory cannot hold
    it.
  - **Simplification.** With natural alignment, v0.3's `inMemory`/`writable` reduce to "a store
    lands below the tape".
  - **Input size.** There is no input-size check. Words beyond `2^60` are not addressable. This
    is only lossy: the KSF laws still have to hold.
- **S4-A4 (`HALT` returns words; §4 item 3).**
  - **Convention.** `ECALL` with `t0 = 0` and an 8-aligned `a0` halts. The output is the `a1`
    doublewords from `a0` (`readOut`); every other `t0` traps. There is no accept/reject: an
    image gives up by trapping.
  - **Why.** The output may point into the tape, so the toy's (and `P_triv`'s) extractor is an
    8-instruction image without a copy loop (`firstMsgImage`).
- **S4-A5 (the extractor sees `L`, not `VK L`/`IDX L`; §4 item 3).**
  - **Choice.** The statement section holds the layout itself (`Layout.words` with
    `Chip.words`, `Table.words` and `toWord`: 17 trusted code lines).
  - **Why.** `IDX` is submitter code and could carry precomputation keyed on `L`, and the
    knowledge claim is about `(L, x)`.
  - **Library.** `pLayout_words` proves that the section parses back to `L.normal 256` for an
    admissible layout of class `k ≤ 28`.
- **S4-A6 (`extractorFuel` is `@[irreducible]`).**
  - **Effect.** The attribute is for elaboration only; the kernel and `decide +kernel` still
    evaluate it.
  - **Why.** Without it, unifying an `extractMid` with `call` expanded `2^(2k+16)` and timed out.
  - **Library.** `extractorFuel_eq` unfolds it.
- **S4-A7 (finding, for the user; §4 item 3, Q1 rationale).**
  - **Fact.** For `k ≥ 24`, `B(k) = 2^(2k+16) ≥ 2^64` (`word_le_extractorFuel`). So a one-word
    (64-bit) secret can be enumerated within the fuel when the test costs at most `2^(2k-48)`
    steps per candidate (256 at `k = 28`). A two-word secret cannot, at any class in range
    (`extractorFuel_lt_two_words`).
  - **Q1 rationale wording.** "Excludes brute force ≈ `2^(64·n_w)`" holds for `n_w ≥ 2`, or for
    `k ≤ 23`.
  - **Benchmark.** The benchmark's hash-chain start is 256 bits, so nothing changes. A relation
    whose hardness rests on a single `K` element is not protected at `k ≥ 24`.
- **S4-A8 (the Protocol swap; §3.1). Prepared; to be applied after Stage 3.**
  - **Fields.** `Protocol` drops `WitMid` and changes `extractor` to `extractor : ExtractorImage`.
  - **Security.** `Secure := SecureWith (relK k) Set.univ P.prover P.specVerifier
    (P.extractor.toExtractor k P.shape) P.ε`.
  - **Toy.** The toy's extractor is `firstMsgImage`.
  - **Validated.** `probes/s4/ProtocolSwap.lean` proves `toy'_secure` for the swapped structure.

## Stage 3 fix pass (after the S3 review, 2026-10-14)

- **S3-A8 (S3-M1: one key digest; §5.1, supersedes S2-A1's `D`).** The key digest is the trusted
  definition `VKc.digest cfg vkc := cfg.hash.run vkc.toBytes`. It hashes the VK elements **and**
  the index root (8 bytes LE per element, then the 32-byte root). `seed` uses it.
  - **§5.1:** `D := VKc.digest cfg`. A leaf statement has `d0 = VKc.digest cfg (index cfg P C_V)`
    and `d1 = VKc.digest cfg (index cfg P L_chain)`.
  - **Stage 5** reuses this function and never restates it. S2-A1's `D` over the VK elements
    alone would let a node witness choose its own index root.
  - **Control:** `digest_kat` pins it to `hashlib.blake2s(vk ‖ root)`.
- **S3-A9 (S3-m4: the key's root).** `NARG` rejects a key whose index root is not 32 bytes. This is
  one conjunct; the type `VKc` is unchanged.
- **S3-A10 (S3-m5: trusted base).** The honest compiled prover moves to `Library/Compile.lean`,
  because no trusted statement uses it. The moved definitions are `Round.tapeBytes`, `fsPrefixes`,
  `fsTranscript`, `pathOf`, `record` and `prove`. `Contract/Compile.lean` drops from 159 to 128
  code lines.
- **S3-A11 (S3-m1: the reason for S3-A2).** "No leaf/node tag" stands, with the corrected reason.
  - Binding at a fixed depth reduces to collision resistance, because the depth and every
    level's input lengths are fixed by the shape.
  - Absorb and squeeze inputs have length `1 mod 8`, and tree inputs `0 mod 8`.
  - The key digest `D` is in the tree's length domain. This is harmless because the indexer fixes
    its input.
- **S3-A12 (S3-m3, S3-m9: the grammar, as the header now states it).** The header alone suffices
  for an encoder; `probes/s3/indep_encoder.py` still matches byte for byte at arity 2, 4, 8 and 16.
  It now states:
  - the key bytes;
  - that every internal node is hashed from its children, including one whose children are all
    padding (`H(0^(32A))` at height 1);
  - that the children of node `p` are `A·p … A·p + A − 1`;
  - that the index tree uses the same `cfg`;
  - that an out-of-range query rejects.

  Two executed-cost changes leave the bytes unchanged:
  - `Cfg.depth` is the closed form `⌈(logLen − logLeaf) / log₂ A⌉` (`Cfg.logArity`).
    `depth_spec` proves it is the least `d` with `2^(logLen − logLeaf) ≤ A^d`.
  - Challenges are decoded from the squeezed bytes read as `K` elements, once per round
    (`Round.decodeK`). `chals` takes those arrays, and the byte offsets are unchanged.
- **S3-A13 (S3-m8: conditions and owners).** S3-A6 now reads: completeness closes S1-A12(c)
  **provided the honest tapes fit `tapeCap`** (`prove_isSome`: otherwise `prove` is `none`).
  §6.5's 128 KiB cap for board L is not part of `NARG`; it is assigned to Stage 7 (harness or
  certificate).
- **S3-A14 (S3-M2, S3-m2, S3-m6: controls and the Stage 5 interface; §11 step 4).**
  - **New controls:**
    - `pfs_honest` and `pfs_cheat`: a plain message before a challenge;
    - `decode_kat`: the challenge byte offsets;
    - `idx_path_flip`: index authentication;
    - `oob_rejected`: the range check;
    - `toy_local`: `narg_local` is not vacuous.
  - Each kills a one-line mutant that survived the previous suite (`probes/s3/RevMutants.lean`).
  - `Library/Compile.lean` adds `NARG_eq_true_iff`, the unfolded acceptance condition that a
    recursion circuit `C_V` must force (§5.3).

## Stage 4 fix pass (after the S4 review, 2026-10-14)

- **S4-A9 (S4-M1: `B(k)` is the total over the composed extractor; §4 item 3, §6.5, Q1).
  Supersedes S4-A7.**
  - **Change (trusted, `Contract/Extractor.lean`).** `extractorFuel k n := 2^(2k+16) / (n + 1)`.
    Each of the `n + 1` calls of the round-by-round extractor of an `n`-round protocol gets that
    many steps. `toExtractor` takes `n` from the shape, and `call` runs with
    `extractorFuel k n`.
  - **Why.** Knowledge comes from the composed extractor (`Library/RbrSound.lean`'s `chain`).
    Its calls may pass state through the witness words: `resumeImage`, `chain_round0`. Rounds
    are free (`padShape`: empty challenge rounds). So under the per-call reading a one-word
    secret was enumerable at every class: `chain_secure` in `probes/s4/ChainBudget.lean`, with
    `2^10` rounds at class 20.
  - **Total.** The whole extraction now has at most `B(k)` steps (`composed_fuel_le`), and
    adding rounds buys nothing.
  - **Per call, within the round cap.** A call has at least `2^(2k+1)` steps
    (`pow_le_extractorFuel`).
  - **Negative control.** `chain_search_fails` (`Controls/Extractor.lean`): a chained search
    whose calls each test at most as many candidates as a call has steps is not an extractor at
    class 20. This holds for any injective `f`, any prover and errors, on any number of padding
    rounds.
  - **Restated thresholds (S4-m2).**
    - A one-element secret is enumerable only if `2^(2k+16) ≥ 2^64 · c`, where `c` is the steps
      per candidate including loop control.
    - That never happens for `k ≤ 23` (`composed_lt_word`).
    - At `k = 24`, `c = 1`, which no loop achieves: `B(24) < 2·2^64` (`budget_24_25`).
    - At `k = 25`, `c ≤ 4`. So in practice the boundary is `k ≥ 25` for cheap tests (`k ≥ 26` for
      any non-trivial test).
    - Two elements are never enumerable: `2^72 < 2^128` (`composed_lt_two_words`).
  - **DESIGN §4 item 3 paragraph.**

    > Each extractor call runs the submitted image (≤ `2^20` bytes, the same for every
    > statement) on a tape the contract builds from `(j, L, x, transcript prefix, next
    > witness)` alone. A protocol of `n` rounds has `n + 1` calls, each of
    > `B(k)/(n+1)` steps, `B(k) = 2^(2k+16)`, so the whole extraction (`Library/RbrSound.lean`'s
    > `chain`) runs for at most `B(k)` steps whatever `n`, even though calls may pass state
    > through the witness words. The output (≤ `2^(k+12)` words, else empty) is decoded by
    > trusted code that adds only zeros. The laws force a valid witness only before round 0,
    > where `[]` fails `relK`. Brute force is excluded for witnesses of two or more `K` elements
    > at every class, and for one `K` element up to `k = 23` (at `k ≥ 24` only if a candidate
    > costs at most `2^(2k−48)` steps, loop control included).

  - **Cost to honest submitters.** A protocol with many rounds gets less per call: down to about
    `2^(2k+1)` steps at the round cap. Extraction work concentrated in one round has to fit
    `B(k)/(n+1)`.
- **S4-A10 (S4-M2: what `B(k)` admits; §4 item 3, Q1 rationale). Keeps the user's value of
  `B(k)`.**
  - **Docstring.** The `extractorFuel` docstring no longer claims "quadratic in the oracle
    length" or "Gaussian elimination". It states:
    - `B(k)` is `2^16` times the square of the witness-cell cap. The longest admissible oracle
      squared is `16·B(k)` (`oracle_sq`).
    - Cubic elimination on `2^k` unknowns exceeds `B(k)` from `k = 17` (`cube_gt`).
    - At about 10 steps per `K` multiply-add, the whole budget admits O(N²) decoding up to about
      `2^(k+6)` elements (`quadratic_fits`), and quasi-linear decoding of every admissible
      oracle.
  - **DISCUSSION Q1.** Its "Quadratic admits Berlekamp–Welch via Gaussian elimination" is to be
    corrected when DESIGN §4 is patched.
  - **Request to the orchestrator.** Add to DESIGN §12: "**O-11** (user / library): measure
    whether CompPoly's Guruswami–Sudan decoder (the Johnson-regime decoder Q1 relies on) fits
    `B(k)` at the benchmark's oracle sizes, at `k = 20`, against `B(20) = 2^56` steps over the
    whole extraction."
- **S4-A11 (S4-m3: one comment-only edit to a carried-over trusted file).**
  - **What.** `Contract/Security.lean`'s header loses the sentence "At L1 the extractor is
    unconstrained … labelled 'RBR-sound'". It is replaced by "For an unconstrained extractor
    `RbrKS` is equivalent to RBR *soundness* (`Library/RbrSound.lean`, A2-M2);
    `Protocol.Secure` names the submitted image (`Contract/Extractor.lean`, Q1), to which the
    collapse does not apply."
  - **What does not change.** No declaration changes, and the line count of code is unchanged.
    The diff is quoted in `docs/stages/S4-RESULT.md`, "Fix pass".
- **S4-A12 (wording; S4-m4, S4-m5, S4-m6).**
  - **(m4) `Contract/Extractor.lean` header.** "The laws force a witness in `relK` only before
    round 0, where `[]` fails (`nil_not_relK`); after round 0 the submitter's state function says
    what an output must satisfy, `[]` included." This replaces "the image must succeed within
    the fuel exactly where the laws ask".
  - **(m5) `witCap` is an interface cap, not a security bound.** It is "the largest intermediate
    witness an extraction passes between calls": four maximum-size oracles. The fuel already
    bounds what an output can contain. Use this wording in S4-A1 and in DESIGN §6.5.
  - **(m6) DESIGN §4 item 3 and Q1.** Say "steps", not "cycles": `B(k) = 2^(2k+16)` steps.
    Every instruction is one step (`div`, `clmul` and `ECALL` included), and there is no cost
    model.
- **S4-A13 (S4-A8 applied: the Protocol swap; §3.1).**
  - **`Contract/Protocol.lean`.** The `WitMid` field is gone and the field is
    `extractor : ExtractorImage`. `Secure` uses `P.extractor.toExtractor k P.shape`, with `k`
    the structure's class and `n` its round count, so the fuel is `extractorFuel k P.n`.
  - **Controls migrated.** `Controls/Toy.lean` uses `firstMsgImage`, `toy_extractMid` and a
    `Fin.cases` state function. `Controls/CompileToy.lean` and `Controls/CompileFS.lean` use
    `firstMsgImage`; these protocols are not claimed secure.
  - **Negative control.** `toy_not_secure_of` and `toy_spin_not_secure` (`Controls/Toy.lean`):
    with the looping image the toy is not secure at any class in range. `nil_not_relK` is in
    `Library/Extractor.lean`.
  - **Probe removed.** `probes/s4/ProtocolSwap.lean` is deleted.
  - **§3.1 block.** Replace the `WitMid`/`extractor` lines by `extractor : ExtractorImage`, and
    `Secure` by `SecureWith … (P.extractor.toExtractor k P.shape) P.ε`.

## Stage 6a (the benchmark layout `L_chain`, O-3; design §7.1–§7.2)

The implemented reference is `harness/gen-chain-layout.py`. Its arithmetisation is
`harness/CHAIN-LAYOUT.md`, and the measurements are `docs/stages/S6a-RESULT.md`.

- **S6-A1 (O-3: the class of the benchmark; §2.2, §6.3, §7.2, §12).**
  - **Measured.** `L_chain(n)` has `9,225·n + 786,505` cells. The fixed `add8` table is 786,464
    fixed cells, above `2^19`, so the fixed-table cap `2^(k−4)` forces `k ≥ 24` for every `n`.

    | n | cells | `k_min` |
    |---|---|---|
    | 2^8 | 3.1 M | 24 |
    | 2^10 | 10.2 M | 24 |
    | 2^11 | 19.7 M | 25 |
    | 2^12 | 38.6 M | 26 |

    The largest chain at class 24 is n = 1,733.
  - **`n = 2^12` does not fit class 24.**
    - Class 24 would need at most about 3,904 cells per compression (about 49 per G-call). The 24
      add lookups of one G-call already produce 24 result bytes and 18 carries.
    - Class 25 would need at most about 7,999 (13 % below this layout).
  - **§2.2 wording.** "The range itself comes from the leaf benchmark, which fits at `k ≥ 24`"
    stays true as "every `L_chain(n)` needs `k ≥ 24`; `n = 2^10` fits 24".
  - **§6.3 / §7.2 (for the user).** Choose one:
    - keep `n ∈ {2^8, 2^10, 2^12}` and run the `2^12` leaves at class 26, which `k_range` (20–28)
      already allows; or
    - change the leaf sizes to `{2^8, 2^10, 2^11}`, at classes 24, 24 and 25.

    The recursion tree's `n = 2^10` fits class 24.
  - **§12 O-3.** Resolved: `k_min = 24`, by the table; cells per `n` as above.
- **S6-A2 (the arithmetisation; §7.2 wording).**
  - **§7.2.** Replace "a Blake2s chip (one row per compression round or per G-function), an 8-bit
    limb table chip …, a chain chip …" with the following.
    - **Chips.** A G chip with two rows per G-call (one half of `G` per row; 53 columns). A fixed
      `add8` table of `2^17` rows (8-bit add with carry) and a 16-row nibble table. Twenty state
      chips `S0 … S19`, one row per compression, holding the state before each half-round and the
      message words. A `FINAL` chip (finalisation and chain link) and the public chip.
    - **Buses.** Four `sub` buses: `ADD`, `ADDTOP`, `PAIR`, `NIB`. Four `eq` buses: G inputs,
      G outputs, message words, output.
  - **Why two rows per G-call.** One G needs 24 byte lookups. The port cap (`≤ 2^4` per chip, §2.2)
    makes one row per G-call or per round inadmissible; a row of one half-G uses 15 ports.
  - **XOR** is field addition.
  - **Additions** are bytewise lookups into `add8`. Byte 3 uses a second port of the same table
    without the carry-out, so the discarded carry is not a cell.
  - **Rotations.** `rotr 16` and `rotr 8` permute bytes. `rotr 12` and `rotr 7` cost one wrap cell
    each (`(1 + X^32)·W`, `W` range-checked as a nibble); this is sound because every packed word
    is later decomposed into range-checked bytes.
  - **The gadget form** of every chip is `gate · linear = 0`: CCS with `t = 2`, `q = 1`, degree 2.
    The gates are the view's constant and flags, and the G chip's phase cell.
- **S6-A3 (statement and boundary conventions; §5.1, §7.1).**
  - **The statement** is `x = (y₀, y₁, y₂, y₃, n, 0, …, 0)`, where `y_j` is digest bytes
    `8j … 8j+7`, little-endian (S2-A1). The public chip constrains all 32 cells, so a statement
    with another `n` or a nonzero tail has no witness.
  - **The start** `s` is the free message of `S0`'s row 0.
  - **The digest words `H₄ … H₇`** are range-checked in `FINAL` (byte pairs on `PAIR`). Otherwise a
    wrong `rot 7` wrap bit in the last compression would alias across the 64-bit limb packing of `y`.
- **S6-A4 (routing by tags; §2.1 usage, no contract change).**
  - **Tags.** `eq`-bus messages carry tags `γ^r` with `γ = X`, a generator of `K*` (order
    `2^64 − 1`). Row `r` of the G chip has tag `γ^r`; the state chips use
    `κ = γ^{160i + 8(s−1)}`.
  - **Pins.** Every tag chain is pinned at its first row (`[r = 0]`) and its last row
    (`[r + 1 = rows]`). This fixes every height, so a prover cannot add, drop or reorder
    compressions.
  - **Uniqueness.** The witness is unique given `s`. No sampled single-cell change survives.
- **S6-A5 (fidelity: tested, and kernel-checked on one G-call; §7.2).**
  - **What the kernel can do.** `decide +kernel` costs about 40 ms per `K` product, about 10 s per
    G row. A compression is 160 G rows (about 27 min), so the kernel control is the one-G-call
    harness (`Controls/Chain.lean`).
    - `rel` is decided for G-calls 0 and 79 (add table trimmed to the rows used).
    - `rel` is proved with the full `add8` table (lookups certified row by row).
    - The statement agrees with the contract's `Blake2s.mix`.
    - There are three negative controls.
    - `L_chain(1024)` is admissible at 24 and not at 23.
  - **What Python does.** The independent evaluator `harness/check-chain.py` covers whole chains
    (n = 4, 16, 256) against `hashlib`, with single-cell mutations and one layout mutant per
    mechanism.
  - **§7.2 wording.** "Fidelity is tested, not proved" stays. Add "the kernel checks one G-call of
    the generated layout; the Python evaluator, cross-checked against the kernel on the same
    instances, checks whole chains".
- **S6-A6 (JSON format and rendering; §7.2, Stage 7).**
  - **The format** is the JSON layout/witness/statement schema of `harness/README.md`, with K
    elements as 16 hex digits and the closed-form table kind `add8`.
  - **The renderer** is `harness/render-layout.py`.
  - **Deviation.** The design says "rendered into Lean by the v0.3 renderer". The v0.3
    `scripts/render-challenge.py` is unchanged; adding a `{{layout:KEY}}` placeholder that calls
    `render-layout.py` is left to Stage 7, together with the challenge stub for the leaf board.
- **S4-A14 (submitter-declared split of `B(k)`; supersedes the even split of S4-A9's "Change"
  bullet; S4-A9's thresholds are unchanged because the total is unchanged).**
  - **Change (trusted, `Contract/Extractor.lean`).** `extractorFuel` is removed and
    `extractorBudget k := 2^(2k+16)` is `B(k)`. `ExtractorImage k n` gets the fields
    `fuel : Fin (n + 1) → ℕ` and `fuel_le : (List.ofFn fuel).sum ≤ extractorBudget k`.
    `toExtractor` runs `extractMid m` with `fuel m.castSucc` and `extractOut` with
    `fuel (Fin.last n)`: each call is indexed by the round before which its witness lives.
  - **Wording.** "The submitter chooses how the total budget `B(k)` is split over the `n + 1`
    calls (a round-0 decoder may take almost all of it); the total, not the split, is what the
    contract bounds."
  - **Protocol.** The field is `extractor : ExtractorImage k n`, and `Secure` uses
    `P.extractor.toExtractor P.shape`.
  - **Library.** `ExtractorImage.composed_fuel_le` (it is `fuel_le`) and `fuel_le_budget`.
    Two ready-made splits: `even` (`B(k)/(n+1)` each; `even_fuel_ge`: at least `2^(2k+1)`
    within the round cap) and `atZero` (all of it on the call before round 0).
    `firstMsgImage k n := atZero firstMsgImg …`.
  - **Controls.**
    - The toy, `cmpToy` and `pfs` use `firstMsgImage` (all on round 0).
    - `brute_extractMid_nil` and `spin_extractMid` hold for any split.
    - `chain_search_fails` is stated for any image at class 20 (any split) and a chained search
      testing at most `c < 256` candidates per step of each call's fuel, so bit-slicing is
      covered. It covers at most `255·2^56 < 2^64 − 1` candidates; reaching `2^64` would take
      256 per step.

## Stage 5 (recursion and certificates; design §5, §3.3, §11 step 6)

The implemented reference is `RecursionFast/Contract/Recursion.lean` and
`RecursionFast/Contract/Certificate.lean`; the measurements are `docs/stages/S5-RESULT.md`.

- **S5-A1 (bounded node witnesses; §5.2).** `aggOK` also requires both keys' index roots to be
  32 bytes (`nw.vkC.2.length = 32 ∧ nw.vkL.2.length = 32`), the check `NARG` makes on the key it
  uses (S3-A9).
  - **Why.** In a node whose children are both leaves, `vkC` is constrained only by its digest
    `d0`. A key's root is a `List UInt8` of any length, so `complete` would ask `C_V` to decode,
    from a witness of at most `2^k` cells, every `vkC` whose digest is `d0`, including arbitrarily
    long preimages: an unsatisfiable obligation. With the check, every part of an accepted node is
    bounded: keys (`vkLen ≤ 2^10` elements and 32 bytes), statements (32 elements), tapes (`≤ tapeCap`,
    by `NARG`), tags.
  - **§5.2 draft.** Add "both keys' index roots are 32 bytes" to `aggOK`'s conjuncts.
- **S5-A2 (finding, for the user: a vacuous recursion-board submission; §5.3, S1-A12(c), S3-A13).**
  - **Fact.** `Controls/Certificate.lean`, `vacuous_certificate`. The toy protocol (`toy_secure`)
    sends its message in the clear, `8·2^(k+10)` bytes, beyond `tapeCap`, so `NARG cfg2 (toy 20)`
    accepts no tape (`toy_narg`) and `aggOK` no node (`toy_aggOK`). Then `complete` is vacuous;
    with the unsatisfiable layout `unsat` so is `sound`. The result is a `RecursionEntry`, a
    `SubmissionR` and a `CertificateR` (one chip, zero entries) with no node that can be proved.
  - **Reading.** This is S1-A12(c)'s residual case: compile completeness (`narg_complete_of_secure`)
    holds only when the honest tapes fit the cap (S3-A13). The Lean certificate therefore does not
    show that a node can be proved, nor that `C_V` fits class `k` for any node; the benchmark run
    does (a node step must produce a verifying proof, §6.3), and such a submission is rejected
    there.
  - **Option (for the orchestrator/user).** Add a field `live : ∃ x' nw, aggOK cfg P x' nw = true`
    to `RecursionEntry`. A real submitter proves it with `aggOK_sat_of_secure`
    (`Library/Recursion.lean`) from one instance of `relK k` (any small layout), its honest tapes,
    and a theorem that they fit `tapeCap` (a size bound on its own proof format); no kernel
    evaluation is needed. Then `complete` makes "`C_V` fits class `k`" non-vacuous for every
    certified entry. Not applied: the design accepts the benchmark as the backstop (§5.3).
- **S5-A3 (the certificate; §3.3).**
  - **Split by board.** `Submission k := {P, cfg, secure}` (board L) and
    `SubmissionR k extends Submission k` with `entry : RecursionEntry P cfg` (board R; the field
    is `entry`, not `rec`, which would clash with the recursor `SubmissionR.rec`). `Declared`
    (`k`, hash, arity) and `DeclaredR` (also the chip count and matrix-entry count of `C_V`, and the
    two key digests); `Certificate D S` (the configuration is the declared one) and
    `CertificateR D S` (also the size of `C_V`). The class is pinned by the type `Submission D.k`.
  - **Cells of `C_V` are not declared.** They depend on the witness and are bounded through
    `complete` (S1-A6). The declared size is static: chips and matrix entries, certified by
    evaluation.
  - **The key digests are declared, not certified.** `D (index cfg P C_V)` commits the index
    oracle, up to `2^(k+8)` elements: beyond the kernel except for toys (`cmpToy`'s 2-leaf index
    costs about 3 hashes). The harness computes both digests with the compiled indexer (§6.3
    step 2, untimed), compares them with the declared ones, and uses them in `rootOK`.
  - **§3.3 table, last row.** "claim JSON (`k`, `cfg` = hash and arity, chips and matrix entries
    of `C_V`, the key digests of `C_V` and `L_chain`)".
  - **Gate (Stage 6b).** The `--computable` table gains `Submission: [P]` (hence `VK`, `IDX`,
    `verify`, `extractor`) and `RecursionEntry: [decode]`.
- **S5-A4 (the statement format; §5.1, §5.2).**
  - **The aggregate statement is a trusted function** `nodeStmt cfg vkC vkL x₁ x₂ =
    ofSlots [D vkC, D vkL, blake2s256 (x₁ ‖ x₂), 0, 0, 0, 0, 0]` (slots as `digestToSlot`), and
    `aggOK` is "`x' = nodeStmt …`, 32-byte roots, both children accepted". The harness recomputes
    the statement tree (§6.3 step 5) with `nodeStmt` and the indexer's keys; such a tree passes
    `rootOK` (`rootOK_nodeStmt`).
  - **`d3 … d7 = 0`** is part of the statement (decided): a node statement carries no free bits
    (`nonzero_d3`).
  - **`d2` uses `blake2s256` for every `cfg`**, as §5.1 says, not `cfg.hash.run`. The two agree
    today (`HashId` has one constructor). When the menu grows, decide whether `d2` follows
    `cfg.hash`, so that a `C_V` needs one hash gadget.
  - **Tags are not hashed into `d2`.** The organiser fixes the tree shape and recomputes the
    statements, so a tag is determined by the position. A leaf statement presented as a node
    child must have `d0`, `d1` equal to the key digests (`node_child_d0`, `node_child_d1`); a node
    statement presented as a leaf child must satisfy `L_chain`'s public chip (S6-A3: `x₄ = n`,
    `x₅ … x₃₁ = 0`), while its `d1` holds the four limbs of a digest.
- **S5-A5 (the root check; §5.1).** `rootOK cfg P C L x` checks `d0`, `d1` against the indexer's
  keys for `C` and `L` (`index cfg P C`, trusted, `Compile.lean`). With `aggOK` it pins the node's
  keys (`keys_of_root`: their digests are the indexer's, by `digestToSlot_inj` on 32-byte
  digests).
- **S5-A6 (controls; §11 step 6, S1-A12(b)).** As prescribed, on `cmpToy : Protocol 20` (not
  secure, tiny shapes). There is no positive `RecursionEntry` (§7.3). `aggOK` is shown
  satisfiable directly (`aggOK_two_leaves`, `aggOK_node_child`) and through compile completeness
  (`toy_sat_via_complete`, from `aggOK_sat_of_complete`). The general `aggOK_sat_of_secure` has no
  instance in the repository: the only `Protocol` proved secure, the toy, has tapes beyond the
  cap.
  §11 step 6's "a layout that ignores `π₂` cannot satisfy `sound`" is `cbad_not_sound`.

## Stage 5 decision pass (orchestrator, 2026-10-15)

- **S5-A7 (S5-A2 resolved: `RecursionEntry.live`; §5.3).** `RecursionEntry` gets the field
  `live : ∃ x' nw, aggOK cfg P x' nw = true`: the compiled argument accepts at least one node.
  Without it `complete` is vacuous for a protocol whose proofs exceed the tape cap. A submitter
  proves it with `aggOK_sat_of_secure` (`Library/Recursion.lean`) plus a bound on its own proof
  size.
  - **Negative control.** `toy_no_entry` (`Controls/Certificate.lean`): the toy, secure but with
    tapes beyond the cap, has no recursion entry for any layout and decoder; `toy_vacuous_fields`
    shows that every other field would hold with `unsat`. `toy_no_submissionR`: no `SubmissionR`
    is built on it. The former `vacuous_certificate` is gone.
  - **Positive evidence.** No positive `RecursionEntry` exists (§7.3). `live` holds for `cmpToy`
    (`toy_aggOK_sat`), and `aggOK_sat_of_secure` is the general route.
  - **§5.3 draft.** Add the field and its docstring; replace "That clause is vacuous if `aggOK cfg P`
    is never true … The benchmark run is what catches it" by "`live` keeps `complete` (and with it
    the cell bound) from being vacuous".
- **S5-A8 (supersedes S5-A4's third bullet; §5.1).** `d2 = digestToSlot (cfg.hash.run (x₁ ‖ x₂))`,
  the same function as `D` and the sponge, so a recursion circuit needs exactly one hash gadget;
  the organiser recomputes the statement tree with `cfg.hash`. With the one-element menu
  (`HashId.blake2s`) nothing changes numerically: the kernel KATs (`nodeStmt_kat`,
  `nodeStmt_kat_R`) and `probes/s5/recursion_ref.py`'s output are unchanged.
  - **§5.1 table.** The node row's `d2` becomes `H(x₁ ‖ x₂)`, `H = cfg.hash`.
- **S5-A9 (for Stage 6b, the harness; §7.4).** The gate's `--computable` table must include
  `Submission.P` (hence its `VK`, `IDX`, `verify` and `extractor`) and `RecursionEntry.decode`
  (replacing v0.3's `Submission0/1/2` rows). The renderer pins `DeclaredR`; `digestC`/`digestL`
  are compared by the harness with the compiled indexer (S5-A3), not proved.

## Stage 6a fix pass (after the S6a review, 2026-10-15)

- **S6-A7 (advice, not a change; S6a review): 4-bit limbs.** Keep the 8-bit `add8` table and the
  S6-A1 sizes: `n ∈ {2^8, 2^10}` at class 24, `2^12` optional at class 26.
  - **The floor for byte lookups.** Any arithmetisation whose additions are table lookups needs at
    least 58 cells per G-call: `6 × (4 result bytes + 3 carries) = 42`, plus 16 operand bytes.
    With nibbles the floor is `6 × 15 = 90`. Class 24 at `n = 2^12` leaves about 49 cells per
    G-call, so no byte-or-narrower table fits it.
  - **What 4-bit limbs would do.** The add table shrinks to `2^9` rows, and the fixed-cell floor
    from `k = 24` to 16. But each half-G needs 24 lookups, so 4 rows per G-call, and about 16.4 k
    cells per compression against 9,225.

    | n | now | with 4-bit limbs |
    |---|---|---|
    | 2^8 | 24 | 23 |
    | 2^10 | 24 | 25 |
    | 2^12 | 26 | 27 |

    It helps only the smallest leaf.
- **S6-A8 (S6a-M1; replaces S6-A5's description of the kernel control; §7.2 wording).**
  - **The harness now checks its outputs.** Its public chip `PUBG` decomposes the four output words
    into bytes checked on `PAIR`, as `FINAL` does in `L_chain`.
  - **Why.** Without this, `PUBG` accepted `b' ⊕ (1 + X^32)·e` through a wrong rot-7 wrap nibble
    (the review's `A6_rel_not_mix`, which no longer holds).
  - **What the kernel control is.**
    - Completeness of the one-G-call harness on two calls of the chain, one of them with the full
      `add8` table.
    - Named single-cell faults, each rejected by the clause it names: gadget `in_A`, the add
      lookups, `GOUT`.
    - The wrap attack, rejected only by `PAIR` (`LG0_neg_wrap`, `LG0_wrap_rest`).
    - `G_link`: the harness's G chip is `L_chain`'s except for the last-row pin's constant.
    - The admissibility of `L_chain(16)`.
  - **What it is not.** It does **not** prove that the harness computes `G` (`rel → MixStmt`).
  - **§7.2 sentence.** "The kernel checks completeness of one G-call of the generated G chip and
    named faults; soundness is tested by the Python evaluator on whole chains, where the next
    decomposition range-checks every output, with one layout mutant per mechanism."
- **S6-A9 (S6a-m4; §6.3 item 1).** The chain's secret start is never a command-line argument.
  - **Input.** The generator reads it from a file or from stdin (`--secret-file F` / `-`), and the
    experiments pass it on stdin.
  - **Witness files are secret material.** A witness file holds `s` in row 0 of `S0`. Stage 7
    places such files, like the secrets, outside the verifier's sandbox.
- **S6-A10 (S6a-m2; §7.2 "a mutated layout must admit a wrong witness").** The mutant suite has
  one mutant per load-bearing mechanism, eight in all: `gate`, `addport`, `nibport`, `gouttag`,
  `fixed`, `nolast`, `selpin`, `pairport`. The three added in the fix pass:
  - **`nolast`.** The last-row pins of every tag counter fix the heights. Without them, the
    `(n−1)`-chain is accepted for `n`.
  - **`selpin`.** The `0/1` pins of the `MSG` selectors `nf` and `nl` keep the chain unbroken.
    Without them, the value `X` makes a port silent (S1-A11 (a)), and the chain restarts from a
    fresh `s'`.
  - **`pairport`.** `FINAL`'s byte check (S6-A3). Without it, a wrong wrap bit aliases into `y`.
- **S6-A11 (S6a-m5, m6: sources and schema).**
  - **The rendered `Lchain`** is `L_chain(16)` from `harness/examples/chain-n16.layout.json`,
    kept in the repository. `L_chain(n)` depends on `n` only through three constants: the
    last-row pins of the G chip, `S0 … S19` and `FINAL`, and `x₄ = n`.
  - **The witness schema has one reading.** `rows` equals the number of listed rows, and K strings
    are exactly 16 lowercase hex digits. Both the checker and the renderer enforce it.

## Stage 8 (Clean as the untrusted circuit frontend; design §9.3, §11 step 9)

Details and measurements are in `docs/stages/S8-RESULT.md`. Every item concerns the untrusted
library: nothing under `Contract/` changed.

- **S8-A1 (location and build; §9.3, §10, O-4).**
  - **Location.** The frontend lives in `RecursionFast/Clean/`, in the lean_lib
    `RecursionFastClean` (not a default target), not in `Library/Clean/`. This keeps Clean out
    of `RecursionFastLibrary` and out of the organiser package: `scripts/org-build.sh` drops the
    `Clean` require and the lib.
  - **Requirement.** Clean `42fe4b26` is required by path from the gitignored `ext/Clean`.
    `scripts/setup-clean.sh` fetches it (clone at the rev, or copy a checkout at the rev), and
    every fresh clone must run it before any root-level `lake` call.
  - **Cost.** The cone is 39 modules; `RecursionFastClean` builds in 3 min 34 s cold and 3.9 s
    warm. `import RecursionFast.Clean` takes 7.2 s and 3.2 GB.
- **S8-A2 (the public input; §9.3 "the verifier table ⇒ the public chip", §5.1).**
  - **The public chip.** The verifier is chip 0. It has `max 32 (size PublicIO)` base columns:
    the public input, then columns constrained to `0`. A gadget constraint `[r = 0] = 1` gives
    it exactly one row.
  - **The statement** is `pubVec p`: the public input's elements, then zeros.
  - **Restriction: `size PublicIO ≤ 32`.** Under it the statement determines the public input
    (`pubVec_injective`), and `StatementPerm ens p ↔ ∃ k w, rel k (pubVec p) w`
    (`statementPerm_iff`). With more elements the bridge still holds, but only the first 32 are
    statement; the rest are witness.
- **S8-A3 (direction from the syntax; §9.3 "mult = ±1 ⇒ send/receive").**
  - **Rule.** The direction of an interaction comes from its multiplicity as written
    (`readMult`), never from its value: in `K`, `-1 = 1`. The multiplicity `(-1) · e` (Clean's
    `Neg`: `pull`, `pulledIf`) receives with selector `e`; any other `e` (`push`, `pushedIf`,
    `emit`) sends with selector `e`.
  - **Counting.** A message counts once in ℕ when its selector evaluates to `1`; otherwise it is
    silent, as `Table.msgs` reads a selector cell.
  - **Consequence.** A variable multiplicity meant as a count (LogUp's `emit m`) is not `m`
    copies. Use a registered table and a `sub` bus instead.
- **S8-A4 (gadget encoding and the degree limit; §9.3 "an assert of degree d is one CCS term").**
  - **Not one term per assert.** That rule is not how the encoding works: a polynomial needs a
    sum of terms.
  - **The rewriting.** Each `assert e` becomes a sum of products of linear forms (`ofExpr`). A
    product with a variable-free side scales instead of multiplying; the sides of any other
    product are merged first, so a linear side is one factor.
  - **The gadget.** A chip's constraints form one gadget with `Q` terms of degree `D` and
    `Q · D` matrices, where `D` is the longest product and `Q` the most products of one
    constraint (`gadgetOf`, `holds_gadgetOf`).
  - **The degree limit.** Every product of `assert e` has at most `max 1 (degreeBound e)`
    factors (`length_ofExpr_le`), `degreeBound` being Clean's syntactic degree (variable 1,
    constant 0, sum max, product sum). So the cap `|S_i| ≤ 8` holds when every assertion and
    every auxiliary message expression has `degreeBound ≤ 8`.
  - **Auxiliary columns.** A message coordinate or selector that is not a row variable gets an
    auxiliary column constrained to equal it.
- **S8-A5 (channels; §9.3).**
  - **Names.** A channel is its name, as in leanerVM: Clean's `RawChannel` carries propositions
    and has no decidable equality. Bus `b < nch` is `ens.channels[b]` (kind `eq`).
  - **Completeness** needs distinct names (`Supported`). Interactions on unlisted channels
    produce no port, since Clean balances listed channels only.
- **S8-A6 (lookups; §9.3 "Lookup ⇒ sub bus; ProverData tables ⇒ fixed tables").**
  - **Static tables.** A lookup into a table registered in `tabs` (by name and arity) receives
    on a `sub` bus. A fixed chip holding the table's rows sends them on it.
  - **Faithfulness.** `LookupsFaithful` (Clean's `Contains` is membership in the rows, for every
    prover data) is a hypothesis of the bridge. A lookup into an unregistered table goes to a
    bus nobody sends on.
  - **Not covered: tables that depend on the prover data.** In Clean `42fe4b26`, `ProverData`
    is witness, so "ProverData tables ⇒ fixed tables" holds only after Clean commits the data
    (Clean PR #446). Until then such lookups are outside the bridge (S8 open question 2).
- **S8-A7 (finding: Clean's balance is vacuous over `K`; §9.2).**
  - `BalancedInteractions l` requires `l.length < ringChar F`. Over `K` it rejects every list of
    two or more interactions (`clean_balance_vacuous`). So Clean's own `Ensemble.Statement` over
    `K` holds only when every channel has at most one interaction in total.
  - `StatementPerm` (Clean's statement with the ℕ-multiset balance `BalancedPerm`) replaces it.
    The bridge `toLayout_rel_iff` is proved for it in both directions, with explicit witness maps.
- **S8-A8 (finding: the BLAKE2s port; §9.3 item 3, §11 step 9).**
  - **It builds unmodified.** leanerVM's BLAKE2s table (13 modules, `485d0465`) builds on our
    pins and translates, through the generic `toLayout`, to one chip: 60 cells per row (37 row
    plus 23 auxiliary), 23 constraints, degree 2.
  - **It is not admissible.** It has **22 ports**, against the cap of `2^4`; every other cap
    holds.
  - **A faithful port needs:**
    - (a) a channel-to-bus key, because leanerVM's direction is the channel (`st.pull`/`st.push`
      pairs);
    - (b) the ports cap raised to `2^5`, or the row split across chips;
    - (c) a transport from leanerVM's `BF64` to our `K`;
    - (d) the compression gadget itself, which the table does not constrain (Flock proves it in
      leanerVM).
  - **Effort.** (a) to (c) are about a stage-day; (d) belongs with Stage 6a's G chip.

## Stage 5 fix pass (after the S5 review, 2026-10-15)

- **S5-A10 (S5-M1: `live` at the indexer's keys; §5.3; supersedes S5-A7's wording).**
  `live : ∃ L x' nw, nw.vkC = index cfg P C ∧ nw.vkL = index cfg P L ∧ aggOK cfg P x' nw = true`.
  - **Why.** `Secure` constrains `P.verify` only on keys `P.VK L`. Under the S5-A7 form a secure
    protocol could meet `live` with a "magic" key that no layout has, while accepting nothing under
    any indexer key (the review's `toyCM`). `complete` would then constrain `C` only on
    magic-key nodes, which need three hashes and no verification.
  - **Controls.** `magic_not_live`, `magic_no_entry` (`Controls/MagicKey.lean`, adopted from the
    review's probe): `toyCM` is secure (`toyCM_secure`) and meets the S5-A7 form
    (`magic_old_live`), but no node with indexer keys is accepted, so it fails `live` for every `C`.
    Positive: `cmpToy_live` (`Controls/Recursion.lean`). `live_of_secure` (`Library/Recursion.lean`)
    proves the field from one instance of `relK k` whose honest proof fits the cap;
    `aggOK_sat_of_secure` and `aggOK_sat_of_complete` produce this form.
  - **Remaining gap (the review's wording, in the field's docstring).** "A protocol that
    special-cases the key of a trivially satisfiable layout can still meet `live` without accepting
    any proof of a hard layout; that the benchmark's nodes are provable is shown by the benchmark
    run (§6.3)." A `live` at `L_chain` itself would close it, but needs a completeness theorem for
    whole chains, which does not exist.
- **S5-A11 (S5-m1: tags in the statement; §5.1, supersedes S5-A4's last bullet).**
  `nodeStmt cfg vkC vkL t₁ t₂ x₁ x₂` has `d3 = tagSlot t₁ t₂ = (tagK t₁, tagK t₂, 0, 0)`, with
  `tagK leaf = 0`, `tagK node = 1`, and `d4 … d7 = 0`; `aggOK` compares `x'` with it. The binding
  of tags to positions is now contract-level for every leaf layout (by induction from the
  recomputed root: `d2` fixes each child, `d3` its tag), not a property of `L_chain`'s public chip.
  - **Cost.** No hash anywhere; in `C_V` one linear constraint per tag (the tags are already the
    witness bits that select the keys).
  - **Controls.** `mistag_rejected` (the review's `mistag`: the level-2 node with its node child
    tagged leaf, at `xR`, is rejected); `nonzero_d3` now sets limb 2 of `d3`, and `nonzero_d4`
    sets `d4`.
  - **Numbers.** `xN` (tags `leaf, leaf`) is unchanged; `xR` (`node, leaf`) has element 12 = 1.
    `probes/s5/recursion_ref.py` and the kernel KATs are updated.
  - **§5.1 table.** The node row gets `d3 = (t₁, t₂, 0, 0)`, `d4 … d7 = 0`.
- **S5-A12 (S5-m3: the statement tree is trusted; §5.1, §6.3 step 5).** `pairUp` (one level:
  adjacent statements, tagged `t`, aggregated in order; `none` on an odd count) and
  `treeRoot cfg vkC vkL d xs` (depth `d`, level 1 over leaves, above over nodes) are trusted
  definitions in `Contract/Recursion.lean` (now 67 code lines). `rootOK cfg P C L d xs x` is
  `treeRoot cfg (index cfg P C) (index cfg P L) d xs = some x`: it pins `d0`, `d1`, `d2` and `d3`.
  For the benchmark, `d = 6` and `xs` the 64 leaf statements in order.
  - **Library.** `rootOK_iff`, `treeRoot_one`, `treeRoot_two`, `treeRoot_node`, and
    `keys_of_root` (restated for a tree of depth `≥ 1`).
  - **Controls.** `rootOK_xT` (positive, the depth-2 tree over `x0, x1, x0, x1`, KAT `treeKat`
    against Python's `xT`), `rootOK_leaf`, `rootOK_other_key`, `rootOK_odd`.
- **S5-A13 (S5-m5: the harness's key digests; for Stage 6b/7; §6.3, §7.4).** The harness
  1. computes `(index S.cfg S.P S.entry.C).digest S.cfg` with the compiled indexer from the
     submitted `S.entry.C`, never from a layout the prover supplies;
  2. computes `(index S.cfg S.P (L_chain 1024)).digest S.cfg` (the recursion tree's `n = 2^10`,
     not the rendered `L_chain(16)`);
  3. rejects a claim whose `digestC` or `digestL` differs;
  4. uses its own values in `rootOK` and as the key of every node's and leaf's `NARG` run, never
     the declared ones.

  Stage 6b/7 negative controls: a claim with one flipped bit in `digestC` is rejected, and so is
  a claim whose `digestL` is that of `L_chain(16)`. `DeclaredR.digestL`'s docstring now says
  `L_chain(2^10)`.
- **Wording (S5-m2, S5-m4, S5-m6; §5.3).**
  - `complete` ranges over every accepted node, whatever its keys: `verify` must bound its own
    work and its tape on every key (e.g. reject keys outside the format of `VK`).
  - A node child's statement is pinned by its parent's `d2` (collision resistance) and by its own
    proof (the `C_V` relation), not by `aggOK`.
  - `complete`: every accepted node is decoded from a satisfying witness, so every accepted
    statement has a witness of at most `2^k` cells (`decode` may also read cells outside
    `rows × cols`).

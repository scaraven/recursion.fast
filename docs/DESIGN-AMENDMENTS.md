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

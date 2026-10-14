# DESIGN amendments (for the orchestrator to patch into `docs/DESIGN.md`)

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

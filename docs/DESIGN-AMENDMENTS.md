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

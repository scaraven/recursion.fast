# S2 review: the trusted BLAKE2s specification (RFC 7693) and its controls

**Verdict: ACCEPT WITH FIXES.** I found no wrong hash. The spec agrees with RFC 7693 in each of
these checks:

- the constants regenerate from the RFC text byte for byte;
- the compression function differs from the leanerVM pin only as the header says;
- 8,432 grid cases plus the RFC's own Appendix E self-test agree;
- the high counter word agrees with an independent model.

The trust policy holds: no imports, no theorems, no forbidden constructs, and axioms within
`propext`, `Quot.sound` and `Classical.choice`.

There is one major finding, S2-M1. It is about the **regression net**, not the current code. The
CI controls never hash a full final block that follows a non-final block (|d| = 128, 192, …).
That is exactly the input of a 4-, 8- or 16-ary Merkle node, and of `d2 = Blake2s(x₁ ‖ x₂)`
(512 bytes). A plausible wrong specification passes all seven kernel-checked KATs
(`probes/s2/Mutants.lean`).

There are eleven minor findings:
- control gaps (S2-m1, S2-m8, S2-m9);
- interface for Stages 5 and 9 (S2-m2, S2-m3, S2-m10);
- integration and provenance (S2-m4, S2-m5, S2-m6, S2-m11);
- one readability point in the trusted file (S2-m7).

Date: 2026-10-14. Scope:
- `RecursionFast/Contract/Hash/Blake2s.lean` (sha256 `9783228d…`, unchanged during the review);
- `RecursionFast/Controls/Blake2s.lean`, which the golf agent edited at about 18:40 (sha256
  `c357858d…`). I diffed its edit against `logs/S2-golf/Blake2s.controls.orig.lean`: it changes
  proofs only (`rotr_eq_rotateRight`, `blake2s256_length`, and the layout of `iv_spec` and
  `lastNode_kat`), and no statement changed. Declarations are cited by name below.
- `docs/stages/S2-RESULT.md`.

I read these against DESIGN §3.2, §5.1, §5.2, §7.1, §8, RFC 7693 (the text is in
`probes/s2/rfc7693.txt`, SHA-256 `c9437548…`, the hash leanerVM pins), the leanerVM pin
`485d0465`, and leanVM `a386121f` (`crates/primitives/src/hash.rs`, `crates/flock/src/hash.rs`).

I formed the expectation from RFC §3.1–§3.3 before reading the spec's block loop. Every
claim below is backed by a probe under `probes/s2/` (run from the repository root) with its log
under `logs/S2-review-*`.

The passes are kept separate:
- **Pass A (specification: non-vacuity, tightness):** S2-M1, S2-m1, S2-m8, S2-m9.
- **Pass B (fidelity to RFC 7693 and to the leanerVM pin):** no defect; S2-m5 and S2-m6
  (provenance record).
- **Pass C (hygiene, trust, interface):** S2-m2, S2-m3, S2-m4, S2-m7, S2-m10, S2-m11.

## Findings

### S2-M1 (major): no kernel vector for a full final block after a non-final one (|d| = 128); a wrong block loop passes every control

- **Declarations.** `blake2s` and `compressInput` (trusted); the KATs `abc_kat`, `empty_kat`,
  `a64_kat`, `a65_kat`, `keyed_empty_kat`, `keyed_65_kat` and `nn16_kat` (controls).
- **Problem.** The seven KATs cover |d| ∈ {0, 3, 64, 65, 129}. None has |d| a multiple of 64
  greater than 64. That is the boundary where the "held-back final block" rule matters: the last
  full block must be the flagged final block, not followed by an empty one. leanVM's own test
  comment names the rule (`crates/primitives/src/hash.rs`, `matches_reference_vectors`: "block+1
  (the case that pins the held-back-buffer rule)").

  The contract hashes exactly this class:
  - a Merkle node of arity 4, 8 or 16 is 128, 256 or 512 bytes (DESIGN §3.2);
  - `d2 = Blake2s(x₁ ‖ x₂)` is 2 × 32 K-elements = 512 bytes (§5.1).

  Today only the one-off differential test catches a bug here. That test lives in `logs/S2/`,
  which is gitignored and not run in CI (S2-m11). O-S2-2 contemplates rewriting this trusted
  function for speed (ByteArray input, unrolled packing). After such a rewrite the CI controls
  are the only regression check.
- **Evidence.** `probes/s2/Mutants.lean` (51 s, `logs/S2-review-mutants.log`):
  - `heldBack` is the spec with the non-final block count `(|d| - 1) / 64` replaced by
    `if |d| ≤ 64 then 0 else |d| / 64`.
  - `hb_abc` … `hb_nn16` prove that it **passes all seven KATs** of `Controls/Blake2s.lean`
    (`decide +kernel`).
  - `hb_len128` proves that it fails the RFC digest of the 128-byte pattern.
  - The three negative controls and `blake2s_length` cannot see the change either.
- **Fix.** Add to `Controls/Blake2s.lean`:

  ```lean
  /-- 128 bytes = two full blocks: the final block is full and follows a non-final one
  (counters 64, then 128 with the flag); a 4-ary Merkle node (`hashlib`; leanVM
  `crates/primitives/src/hash.rs`, `pattern(128)`). -/
  theorem len128_kat : blake2s256 (pattern 128) =
      hex "83470c75afa23d90cd7659906e4b47daa278131fbb225241dd37a40fd5355ac7" := by decide +kernel
  ```

  - This is checked in `probes/s2/Boundary.lean` and takes **4.5 s** in the kernel. The digest is
    the same in hashlib and in leanVM's test table.
  - Add the item to the file's header list ("pins: a full final block is not followed by an
    empty one").
  - Optional, and stronger than any vector: a Library theorem stating
    `compressInput h t d ((|d| - 1) / 64)` as the RFC §3.3 loop over the 64-byte chunks of `d`,
    with counters `(i + 1) · 64` and then `|d|`. It would pin the loop for every length. It is
    also the lemma Stage 9 needs to prove a circuit computes `blake2s256` (S2-m2).

### S2-m1 (minor): keyed and short-digest classes are pinned only where `kk = nn` (or `kk = 0`) and `nn ∈ {16, 32}`

- **Declarations.** `blake2s` (key padding `List.replicate (64 - kk) 0`, the parameter word);
  `keyed_empty_kat`, `keyed_65_kat`, `nn16_kat`.
- **Problem.**
  - Both keyed KATs have `kk = nn = 32`, so a spec that pads the key with `64 - nn` zeros (a
    one-letter slip) passes them. `probes/s2/Mutants.lean`, `padNN`: `pn_keyed_empty` and
    `pn_keyed_65` pass, `pn_kk1` fails, and `pn_unkeyed` shows that the unkeyed KATs cannot
    see it.
  - The RFC's own Appendix E self-test also always has `kk = nn`, so it does not catch this
    either.
  - No vector has `0 < kk < 32` (a key actually padded), `nn = 1`, or `nn` not a multiple of 4.
    `blake2s_length` pins only the length of the output.
  - The contract uses only `blake2s256`, so this is minor. But `blake2s` is a trusted export
    (O-S2-3 keeps it).
- **Fix.** One 5 s vector covers the short key, `kk ≠ nn` and the S2-M1 boundary together
  (`probes/s2/Combined.lean`; it kills both mutants, `hb_kk1len64` and `pn_kk1len64`):

  ```lean
  /-- A one-byte key (padded with 63 zeros, `kk ≠ nn`) and 64 bytes: `|d| = 128` (`hashlib`). -/
  theorem kk1_kat : blake2s [0x2a] 32 (pattern 64) =
      hex "ac00e6c0bcf8a333106c7f08f68dc06a227a51af0447abb1d099cae263983b85" := by decide +kernel
  /-- `nn = 1`: the parameter byte `0x01` and truncation inside a word (`hashlib`). -/
  theorem nn1_kat : blake2s [] 1 abc = hex "0d" := by decide +kernel   -- 1.45 s
  ```

  With S2-M1 the controls go from about 38 s to about 49 s (the budget is ≤ 60 s).

### S2-m2 (minor): the facts later stages need are in `Controls/`, which nothing may import

- **Declarations.** `blake2s_length`, `blake2s256_length` and `rotr_eq_rotateRight`
  (`Controls/Blake2s.lean`).
- **Problem.**
  - Stage 5 turns the 32-byte `D` output into the 4 K-elements of a `Stmt` slot, and the agents'
    `RecursionEntry.sound` proofs reason about `D nw.vkC = x'.d0`. Both need
    `blake2s256_length`.
  - Stage 9 ports leanerVM's Clean BLAKE2s table. That table is proved against leanerVM's
    `compress`, whose `rotr` is `⟨x.toBitVec.rotateRight n⟩`. Bridging it to
    `RecursionFast.Blake2s.compress` needs `rotr_eq_rotateRight`.
  - `Controls/` is CI-only, and `Library/` is the layer submitters import.
- **Fix.**
  - Move the three theorems to `Library/Blake2s.lean` (untrusted; it imports the spec only).
  - Keep the controls' header pointing at them, or keep a one-line `example` in Controls.
  - State `rotr_eq_rotateRight` with the exact leanerVM right-hand side, as now. It is stated for
    the type actually used (`UInt32`, `n : Nat`, every `n < 32`) and so covers 16, 12, 8 and 7.
    The hypothesis is needed: at `n = 33` the two differ.

### S2-m3 (minor): the byte type and the digest ↔ `K` convention are not fixed yet (O-S2-1)

- **Declarations.** `blake2s256 : List UInt8 → List UInt8` here, and `K.toBytes : List (BitVec 8)`
  in `Contract/Field.lean`.
- **Problem.**
  - The trusted base now has two byte types.
  - Nothing yet says how a 32-byte digest becomes `d_i`, the 4 K-elements: there is no
    `K.ofBytes`.
  - DESIGN §3.2's `VKBytes` type is undecided. If it becomes `ByteArray` for speed, `D` needs a
    conversion too.
  - The digest bytes themselves are unambiguous: standard RFC §2.4 little-endian. The differential
    test shows `hashlib` reproduces them, so a Rust prover can use any conforming BLAKE2s, and the
    `blake2s` docstring states the convention. The open part is only the `K` side.
- **Fix (Stage 5, tracked here).**
  - Define in trusted code `Digest.toK : List UInt8 → Vector K 4`: limb `i` is bytes
    `8i … 8i + 7`, little-endian, the inverse of `K.toBytes`.
  - Define `D vk := blake2s256 ((vk.flatMap K.toBytes).map UInt8.ofBitVec)`, or the `VKBytes`
    equivalent.
  - State in the docstring that this is Rust's `u64::from_le_bytes` on each 8-byte chunk.
  - Back it with a round-trip control (`(Digest.toK b).toList.flatMap K.toBytes = b.map
    UInt8.toBitVec` for `|b| = 32`) and a KAT on `D` of a fixed byte string.

### S2-m4 (minor): the new modules are not in the root imports (O-S2-4)

- **Declarations.** `RecursionFast/Contract.lean` and `RecursionFast/Controls.lean`.
- **Problem.**
  - Lake's globs build both modules, but the roots do not import them.
  - `axiomaudit` imports the roots, so the CI axiom audit does not see the trusted hash. A
    future olean manifest built from the roots would not see it either.
  - `Contract.lean`'s header already lists `Hash.Blake2s` in its reading order.
- **Fix.**
  - Add `import RecursionFast.Contract.Hash.Blake2s` after `Field` in `Contract.lean`.
  - Add `import RecursionFast.Controls.Blake2s` in `Controls.lean`.
  - Re-run `lake build axiomaudit && lake exe axiomaudit`. `probes/s2/Axioms.lean` already
    gives PASS on both modules.

### S2-m5 (minor): the header drops the provenance of the constants

- **Declarations.** The file header; `iv` and `sigma`.
- **Problem.**
  - leanerVM's module docstring records that `iv` and `sigma` were dumped mechanically by
    `scripts/dump-blake2s.py constants` from the RFC 7693 text (SHA-256 `c9437548…`), and that
    leanVM `a386121f` has the same tables.
  - The vendored header keeps only "copied from leanerVM", so a reader of the trusted file loses
    the chain back to the RFC.
  - I re-ran the dump: the RFC-derived tables are **identical** to the spec
    (`probes/s2/vendor-diff.sh`, `probes/s2/vendor-diff.txt`).
- **Fix.** Add one header sentence: "`iv` and `sigma` are leanerVM's mechanical dump of RFC 7693
  Appendix D (`scripts/dump-blake2s.py constants`, RFC text SHA-256 `c9437548…`); `iv_spec` and
  `sigma_perm` re-check them."

### S2-m6 (minor): there is no copy of the Apache-2.0 licence in the repository

- **Problem.**
  - The header is the "prominent notice" of Apache-2.0 §4(b): it names the commit, the paths,
    the line ranges and the changes, and I confirmed all of them. Two details it leaves out are
    harmless: `iv`/`sigma` moved from `LeanerVM.Parameters` to `RecursionFast.Blake2s`, and the
    `end Blake2s` line was dropped.
  - leanerVM has no NOTICE file and no copyright lines, so there is nothing to carry under
    §4(c)/(d).
  - But §4(a) requires giving recipients "a copy of this License". The repository has no
    `LICENSE`, `NOTICE` or `LICENSES/` at all.
- **Fix.** Add `LICENSES/Apache-2.0.txt`, a copy of leanerVM's `LICENSE`, and refer to it from
  the header ("Apache-2.0, see `LICENSES/Apache-2.0.txt`"). This is an orchestrator task.
  Whatever the repository's own licence will be, the vendored excerpt needs this.

### S2-m7 (minor): two trusted expressions rely on non-obvious elaboration and shift semantics

- **Declarations.** `block` and `rotr`.
- **Problem.**
  - In `block`, `b (4 * j)` with `j : Fin 16` elaborates to `4 * j.val` in `Nat`
    (`probes/s2/BlockElab.lean`, `#print`). It is correct, but a reader of the trusted file has to
    know the binop coercion rule to rule out `Fin 16` wrap-around, where `4 · 4 = 0`.
  - `rotr` is correct for `n < 32` because Lean's `UInt32` shifts reduce the amount mod 32 and
    `32 - n ∈ {25, 24, 20, 16}`. The docstring says `n < 32` but not which amounts occur.
- **Fix.**
  - Write `b (4 * j.val)`, `b (4 * j.val + 1)`, and so on. This is the same term, so no semantic
    change.
  - Extend `rotr`'s docstring: "(BLAKE2s uses `n ∈ {16, 12, 8, 7}`)".

### S2-m8 (minor): the high counter word (t ≥ 2^32) has no vector

- **Declarations.** `initialState` (`v[13] ^^^ (t >>> 32).toUInt32`) and `compressInput`
  (`(t + …).toUInt64`).
- **Problem.**
  - No KAT and no hashlib input reaches 4 GiB, so the high counter word is pinned only by
    reading the code.
  - The contract never hashes that much: the tape cap is 1 MiB. So this is an observation, not a
    defect.
- **Evidence.** `probes/s2/compress_model.py` is an independent RFC §3.1–§3.2 model in Python:
  - it was written from the RFC, not from the Lean;
  - it agrees with hashlib on 609 inputs;
  - it gives `compress` vectors at `t = 2^32 + 3` and `t = 2^64 - 1`.
  `probes/s2/HighCounter.lean` (`highCounter`, `maxCounter`) checks both in the kernel, at about
  2 s each.
- **Fix.** Optional: copy `highCounter` into Controls. Otherwise, record in the RESULT that the
  high word is checked by inspection and by this probe.

### S2-m9 (minor): RFC 7693's own self-test (Appendix E) is not used

- **Problem.**
  - Appendix E's `blake2s_selftest` is the RFC's only multi-parameter vector, and it is
    independent of hashlib. Its grand hash covers:
    - `nn ∈ {16, 20, 28, 32}` and `ll ∈ {0, 3, 64, 65, 255, 1024}`;
    - keyed and unkeyed;
    - a final hash of 12 × (16 + 20 + 28 + 32) = 1,152 bytes. That is 18 blocks, the last one
      full, so this hash also exercises S2-M1's class, as does the keyed `ll = 64` case
      (`|d| = 128`).
  - The controls cite Appendix B only.
- **Evidence.** `probes/s2/SelfTest.lean` evaluates it with the spec and reproduces
  `blake2s_res = 6a411f08…7f4c1dfe` (3 s). As a kernel theorem (`probes/s2/SelfTestKernel.lean`)
  it did not finish: I killed it after 5 min of wall time at 32.9 GB of memory. It is unusable in CI.
- **Fix.** Add `#guard` with the `SelfTest.lean` computation to Controls (or to a `tests/`
  executable), labelled as a check of the compiled and interpreted path. It runs in about 1 s
  and prints nothing on success.

### S2-m10 (minor): DESIGN names the one-argument hash `blake2s`; the Lean `blake2s` takes three arguments

- **Problem.**
  - DESIGN §5.2's `aggOK` writes `x'.d2 = blake2s (nw.x₁ ++ nw.x₂)`, §3.2 writes
    `hash ∈ {blake2s, …}`, and §7.1 writes `Blake2s^n(s)`.
  - In Lean, `RecursionFast.blake2s` is the keyed three-argument function. The one-argument
    function is `blake2s256`.
  - A literal transcription fails to typecheck, so this is not silent, but it invites a
    `blake2s [] 32` spelled out by hand, or a wrong `nn`.
- **Fix.**
  - Add an entry to `docs/DESIGN-AMENDMENTS.md`: "`Blake2s`/`blake2s` in DESIGN §3.2, §5.1–§5.2
    and §7.1 is `RecursionFast.blake2s256`."
  - §7.1's `R_chain` chains 32-byte digests. The generator's differential test (§7.2) should use
    `Nat.iterate blake2s256 n s` evaluated from this spec, rather than an external BLAKE2s, so
    that the benchmark is tied to the contract's hash.

### S2-m11 (minor): the differential test is not reproducible from the repository

- **Problem.** `logs/S2/diff-hashlib.{lean,py}` are under `logs/`, which `.gitignore` excludes.
  The strongest evidence in S2-RESULT (306 cases), and the only evidence for S2-M1's class before
  this review, will not survive the commit. `tests/` exists but is empty.
- **Fix.**
  - Commit the two scripts under `tests/blake2s/` (or `scripts/`).
  - Better: commit this review's grid version, `probes/s2/Diff.lean` and `probes/s2/diff.py`:
    - deterministic, with no RNG;
    - `kk ∈ {0, 1, 2, 31, 32}`, `nn ∈ {1, 2, 3, 16, 31, 32}`, every `ll ≤ 260` plus
      319–321, 511–513, 1023–1025, 4096 and 4097;
    - 8,432 cases in 21 s, **0 mismatches** (`logs/S2-review-diff.log`).
  - Run it in `scripts/ci.sh`.

## Pass B: fidelity, item by item (no defect found)

| RFC 7693 item | Spec | Checked by |
|---|---|---|
| §2.6 IV, §2.7 SIGMA | `iv`, `sigma` | `probes/s2/vendor-diff.sh`: identical to `dump-blake2s.py constants` on the RFC text; `iv_spec`, `sigma_perm` |
| §2.3 `>>>`, §2.1 `(R1..R4) = (16, 12, 8, 7)` | `rotr`, `mix` | `rotr_eq_rotateRight`; read against §3.1 line by line |
| §3.1 G, §3.2 F (column, then diagonal; `v[12..13] ^= t`, `v[14] ^= f0`) | `mix`, `round`, `initialState`, `compress` | read against the RFC; `vendor-diff.sh`: only the documented `rotr` hunk and namespace prefixes differ from leanerVM `485d0465` |
| §2.5 `h[0] ^= 0x01010000 ^ (kk << 8) ^ nn` | `blake2s` | precedence checked: `<<<` (75) binds tighter than `^^^` (58); `nn16_kat`, `nn1` and `kk1` probes |
| §3.3 key block `d[0]`, zero-padded, counted in `t` | `blake2s` (`d := key ++ zeros ++ msg`) | `keyed_empty_kat`, `keyed_65_kat`; probes `kk1`, `kk32len1`, `kk32len64` |
| §3.3 `dd = 1` for `kk = ll = 0` | `(|d| - 1) / 64 = 0` | `empty_kat` (`t = 0`) |
| §3.3 counters `(i + 1)·bb`, final `ll` or `ll + bb` | `compressInput` | `a65_kat`, `keyed_65_kat`; probes `len128`, `len129` |
| §2.4 LE bytes ↔ words; first `nn` bytes | `block`, `le`, `take nn` | `abc_kat` (Appendix B); `blake2s_length`; probe `nn1` |
| v[13] high counter word | `initialState` | probe `highCounter`, `maxCounter` (S2-m8) |
| whole function | `blake2s` | 8,432-case grid vs hashlib, 0 mismatches; Appendix E self-test reproduced |

Out of the RFC domain (`kk > 32`, `nn = 0`, `nn > 32`) the function is total and arbitrary, as
the docstring says. No contract path reaches it, because `blake2s256` fixes `kk = 0` and `nn = 32`.

## Trust and totality (Pass C)

- **Constructs.** The trusted file has no `import`, so it uses Lean core only. It has no
  `theorem`, `instance`, attribute, `set_option`, `partial`, `unsafe`, `implemented_by`, `extern`,
  `csimp` or `native_decide`.
- **Totality.** `compressInput` recurses structurally on its `Nat` argument.
- **Docstrings.** Every one of the 11 definitions has a docstring, and each cites an RFC section.
  The sections cited are correct: §2.3 is "Arithmetic Notation", which defines `>>>`.
- **Lint.** `scripts/check-hygiene.sh`: OK.
- **Axioms.** `probes/s2/Axioms.lean` (`logs/S2-review-axioms.log`) audits 12 declarations in the
  spec and 28 in the controls, with **0 outside** `propext`, `Classical.choice`, `Quot.sound`.
  - `blake2s`, `blake2s256` and `rotr_eq_rotateRight` use `[propext, Quot.sound]`.
  - The `hex` KATs also use `Classical.choice`, which comes from core's `String` lemmas.
  - No declaration uses `Lean.ofReduceBool`.
- **The gate.** It rejects `@[csimp]` from unpinned modules (`scripts/Gate.lean`). So D-S2-1's
  premise holds: an agent cannot swap in a faster hash.
- **D-S2-1** (machine-shift `rotr`). I accept it. It is one line, it is proved equal to
  leanerVM's form for all `n < 32`, and its premise holds.
- **Comment density.** 46 comment lines to 67 code lines, against 27 to 36 in `Field.lean`;
  comparable.
- **Controls.** The file explains what each vector pins. It elaborates in **37.7 s** wall time and
  1.07 GB (`logs/S2-review-controls-time.log`).

## Coverage table (input class × kernel vector)

"Controls" means a theorem in `Controls/Blake2s.lean`, and "probe" means a theorem in
`probes/s2/*.lean`. Every class is also covered by the evaluated grid (`Diff.lean`), except the
high counter word.

| Input class | Controls | Probe (kernel time) |
|---|---|---|
| `ll = 0`, `kk = 0` (one zero block, `t = 0`) | `empty_kat` | — |
| `ll = 1` | — | `len1` (2.3 s) |
| `1 < ll < 64` | `abc_kat`, `nn16_kat` | — |
| `ll = 64` (one full final block) | `a64_kat` | — |
| `ll = 65` (counters 64, 65) | `a65_kat` | — |
| **`ll = 128`, `kk = 0` (full final block after a non-final one)** | **none (S2-M1)** | `len128` (4.5 s) |
| `ll = 129`, `kk = 0` (three blocks) | — (`keyed_65_kat` has `\|d\| = 129`) | `len129` (6.0 s) |
| `\|d\|` a multiple of 64, ≥ 192 (Merkle arity 8/16, `d2`) | none | — (grid: 192, 256, 320, 512, 1024, 4096) |
| `kk = 32`, `ll = 0` (key block alone, `t = 64`) | `keyed_empty_kat` | — |
| `kk = 32`, `ll = 1` | — | `kk32len1` (4.3 s) |
| `kk = 32`, `ll = 64` (`\|d\| = 128`) | — | `kk32len64` (5.1 s) |
| `kk = 32`, `ll = 65` (counters 64, 128, 129) | `keyed_65_kat` | — |
| **`0 < kk < 32` (key actually padded); `kk ≠ nn`** | **none (S2-m1)** | `kk1` (4.4 s), `kk1nn1empty` (2.0 s), `kk1len64` (≈ 5 s) |
| `nn = 1`; `nn` not a multiple of 4 | length only (`blake2s_length`) | `nn1` (1.45 s), `kk1nn1empty` |
| `nn = 16` | `nn16_kat`, `nn_neg` | — |
| bytes ≥ `0x80` (packing) | `keyed_65_kat` (pattern) | — |
| `t ≥ 2^32` (high counter word) | none (unreachable) | `highCounter`, `maxCounter` (≈ 2 s each) |
| last-node flag `f1` (unused) | `lastNode_kat` | — |
| one-bit message change; key ignored; `nn` as truncation only | `flip_neg`, `key_neg`, `nn_neg` | — |
| RFC Appendix E self-test (48 hashes plus the grand hash) | none | `SelfTest.lean` (`#eval`, 3 s); kernel: aborted (> 5 min, > 32 GB) |
| out of domain (`kk > 32`, `nn ∉ [1, 32]`) | none (documented, unused) | — |

## Interface for later stages

The interface is sufficient for `D` and for `d2`: both are `blake2s256` of a `List UInt8`, and
`blake2s256_length` gives 32 bytes. Before Stage 5, three things are owed:

- where the facts live (S2-m2);
- the digest → `Vector K 4` convention (S2-m3);
- the DESIGN name (S2-m10).

The byte order the Rust and native provers must match is standard RFC 7693: digest bytes are
the little-endian words `h[0..7]`. The `K` side is `K.toBytes`, also little-endian. What is not
yet written down is the map from 32 digest bytes to 4 limbs (S2-m3).

## Probes (`probes/s2/`, run from the repository root)

| Probe | What it shows | Log |
|---|---|---|
| `vendor-diff.sh` | RFC-dumped `iv`/`sigma` are identical to the spec; the vendored diff vs leanerVM `485d0465` has 3 hunks (`rotr`, the dropped `end Blake2s`, the namespace prefixes) | `probes/s2/vendor-diff.txt` |
| `rfc7693.txt` | the RFC text, SHA-256 `c9437548…` (leanerVM's pin) | — |
| `Boundary.lean` | 9 kernel vectors: `hex_all`, `len1`, `len128`, `len129`, `nn1`, `kk1`, `kk1nn1empty`, `kk32len64`, `kk32len1` (31 s) | `logs/S2-review-boundary.log` |
| `Combined.lean` | `kk1len64`: one 5 s vector for S2-M1 and S2-m1 | `logs/S2-review-combined.log` |
| `Mutants.lean` | `heldBack` and `padNN` pass every existing KAT; the new vectors kill both (51 s) | `logs/S2-review-mutants.log` |
| `vectors.py` | hashlib digests for the probes | `probes/s2/vectors.out` |
| `Diff.lean`, `diff.py` | grid differential: 8,432 cases, 0 mismatches | `logs/S2-review-diff.{out,log}` |
| `SelfTest.lean` | RFC Appendix E `blake2s_res` reproduced (`#eval`) | `logs/S2-review-selftest.log` |
| `SelfTestKernel.lean` | the same as a `decide +kernel` theorem (timing) | `logs/S2-review-selftest-kernel.log` |
| `compress_model.py`, `HighCounter.lean` | independent Python F; `t = 2^32 + 3` and `2^64 - 1` in the kernel | `logs/S2-review-compress-model.log`, `logs/S2-review-highcounter.log` |
| `Axioms.lean` | axiom audit of both modules: 0 outside the allowed set | `logs/S2-review-axioms.log` |
| `BlockElab.lean` | `block` elaborates `4 * j` as `4 * j.val : Nat`; LE packing of bytes 0..63 | — |

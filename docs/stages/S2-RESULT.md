# S2 RESULT: the hash BLAKE2s (RFC 7693), trusted specification and known-answer tests

Stage 2 is DESIGN §11 step 3 (open item O-2). One agent implemented it on 2026-10-14. Nothing is
committed and no existing file was edited. The root files are unchanged: the orchestrator adds
`import RecursionFast.Contract.Hash.Blake2s` to `RecursionFast/Contract.lean` (after `Field`) and
`import RecursionFast.Controls.Blake2s` to `RecursionFast/Controls.lean`. Lake's globs already build
both modules in the default `lake build` (`logs/S2/build.log`).

## Headline

The figures below are **after the fix pass** (section "Fix pass" at the end). The fix pass
moved the general facts to `Library/Blake2s.lean` and added five kernel vectors.

- **Trusted spec: 68 code lines** (target ≤ 130, cap 150). It is in `Contract/Hash/Blake2s.lean`,
  has no `import` line (Lean core only), and the §8 budget does not count it.
- **The spec agrees with Python's `hashlib.blake2s`** on 306 random cases and **disagrees on none**
  (`logs/S2/diff-hashlib.log`). The cases cover key lengths 0–32, `nn` from 1 to 32, every message
  length from 0 to 299, and lengths 511, 512, 513, 1000, 4096 and 8193.
- **Twelve kernel-checked known-answer tests (KATs), three negative controls, and the constants
  checks** are in `Controls/Blake2s.lean`. The three general facts (`rotr_eq_rotateRight`,
  `blake2s_length`, `blake2s256_length`) are in `Library/Blake2s.lean`.
  - The KATs, the negative controls and the constants checks are closed by `decide +kernel`. The
    library facts are closed by `simp` or a term.
  - Each KAT takes **1.4–5.2 s** in the kernel. The file takes **≈ 47–49 s** (budget ≤ 60 s), and
    peak memory is 1.07 GB.
  - `rfl` and plain `decide` both fail with "maximum recursion depth", which cannot be raised
    because the hygiene check forbids it (`logs/S2/rfl-decide-attempt.log`).
- **Axioms:** only `propext`, `Quot.sound` and `Classical.choice`. The axiom audit, run on the
  three new modules, reports **PASS** on 44 declarations (12 spec, 27 controls, 5 library), and
  `scripts/check-hygiene.sh` reports OK.
- **Deviation needing a decision (D-S2-1):** `rotr` uses machine shifts, not leanerVM's
  `BitVec.rotateRight`. The executed (compiled) hash becomes **13× faster**: 82 µs → 6.1 µs per
  one-block hash. The rotation alone accounts for 7.5×; block packing over an `Array` (`block` is
  new code) gives the rest. The equivalence with leanerVM's definition is proved
  (`Blake2s.rotr_eq_rotateRight`, `Library/Blake2s.lean`).

## Files

Code lines are from `scripts/loc.py` (`logs/S2/fix/loc.log`). The before-the-fix-pass counts were:
spec 67, and controls 55, which became 51 after the golf.

| File | Status | Code | Total | What it is |
|---|---|---:|---:|---|
| `Contract/Hash/Blake2s.lean` | **TRUSTED, new** | 68 | 139 | `Blake2s.iv`, `sigma`, `rotr`, `mix`, `round`, `initialState`, `compress` (vendored); `Blake2s.block`, `Blake2s.compressInput`, `blake2s`, `blake2s256` (new) |
| `Contract/Hash/LICENSE-leanerVM` | licence, new | — | 184 | Apache-2.0 text, byte-identical to leanerVM's `LICENSE` at `485d0465` |
| `Library/Blake2s.lean` | untrusted, new | 13 | 34 | `Blake2s.rotr_eq_rotateRight`, `blake2s_length`, `blake2s256_length` (moved from the controls, S2-m2) |
| `Controls/Blake2s.lean` | controls, new | 52 | 160 | `hex` reader, constants checks, 12 KATs, 3 negative controls (16 theorems) |
| `probes/s2/` | probes (committed) | — | — | the reviewer's probes, plus: the grid differential test `Diff.lean` and `diff.py` with a one-line `README.md`; `SelfTest.lean` (Appendix E, `#guard`); `Mutants.lean` (extended) |

Build times, from the default `lake build` with only the three new modules stale
(`logs/S2/fix/build.log`):

| Module | Time |
|---|---:|
| `Contract.Hash.Blake2s` | 5.2 s (`lake env lean`: 7.0 s wall, 0.85 GB) |
| `Library.Blake2s` | 0.9 s |
| `Controls.Blake2s` | 47 s (`lake env lean`: 48.5 s wall, 1.07 GB; `logs/S2/fix/controls-time.log`) |

## Interface

```lean
def RecursionFast.blake2s (key : List UInt8) (nn : Nat) (msg : List UInt8) : List UInt8
def RecursionFast.blake2s256 (msg : List UInt8) : List UInt8 := blake2s [] 32 msg
-- helpers, in namespace RecursionFast.Blake2s:
--   iv, sigma, rotr, mix, round, initialState,
--   compress (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32),
--   block (d : List UInt8) : Vector UInt32 16,
--   compressInput (h) (t : Nat) (d : List UInt8) : Nat → Vector UInt32 8
```

The interface has no `digestWords` or `ofBytes`, because `D` only needs bytes in and bytes out. The
glue to `K` is Stage 5's job (O-S2-1).

## How the full hash follows RFC 7693 §3.3

The full hash is in `blake2s`, which is 6 lines, and `compressInput`, which is 3 lines.

1. **Parameter block (§2.5).** The initial state is
   `h := iv.set 0 (iv[0] ^^^ 0x01010000 ^^^ kk <<< 8 ^^^ nn)`. This is the RFC line
   `h[0] := h[0] ^ 0x01010000 ^ (kk << 8) ^ nn` verbatim.
2. **Padded input.** The input is `d := (if kk = 0 then [] else key ++ zeros(64 - kk)) ++ msg`, so the
   key block, when present, is `d[0]`. `|d|` is the RFC's `ll`, plus `bb = 64` when the key is set.
   This is exactly the counter the RFC gives the final block.
3. **Blocks.** `(|d| - 1) / 64 = dd - 1` non-final blocks precede the final one. With ℕ subtraction,
   an empty `d` gives 0, so `dd = 1` and there is one zero block: the RFC's "dd is always nonzero".
   - `compressInput` recurses **structurally on that ℕ**. There is no well-founded recursion, no
     `partial` and no fuel that could run out.
   - Each non-final block is compressed with counter `t + 64` and `f0 = 0`.
   - The final block is the rest of `d`, at most 64 bytes, zero-padded. It is compressed with counter
     `t + |rest| = |d|` and `f0 = 0xFFFFFFFF`, `f1 = 0`.
   - The counter is the `Nat` converted `toUInt64`, so it is exact below 2^64 bytes, the RFC's limit.
4. **Words (§2.4).** `block d` reads the first 64 bytes of `d`, zero-padded, as 16 little-endian
   words. The output is the 8 state words, each as 4 little-endian bytes, of which the first `nn`
   are kept.

**Domain.** The function is total, but RFC 7693 defines it only for `key.length ≤ 32` and
`1 ≤ nn ≤ 32`. The docstring says so, and nothing enforces it (O-S2-3). The contract only uses
`blake2s256` (`kk = 0`, `nn = 32`).

**Performance.** The function is linear in `|msg|`:
- each block is `take 64` plus `toArray`;
- the compression updates its working vector in place: `Vector.set` on a unique array, which the
  generated C confirms (`lean_array_fget_borrowed`, `uint32` arithmetic).

## Controls and what each shows (`Controls/Blake2s.lean`)

Each expected digest is the published hex string, read by `hex : String → List UInt8`.
`hex_pos` pins the reader (`hex "00ff7f80a519" = [0x00, 0xff, 0x7f, 0x80, 0xa5, 0x19]`).

A bug in `hex` cannot make a KAT pass, because the left side is the bytes the spec computes. The
negative controls compare two spec outputs and never use `hex`. Kernel times come from
`logs/S2/fix/controls-trace-sync.log` (`-DElab.async=false`).

| Theorem | Statement / input | Source of the expected value | What it pins | Kernel |
|---|---|---|---|---:|
| `sigma_perm` | each row of `sigma` is a permutation of `Fin 16` | RFC §2.7 (leanerVM test) | schedule shape | 0.87 s |
| `iv_spec` | `iv[i] = ⌊2^32·frac(√pᵢ)⌋` via `s² ≤ p·2^64 < (s+1)²` | RFC §2.6 (leanerVM test) | IV from its definition, not transcription | < 0.6 s |
| `abc_kat` | `blake2s256 "abc" = 508c5e8c…86675982` | **RFC 7693 Appendix B**; hashlib; leanVM `flock` | one block, counter 3, parameter block, output order | 2.31 s |
| `empty_kat` | `blake2s256 [] = 69217a30…1ed0eef9` | hashlib; leanVM `primitives` and `flock` | `dd = 1` zero block, counter 0 | 2.31 s |
| `a64_kat` | `blake2s256 ('a'×64) = 651d2f5f…ffb7b252` | hashlib; leanVM `flock` | exactly one full block; no extra empty block | 2.45 s |
| `a65_kat` | `blake2s256 ('a'×65) = 045f8ae1…3d92a497` | hashlib; leanVM `flock` | two blocks: counter 64 (no flag), then 65 (flag) | 3.65 s |
| `keyed_empty_kat` | `blake2s (0…31) 32 [] = 48a8997d…45fd2c49` | hashlib; leanVM `primitives` | key block alone is final, counter 64; `kk` in parameter block | 2.39 s |
| `keyed_65_kat` | `blake2s (0…31) 32 (pattern 65) = 82e02e62…446b71cb` | hashlib; leanVM `primitives` | three blocks, counters 64, 128, 129 | 5.21 s |
| `nn16_kat` | `blake2s [] 16 "abc" = aa493811…d200d0ae` | hashlib (`digest_size=16`) | `nn` in parameter block and truncation | 1.52 s |
| **`len128_kat`** (fix) | `blake2s256 (pattern 128) = 83470c75…d5355ac7` | hashlib; leanVM `primitives` | `\|d\| = 128`: a full final block after a non-final one, no empty block after it (Merkle arity 4/8/16, `d2`) | 3.74 s |
| **`kk1_kat`** (fix) | `blake2s [0x2a] 32 (pattern 64) = ac00e6c0…63983b85` | hashlib | key padded with `64 − kk` zeros, `kk ≠ nn`, `\|d\| = 128` | 3.93 s |
| **`nn1_kat`** (fix) | `blake2s [] 1 "abc" = 0d` | hashlib | `nn = 1`: parameter byte and truncation inside a word | 1.40 s |
| **`kk1nn16_kat`** (fix) | `blake2s [0x2a] 16 "a" = 27729f2e…4a0e09f2` | hashlib | `kk = 1`, `nn = 16` (neither 32, `kk ≠ nn`) | 3.18 s |
| `lastNode_kat` | `compress` with `f0 = f1 = 0xFFFFFFFF` on the empty block = `[0x3c11fc24, …]` | leanerVM test (hashlib `last_node=True`) | the vendored `f1` path, unused by `blake2s` | 1.36 s |
| **`highCounter_kat`** (fix) | `compress` of "abc"'s block at `t = 2^32 + 3`, `f0` set = `[0xedf58467, …]` | independent Python model of RFC §3.1–§3.2 (`probes/s2/compress_model.py`, = hashlib on 609 inputs) | the high counter word `v[13] ^ (t >>> 32)` | 1.39 s |
| **`flip_neg`** | `blake2s256 "abb" ≠ blake2s256 "abc"` (one bit, `0x63 → 0x62`) | — | spec is not constant in the message | 2.43 s |
| **`key_neg`** | `blake2s (0…31) 32 [] ≠ blake2s256 []` | — | the key is not ignored | 2.86 s |
| **`nn_neg`** | `blake2s [] 16 "abc" ≠ (blake2s256 "abc").take 16` | — | `nn` is not only a truncation | 2.44 s |

The general facts are in `Library/Blake2s.lean` (S2-m2): `Blake2s.rotr_eq_rotateRight`
(`∀ x, n < 32 → rotr x n = ⟨x.toBitVec.rotateRight n⟩`, `simp`; D-S2-1 changes no value),
`blake2s_length` (`= min nn 32`, `simp`) and `blake2s256_length` (`= 32`, term).

The leanVM test vectors were confirmed in the pinned checkout `a386121f` before use:
- `crates/flock/src/hash.rs` lines 1059–1078 give the empty message, "abc", 'a'×64 and 'a'×65;
- `crates/primitives/src/hash.rs` lines 1222–1258 give the unkeyed pattern vectors and the keyed
  vectors.

The keyed empty-message vector `48a8997d…45fd2c49` is confirmed by both leanVM and hashlib.

### Independent check: `#eval` (compiler and interpreter path; `logs/S2/kat-eval.log`)

```
"abc        508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"
"empty      69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"
"a x 64     651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252"
"a x 65     045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497"
"keyed []   48a8997da407876b3d79c0d92325ad3b89cbb754d86ab71aee047ad345fd2c49"
"keyed p65  82e02e62a066f2f3cd7a8a542581cbf441e35cf7a771fc7adb0965d8446b71cb"
"nn16 abc   aa4938119b1dc7b87cbad0ffd200d0ae"
"abb        178d4bc76f5b3d0328a7c1dcce8c9b85845114630b7bbc357255356e35c443c9"
"lastNode   [3c11fc24, 848cbe3d, 40703c49, 680dafae, ab7b3bcc, 49aecd0d, 704abbdb, 365c9d25]"
```

Python's `hashlib` gives the same nine values in the same log. For `lastNode`, the hashlib output
`24fc113c…` is the little-endian byte form of the same words.

### Differential test (`logs/S2/diff-hashlib.{lean,py,out,log}`)

The Lean side derives the key, `nn` and message of each case from an LCG and prints both
`blake2s key nn msg` and `blake2s256 msg`. `python3 -I` recomputes both with `hashlib.blake2s`.

Result: **306 cases, 0 mismatches.** Every key length from 0 to 32 and every `nn` from 1 to 32
occurs.

## `#print axioms` (`logs/S2/axioms.log`; after the fix pass, see "Fix pass")

```
'RecursionFast.blake2s' depends on axioms: [propext, Quot.sound]
'RecursionFast.blake2s256' depends on axioms: [propext, Quot.sound]
'RecursionFast.Blake2s.compressInput' depends on axioms: [propext, Quot.sound]
'RecursionFast.Blake2s.compress' depends on axioms: [propext, Quot.sound]
'RecursionFast.Blake2s.block' depends on axioms: [propext, Quot.sound]
'RecursionFast.Blake2s.rotr_eq_rotateRight' depends on axioms: [propext, Quot.sound]   -- now in Library
'RecursionFast.Controls.Blake2s.abc_kat' depends on axioms: [propext, Classical.choice, Quot.sound]
… (every other KAT the same; sigma_perm, iv_spec, lastNode_kat, the length theorems and the three
   negative controls: [propext, Quot.sound])
```

- In the spec, `propext` and `Quot.sound` come from the `get_elem_tactic` bound proofs of the vector
  indexing.
- In the `hex`-based KATs, `Classical.choice` comes from core's `String` lemmas.
- None of the KATs uses `Lean.ofReduceBool`.

The axiom audit (`scripts/AxiomAudit.lean` with `mods` set to the two new modules,
`logs/S2/AxiomAuditS2.lean`) reports:
`RecursionFast.Controls.Blake2s: 28 declarations`, `RecursionFast.Contract.Hash.Blake2s: 12 declarations`,
`PASS (every declaration within propext, Classical.choice, Quot.sound)`.

## Provenance of the vendored code

- **Source:** leanerVM (Apache-2.0), `git@github.com:Verified-zkEVM/leanerVM`, commit
  `485d0465d1db38a471fb387aa0dd6baf5a5a1ac7`. The working tree was clean. The files were last changed
  in `72f71be` (Layer 1) and `144c5aa` (Lean 4.34.1 bump).
- **`LeanerVM/Parameters/Blake2s.lean` lines 29–47:** `iv`, `sigma`. leanerVM dumped these
  mechanically from the RFC 7693 text, SHA-256 `c9437548…`.
- **`LeanerVM/Semantics/Blake2s.lean` lines 64–110:** `rotr`, `mix`, `round`, `initialState`,
  `compress`.
- **Byte-level diff** (`logs/S2/vendor-diff.log`, blank lines ignored). There are exactly two hunks:
  1. `rotr`: `⟨x.toBitVec.rotateRight n⟩` with `n : ℕ` became
     `x >>> n.toUInt32 ||| x <<< (32 - n).toUInt32` with `n : Nat`. Its docstring now says `n < 32`
     and "with machine shifts".
  2. `compress`: `Blake2s.round` and `Blake2s.initialState` lost their namespace prefix, because
     `compress` now lives in `RecursionFast.Blake2s`.

  The module-system lines (`module`, `public import`, `@[expose] public section`) are not copied.
  Every other docstring and line is verbatim.
- **Attribution:** the file header names the licence, the repository, the commit, the paths, the
  line ranges and the changes. This is the "prominent notice" that Apache-2.0 §4(b) asks for. leanerVM
  has no NOTICE file and no per-file copyright lines to carry over. The fix pass added the licence
  text itself (§4(a)) as `RecursionFast/Contract/Hash/LICENSE-leanerVM`, and the header names it.

## Deviations from the design and the brief, with reasons

1. **D-S2-1: `rotr` is not verbatim. It uses machine shifts.**
   - **Why:** compiled Lean runs `BitVec.rotateRight` on `Nat`. The left shift of a 32-bit value
     overflows the 63-bit scalar range into a GMP bignum.
   - **Measured** with `leanc -O3` (`logs/S2/bench-compiled.log`):

     | Variant | One-block hash | Per block, long input |
     |---|---:|---:|
     | leanerVM's `rotr`, `List.getD` block | 82 µs | 83 µs (16 KiB input, 257 blocks) |
     | machine-shift `rotr`, `List.getD` block | 10.9 µs | 9.7 µs |
     | **final spec** (machine-shift `rotr`, `Array` block) | **6.1 µs** | **5.5 µs** |

     In the final spec, one compression takes 1.9 µs and one `block` 2.5 µs.
   - **Why it matters:** the executed verifier is this code, compiled (DESIGN §3.2). The trusted base
     forbids `implemented_by` and `csimp`, and agents cannot replace the organiser's hash. So this
     speed is a fixed per-hash cost in every score.
   - **Equivalence:** `Blake2s.rotr_eq_rotateRight` (`Library/Blake2s.lean`) proves the two definitions equal for every `n < 32`. The
     spec only uses 16, 12, 8 and 7.
   - **To revert:** change one line; the controls still pass.
2. **The brief named `Nat`; there is no `ℕ` to replace.** The only `ℕ` was in `rotr`, which D-S2-1
   rewrote.
3. **The general keyed `blake2s` is total and not restricted to the RFC domain** (`kk ≤ 32`,
   `1 ≤ nn ≤ 32`). The docstring states the domain. See O-S2-3.
4. **The controls read expected digests through a `hex` helper** instead of writing byte lists.
   - **Why:** each digest can be compared character for character with RFC Appendix B, hashlib and
     the leanVM tests.
   - **Cost:** at most about 1 s of kernel time per vector. `abc` takes 1.8 s with a byte list
     (`logs/S2/bytelist-kat.log`) and 2.0 s with `hex`.
5. **The KATs are named `theorem`s, not `example`s**, so that the axiom audit and `#print axioms`
   can see them.
6. **Size:** DESIGN §8 estimates ≈ 150 lines; the result is 67 code lines.
7. **The `#eval`s live in `logs/S2/kat-eval.lean`, not in the controls file.** CI build logs stay
   quiet, and the kernel and compiler paths remain separate checks.

## Open questions for the orchestrator

- **O-S2-1: bytes type for `D` (Stage 5).**
  - **The mismatch:** `Field.lean`'s `K.toBytes` returns `List (BitVec 8)`, but the hash takes
    `List UInt8` (as briefed).
  - **Cheapest bridge:** `UInt8.ofBitVec`, which is `UInt8`'s structure constructor, so the bridge
    is definitional: `D vk := blake2s256 ((vk.flatMap K.toBytes).map UInt8.ofBitVec)`.
  - **Also needed:** Stage 5/6 must decide how a 32-byte digest becomes the 4 `K`-elements of a
    `Stmt` digest slot `d_i`. Little-endian 8-byte limbs mirror `K.toBytes`.
    `blake2s256_length` already gives the 32.
- **O-S2-2: compiled speed of the executed verifier.**
  - **Sign-off needed:** D-S2-1 above.
  - **Broader point:** the trusted `K.mul` (`Field.lean`, `clmul` over `BitVec 128`) costs
    **27 µs** compiled (`logs/S2/bench-kmul.lean`), about 4.5 one-block hashes. Natively the ratio is
    the other way round: clmul takes nanoseconds and a BLAKE2s compression about 150 ns.
  - **What agents can and cannot change:** agents can write faster `K` arithmetic in their own
    verifier and prove it equal to the spec, but not a faster hash.
  - **Decision:** whether ≈ 6 µs per block is acceptable as the fixed hash cost. The alternative is
    a still-pure but faster trusted formulation, e.g. `ByteArray` input or unrolled packing.
- **O-S2-3: domain of `blake2s`.**
  - **Options:**
    - keep it as is (documented, only `blake2s256` is used);
    - drop the general keyed form and expose only `blake2s256`, which saves about 3 lines;
    - restrict it by type.
  - **Recommendation:** keep it as is. The keyed vectors are part of the tests that pin the counter
    rule.
- **O-S2-4: root imports.**
  - **Lines to add:** `import RecursionFast.Contract.Hash.Blake2s` in `Contract.lean`, and
    `import RecursionFast.Controls.Blake2s` in `Controls.lean`.
  - **Why it matters:** `axiomaudit` imports the roots, so it sees the new modules only after these
    lines are added.
  - **Cost:** CI gains about 31 s, the controls file.
- **O-S2-5: no existing verified Lean spec was found to reuse** (DESIGN §8 asked). leanerVM has the
  compression function but no full hash with padding, key or counter loop. That part (`block`,
  `compressInput`, `blake2s`) is new, and it is what the KATs and the differential test pin.

## Commands run

- `lake build` (default targets): green, no warnings (`logs/S2/build.log`). With only the new modules
  stale it takes 38.6 s.
- `/usr/bin/time -v lake env lean RecursionFast/Controls/Blake2s.lean` and the spec file: the timings
  above (`logs/S2/controls-trace.log`, `logs/S2/controls-trace-sync.log`, `logs/S2/spec-time.log`).
- `lake env lean logs/S2/axioms.lean` → `logs/S2/axioms.log`. `lake env lean --run
  logs/S2/AxiomAuditS2.lean` → `logs/S2/axiomaudit.log` (PASS).
- `scripts/check-hygiene.sh` → `logs/S2/hygiene.log` (OK).
- `python3 scripts/loc.py RecursionFast/Contract/Hash/Blake2s.lean RecursionFast/Controls/Blake2s.lean`
  → `logs/S2/loc.log`.
- `lake env lean --run logs/S2/diff-hashlib.lean > logs/S2/diff-hashlib.out`, then
  `python3 -I logs/S2/diff-hashlib.py logs/S2/diff-hashlib.out` → `logs/S2/diff-hashlib.log`.
- `lake env lean logs/S2/kat-eval.lean` → `logs/S2/kat-eval.log`.
- `logs/S2/bench-{final,parts,kmul}.lean`, built standalone with `lean -c` and `leanc -O3` →
  `logs/S2/bench-compiled.log`. That log's "per block" column for the 8224-byte case divides by 129;
  the input is actually 16 KiB, 257 blocks, and the corrected per-block figures are the ones in
  D-S2-1.

## Fix pass

This pass answers `docs/reviews/S2-review.md` (verdict **ACCEPT WITH FIXES**) and follows the
orchestrator's decisions, on 2026-10-14. The golf (`docs/reviews/S2-golf.md`) had changed proofs
only. It left the controls at 51 code lines and the spec byte-identical (sha256 `9783228d…`). I
re-read the golfed controls before editing and moved its golfed proofs verbatim. Starting copies
are `logs/S2/fix/{spec,controls}.before.lean`; all logs of this pass are under `logs/S2/fix/`.

### Findings, one by one

- **S2-M1 (major): fixed.** Added `len128_kat`: `blake2s256 (pattern 128) = 83470c75…d5355ac7`
  (hashlib and leanVM `pattern(128)`), 3.7 s. A full final block after a non-final one is now
  pinned in CI.
- **S2-m1: fixed.** Each vector stays ≤ 6 s:
  - `kk1_kat`: key `[0x2a]`, `nn = 32`, `pattern 64`, so `|d| = 128`; 3.9 s;
  - `nn1_kat`: `blake2s [] 1 "abc" = 0d`; 1.4 s;
  - `kk1nn16_kat`: key `[0x2a]`, `nn = 16`, message "a"; a keyed vector with `kk ≠ nn` and
    neither 32; 3.2 s.

  The expected values are recomputed by `probes/s2/vectors.py` with hashlib
  (`logs/S2/fix/vectors.log`).
- **S2-m2: fixed.** `rotr_eq_rotateRight`, `blake2s_length` and `blake2s256_length` moved to the
  new untrusted `RecursionFast/Library/Blake2s.lean`.
  - It imports the spec only; Mathlib was not needed.
  - The new names are `RecursionFast.Blake2s.rotr_eq_rotateRight`, `RecursionFast.blake2s_length`
    and `RecursionFast.blake2s256_length`. They were `RecursionFast.Controls.Blake2s.*`.
  - The statements are unchanged, and the proofs are the golfed ones.
  - `RecursionFast/Library.lean` is not edited; the orchestrator adds
    `import RecursionFast.Library.Blake2s`. Lake's glob builds it already.
- **S2-m3: deferred to Stage 5.** Recorded as **S2-A1** in `docs/DESIGN-AMENDMENTS.md`:
  - `D` hashes `vk.flatMap K.toBytes` mapped by `UInt8.ofBitVec`;
  - a digest becomes 4 K-elements, each read little-endian from 8 bytes;
  - `K.ofBytes` is to be added.
- **S2-m4:** the orchestrator adds the root imports at commit. There are now three:
  `Contract.Hash.Blake2s`, `Controls.Blake2s` and `Library.Blake2s`.
- **S2-m5 and S2-m6: fixed.** The header now records the following:
  - `iv` and `sigma` are leanerVM's mechanical dump of the RFC 7693 text (Appendix D;
    `scripts/dump-blake2s.py constants`; RFC text SHA-256
    `c943754888364fe29bbd0bb3c71c6658ef392371497eaa4a9d9dde015b0721e5`, which equals
    `sha256sum probes/s2/rfc7693.txt`), re-checked by `iv_spec` and `sigma_perm`;
  - the compression function's commit, paths and lines;
  - that `iv` and `sigma` moved namespace;
  - the licence file.

  The licence is `RecursionFast/Contract/Hash/LICENSE-leanerVM`. `cmp` shows it is byte-identical
  to leanerVM's `LICENSE` at `485d0465`.
- **S2-m7: fixed.**
  - `block` now writes `b (4 * j.val)`, …, `b (4 * j.val + 3) <<< 24`.
  - `rotr`'s docstring adds "(BLAKE2s uses `n ∈ {16, 12, 8, 7}`)".
  - **Meaning is identical.** `logs/S2/fix/blockterm.lean` dumps the kernel terms of `block`,
    `rotr`, `compress`, `compressInput`, `blake2s` and `blake2s256` before and after the edit. The
    two dumps are textually identical: `terms.diff` is empty. Every KAT passes unchanged.
- **S2-m8: fixed.** Added `highCounter_kat`, 1.4 s.
  - It checks `compress` at `t = 2^32 + 3`, against the reviewer's independent Python model of
    RFC §3.1–§3.2. I re-ran the model; it equals hashlib on 609 inputs.
  - `maxCounter` (`t = 2^64 − 1`) stays in `probes/s2/HighCounter.lean`.
- **S2-m9: fixed.** `probes/s2/SelfTest.lean` now ends in `#guard grand == blake2sRes`, the RFC
  7693 Appendix E grand hash.
  - It is evaluated, never a kernel theorem.
  - It passes silently in 2.8 s (`logs/S2/fix/selftest.log`).
  - A false `#guard` does fail the file: `#guard blake2s256 [] == []` reports "did not evaluate
    to `true`".
- **S2-m10: recorded** as **S2-A2** in `docs/DESIGN-AMENDMENTS.md`: the design's `blake2s(·)` is
  `RecursionFast.blake2s256`.
- **S2-m11: fixed.**
  - The committed differential test is the reviewer's deterministic grid, `probes/s2/Diff.lean`
    and `probes/s2/diff.py`. It covers `kk ∈ {0, 1, 2, 31, 32}`, `nn ∈ {1, 2, 3, 16, 31, 32}`,
    and lengths 0–260 plus 319–321, 511–513, 1023–1025, 4096 and 4097.
  - `probes/s2/README.md` gives the one-line run command.
  - Re-run on the fixed spec: **8432 cases, 0 mismatches**, 19 s (`logs/S2/fix/diff.log`).
  - My earlier random test (`logs/S2/diff-hashlib.*`, 306 cases) is superseded and stays in
    `logs/` only.
  - CI wiring is Stage 6.
- **Also updated:** `probes/s2/Axioms.lean` audits the library module as well.

### Mutants against the CI vectors (`probes/s2/Mutants.lean`, re-run: 48 s, `logs/S2/fix/mutants.log`)

| Mutant | What is wrong | Passes (proved) | Killed by |
|---|---|---|---|
| `heldBack` | an extra empty final block when `\|d\|` is a multiple of 64 above 64 (`if \|d\| ≤ 64 then 0 else \|d\| / 64` non-final blocks) | the seven original KATs (`hb_abc` … `hb_nn16`) | **`len128_kat`** (`hb_len128`) and **`kk1_kat`** (`hb_kk1len64`) |
| `padNN` | key padded with `64 − nn` zeros, not `64 − kk` | `keyed_empty_kat`, `keyed_65_kat` (`pn_keyed_*`); every unkeyed vector (`pn_unkeyed`, `rfl`) | **`kk1_kat`** (`pn_kk1len64`) |
| `wordTrunc` (new in the fix pass) | output truncated to whole words, `4⌈nn/4⌉` bytes | every vector with `nn ∈ {16, 32}` (`wt_32`, `wt_16`, `rfl`) | **`nn1_kat`** (`wt_nn1`) |

Every mutant now fails at least one vector of `Controls/Blake2s.lean`.

### Checks after the fix pass

- **Build:** `lake build` (default targets) is green, 2093 jobs, no warnings. With the three new
  modules stale: spec 5.2 s, library 0.9 s, controls 47 s (`logs/S2/fix/build.log`).
- **Controls timing:** `/usr/bin/time -v lake env lean RecursionFast/Controls/Blake2s.lean` takes
  **48.5 s** wall, 1.07 GB peak, at load average ≈ 1.9 (`logs/S2/fix/controls-time.log`).
  Synchronously traced, every theorem takes ≤ 5.2 s, and the new ones take 1.4–3.9 s
  (`logs/S2/fix/controls-trace-sync.log`). The budget is ≤ 60 s.
- **Line counts** (`logs/S2/fix/loc.log`):

  | File | Code before | Code after |
  |---|---:|---:|
  | spec | 67 | 68 (the `block` line is split for `j.val`) |
  | controls | 51 after golf | 52 |
  | library | — | 13 |

- **`#print axioms`** (`logs/S2/fix/axioms.log`):

  ```
  'RecursionFast.blake2s' depends on axioms: [propext, Quot.sound]
  'RecursionFast.blake2s256' depends on axioms: [propext, Quot.sound]
  'RecursionFast.Blake2s.block' depends on axioms: [propext, Quot.sound]
  'RecursionFast.Controls.Blake2s.len128_kat' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RecursionFast.Controls.Blake2s.kk1_kat' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RecursionFast.Controls.Blake2s.nn1_kat' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RecursionFast.Controls.Blake2s.kk1nn16_kat' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RecursionFast.Controls.Blake2s.highCounter_kat' depends on axioms: [propext, Quot.sound]
  'RecursionFast.Blake2s.rotr_eq_rotateRight' depends on axioms: [propext, Quot.sound]
  'RecursionFast.blake2s_length' depends on axioms: [propext, Quot.sound]
  'RecursionFast.blake2s256_length' depends on axioms: [propext, Quot.sound]
  ```

- **Axiom audit** (`scripts/AxiomAudit.lean` on the three modules, `logs/S2/fix/axiomaudit.log`):
  12, 27 and 5 declarations, **PASS**.
- **Probe audit:** `probes/s2/Axioms.lean` finds 0 declarations outside the allowed set.
- **Hygiene:** `scripts/check-hygiene.sh` reports OK.
- **Files touched in this pass:**
  - `Contract/Hash/Blake2s.lean` (header, a docstring, the `block` text);
  - `Contract/Hash/LICENSE-leanerVM` (new);
  - `Library/Blake2s.lean` (new);
  - `Controls/Blake2s.lean`;
  - `probes/s2/{Mutants,SelfTest,Axioms}.lean` and `probes/s2/README.md` (new);
  - `docs/DESIGN-AMENDMENTS.md` (Stage 2 section appended);
  - this file.

  No root file was touched, and nothing was committed.

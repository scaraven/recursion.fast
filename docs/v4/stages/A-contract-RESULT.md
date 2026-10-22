# Stage A (v4, SROM): the trusted contract, its library and controls — RESULT

Status (2026-10-22): **done**. `lake build` is green (1,262 jobs). The axiom audit passes on all 43
`RecursionFast.*` modules: `propext`, `Classical.choice` and `Quot.sound` only. Nothing in the
built targets uses `sorry`, `native_decide` or a code-changing attribute; the only attributes are
`@[simp]` and `@[inline]`. The trusted contract has **355 code lines** (v3: 292; target ≤ 370,
cap 500). Every item of the stage, the stretch goal included, is built:
- the library (the bridge from `runSeq` to `runLog`, the reference signer and its theorem, the
  witness-sending certificate under every key, the word-level badge path proved equal, V4-8's
  composition walk, C-m1's impossibility, an executable signer);
- the controls, with a positive and a negative control for every trusted definition;
- the speed measurements.

The amendments V4-A3, V4-A4 and V4-A7 are implemented (§7).

Branch `v4/srom-rules`, worktree `/home/devops/Verified-zkEVM/recursion.fast-v4`. Nothing is
committed (the orchestrator commits).

## 0. Environment (read this before building)

The shared package tree `/home/devops/CambridgePQ/recursion.fast/contract/.lake/packages` is
**not built any more**: every package's `.lake` directory there is empty (modified at 13:44 on
2026-10-22). With it, any import of Mathlib would rebuild Mathlib inside the read-only tree. I did
not touch that tree. Instead:

- `leanerVM/.lake/packages` holds the same revisions as this repository's manifest for every
  package (Mathlib `d13f23b`, batteries `f2effa3`, …; checked against each `git rev-parse HEAD`)
  and is built. I copied it with rsync (9.0 GB, 43 s) to
  `recursion.fast-v4/.lake/pkgs-local/`, which is private and gitignored.
- I repointed the local, gitignored symlink `recursion.fast-v4/.lake/packages` to that copy. The
  manifest and the `[[require]]` blocks are unchanged.
- Other worktrees, stage B's included, will hit the same empty tree.

## 1. What was built, file by file

### Contract (`RecursionFast/Contract/`, trusted; code lines by `scripts/loc.py`, `logs/A-loc-contract.log`)

| File | v3 | v4 | What changed |
|---|---:|---:|---|
| `Contract.lean` | 8 | 9 | Reading order: Hash, Relation, **Signature**, Oracle, Security, Machine, Extractor, Tree, Certificate. |
| `Hash/Blake2s.lean` (+ `LICENSE-leanerVM`) | 68 | 68 | Code byte-identical. One header sentence changed: v3 said BLAKE2s is "the instantiation of the oracle", which is false in v4. |
| `Relation.lean` | 25 | 38 | `Trace`, `Sig`, `Signed`, `Wit` with signed children, `Rel (acc)`. Tags `T W K M` added and `R` deleted. `queryCap = 2^20` (V4-A3). |
| `Signature.lean` (new) | — | 31 | The byte layouts of BRIEF §4.2 exactly: `traceBytes`/`traceDigest`, `msgDigits`/`wotsDigits`, `wotsStep` (F), `wotsChain`, `wotsEnds`, `wotsLeaf`, `sigNode`, `sigRoot`, `SigOk`. |
| `Oracle.lean` | 22 | 24 | `runSeq` added, with exact consumption (V4-A3). `run` deleted: `Vb` was its only trusted user, and it moved to `Library/Oracle.lean`. |
| `Security.lean` | 33 | 33 | Verbatim. Header updated (V4-1; O-25 is now closed by the deployment). |
| `Machine.lean` | 62 | 62 | Verbatim; header note only. |
| `Extractor.lean` | 35 | 51 | Tape unchanged (`logWords` factored out; the tape is definitionally the same). The output decoder is new: a strict reader in `StateT (List Word) Option` (`readNat`, `readBytes`, `readString`, `readDigest`, `readList`, `readEntry`, `readTrace`, `readSig`, `readSigned`, `readWit`, `decodeWit`). `outCap` adequacy recomputed (header). |
| `Tree.lean` | 8 | 8 | Verbatim; header note only. |
| `Certificate.lean` | 31 | 31 | `Submission` with `vk` in `V` and `P`, `Submission.acc` (conjunct order of V4-A3), `Certificate` with `∀ vk` in `secure` and `complete`, `Declared`, `CertificateR`. `blake2sOracle` and `Vb` deleted. |
| **Total** | **292** | **355** | |

Every trusted definition has a docstring saying what it means. Module headers give the reasons
and cite V4-n, V4-An and the v3 ids they inherit.

### Library (`RecursionFast/Library/`, untrusted, kernel-checked; 1,780 code lines, 220 theorems)

- **Ported**:
  - Unchanged from v3: `Blake2s`, `Security`, `PaperTheorem`, `Completeness`, `Machine`, `Tree`.
  - `Oracle` now defines `OProg.run`, with `runLog_eq_run`, `runLog_queries` and `run_bind`.
  - `Words` covers the v4 output format: `sigWords`, `signedWords`, `witWords`, `Wit.Fits`, a
    round-trip lemma per reader, `decodeWit_witWords`, `readWit_witWords` (trailing words are
    ignored), `enc64_inj`, `unpack_packBytes`, and the linear twins `packFast`, `witWordsF`.
- **`Trace`** (new):
  - `OProg.runLog_of_runSeq`: if `runSeq tr p = some b`, every entry of `tr` is in `L`, and `L` is
    functional, then `runLog L p = some b`. This is the bridge the composition uses.
  - `runSeq_queries`: the honest trace.
  - `runSeq_map_fst` and `runSeq_length_le`: an accepted functional trace is the verifier's query
    sequence, so it has at most `qV` entries.
  - `traceBytes_inj` and `traceDigest_eq`: equal digests of two accepted traces mean equal traces
    or a `Collision`.
- **`Signer`** (new):
  - `chainStart` is V4-A4's derivation, `BLAKE2s-256 keyed by seed of (0x53 ‖ enc64 j ‖ i)`.
  - `pubEnds`, `node`, `pk`, `sibs`, `authPath` and `sign` are defined for **every** secret
    function `sk`.
  - **`sigOk_sign`**: `SigOk (pk sk) m (sign sk j m) = true` for `j < 2^16`. It is proved
    symbolically from `wotsChain_add`, `wotsDigits_le`, `wotsDigits_length` and `sigRoot_sibs`;
    no hash is evaluated.
- **`SignerFast`** (new): the executable reference signer.
  - `chainStartF = chainStart` goes through `blake2sKeyedB`, the keyed path at word level.
  - `buildTree` computes the tree once; `buildTree_get` says entry `k` of level `t` is
    `node sk t k`.
  - `Tree.pk_eq`, `Tree.sign_eq` and `Tree.sigOk_sign`.
  - The CLI is in §5.
- **`Blake2sFast`** (new): `compressF` (words in registers, the schedule written out) and
  **`compressF_eq : compressF = compress`**. The proof is symbolic:
  - eight `mixᵢ` lemmas by `rfl`;
  - a round, by rewriting;
  - `sigma.foldl` unrolled.

  The file also has the byte-array message path `blockAt`/`loopB`/`outBytes` and
  **`digestB_eq : digestB b = blake2sDigest b.data.toList`**.
- **`Fast`** (new): a twin of every hash on the badge path, each proved equal to the contract's
  function:
  - `traceDigestF`, `SigOkF`, `wotsStepF`, `wotsChainF`, `wotsLeafF`, `sigNodeF`, `sigRootF`,
    `chainStepF`, `chainEndF`, `leafStmtF`, `nodeStmtF`;
  - **`Submission.accF` with `accF_eq : S.accF = S.acc`**.

  All of them build byte arrays (`pushU64`, `pushDigest`); none goes through lists.
- **`WitnessSending`** (v3's argument under v4):
  - `check vk c π` decodes `π` as a witness and checks `Rel (acc vk)` recursively, with every
    child accepted. A child needs: its proof within `proofCap`, its queries within `queryCap`, a
    valid signature on its trace's digest, an **empty trace** (it asks no query, and exact
    consumption applies), and its proof accepted.
  - Decoding is strict (canonical encoding); `check` runs the linear twins and the word-level
    hashes, and `check_eq` restates it with the specification functions.
  - `acc_eq`, `check_sound`, `check_canonical`, `fits_of_rel`, `check_encode`, `check_iff`.
  - `ks vk`, `complete vk` (δ = 0), and `computes`: v3's 21-statement copy program, 8 steps per
    word.
  - **`certificate : Certificate submission`**: it holds under every key.
- **`SigTrust`** (new, C-m1, V4-A7 (a)). `Vsig vk c π` accepts a proof that carries a
  `vk`-valid signature of `c`.
  - **`sigTrust_kstate_iff`**: under `pk sk`, `Vsig` has a knowledge state for some extractor
    iff every digest has a witness.
  - `sigTrust_extracts` and `sigTrust_no_kstate_none`.
  - The twin `sigTrust_ks_of_unsignable`: under a key for which no signature verifies, the same
    verifier is knowledge-sound at ε = 0.
- **`Compose`** (new, V4-8, the stretch goal; finished and in the default target). Its inputs are
  a `KState` for `Rel (S.acc vk)`, a functional log `L` with at most `logCap` entries and `μ L < 1`,
  `2^r` leaves with digests `leafStmt hᵢ n` (`n ≤ chainCap`), and a root signed proof accepted
  by `S.acc vk`.
  - The computable `walk` returns one of three outcomes:
    - `Outcome.starts`: `sᵢ` with `chainEnd sᵢ n = hᵢ` for every leaf;
    - `Outcome.collision`: a `Collision`, two different byte strings with one BLAKE2s digest;
    - `Outcome.forgery`: a signed proof met on the walk whose `SigOk` is true and whose trace is
      not contained in `L`.
  - `compose` is the same result as a proposition.
  - Helpers: `extract` (it computes the witness from `S.E`, not by choice) and
    `treeRoot_append`.
  - A helper agent wrote the proof against statements I fixed. I checked that the statements are
    unchanged and that the file builds; the audit is clean.

### Controls (`RecursionFast/Controls/`; 2,029 code lines, 292 theorems)

The table in §3 lists every trusted definition with its positive and negative control. New files:
`Signature.lean`. Rewritten for v4: `Relation`, `Oracle` (runSeq), `Security`, `Extractor` (the
format KATs), `WitnessSending`, `Certificate` (the key quantifier) and `Backdoor`. Unchanged:
`Blake2s`, `Potential`, `Completeness`, `Machine`, `Tree`, and `LogScan` (two lemmas adapted to
the new decoder).

### Scripts

- `scripts/loc.py`: v3's, unchanged.
- `scripts/AxiomAudit.lean`: v3's, retargeted to v4's three roots. Run it with
  `lake env lean --run scripts/AxiomAudit.lean` (log in `logs/A-axiom-audit.log`).
- `scripts/speed/` holds a separate Lake configuration, `lakefile.toml`, used with
  `lake -f scripts/speed/lakefile.toml build speed signer` from the repository root. It
  duplicates the main `[[require]]` blocks and adds two `[[lean_exe]]` targets, so the main
  lakefile stays unchanged.
  - `Speed.lean`: the badge-path probe.
  - `Signer.lean`: the signer CLI.
  - `signer_ref.py`: an independent Python reference of BRIEF §4.2 and V4-A4, using hashlib
    only.

`lakefile.toml` is unchanged. `RecursionFast.lean` now imports Contract, Library and Controls,
so the default target `RecursionFast` builds all three. The lakefile's header comment still says
"empty skeleton"; it is outside `[[lean_lib]]`, so I left it for stage D.

## 2. Build times (this VM: 32 vCPU, QEMU virtual CPU; Mathlib cached in the private copy)

| Build | Wall time | Log |
|---|---:|---|
| Cold (this package's outputs deleted, all 1,262 jobs checked) | **2 min 55 s** (user 7 min 33 s) | `logs/A-build-cold.log` |
| No-op `lake build` | 2.7 s | `logs/A-build-noop.log` |
| Edit of a comment in `Contract/Certificate.lean` | about 5 s (1 module rebuilt; Lake 5 hashes outputs) | `logs/A-build-incremental.log` |
| Contract alone | 20 s | `logs/A-contract-build1.log` |

The cold build's long poles are the kernel known answers:

| Module | Time | What it evaluates |
|---|---:|---|
| `Controls/Extractor` | 116 s | the 1,216-word node format KAT, decoded and encoded by the kernel; no hashing |
| `Controls/Relation` | 66 s | about 12 compressions |
| `Controls/Blake2s` | 57 s | v3's 25 compressions |
| `Library/Blake2sFast` | 27 s | `compressF_eq` |
| `Controls/Signature` and `Controls/Tree` | 22 s each | |

## 3. Controls: a positive and a negative control for every trusted definition

| Trusted definition | Positive | Negative |
|---|---|---|
| `iv`, `sigma`, `rotr`, `mix`, `round`, `initialState`, `compress`, `block`, `compressInput`, `blake2s`, `blake2s256` | `Controls/Blake2s`: `iv_spec`, `sigma_perm`, 12 KATs (RFC 7693, hashlib, leanVM); `Library/Blake2s`: `rotr_eq_rotateRight` | `flip_neg`, `key_neg`, `nn_neg` (v3) |
| `blake2sDigest`, `chainStep`, `chainEnd`, `leafStmt`, `nodeStmt`, `enc64`, `chainCap` | `chain1/2/16_kat`, `leafStmt_kat`, `nodeStmt_kat`, `leaf_at_chainCap`; `enc64_inj` | `start_ne_end`, `wrong_end`, `leaf_over_chainCap` |
| tags `C L N T W K M` | `tags_separate` (the 7 tags are distinct; each hash input starts with its tag) | `R` deleted; distinctness in `tags_separate` |
| `Trace`, `Sig`, `Signed`, `Wit`, `Rel` (leaf clause) | `leaf_at_chainCap` | `leaf_over_chainCap`, `wrong_end` |
| `Rel` (signed node clause) | **`node_of_two_leaves`**, `node_of_two_leaves_ref` (reference signer, symbolic) | `node_needs_statement`, `node_statement_mismatch`, `first_child_rejected`, `second_child_rejected`, **`child_other_key`**, **`child_trace_nonempty`** |
| `traceBytes`, `traceDigest` | `traceBytes_kat`, `traceDigest_layout`, `traceDigest_kat`, `traceDigest_empty_kat` (hashlib); `traceBytes_inj` | **`traceDigest_changed_answer`** (a changed answer gives another digest), `acc_changed_answer` |
| `wotsLen`, `msgDigits`, `wotsDigits` | `wotsDigits_ff`, `wotsDigits_zero`, `wotsDigits_order`; `wotsDigits_length`, `wotsDigits_le` | `sigOk_ots_length` (not 133 values) |
| `wotsStep`, `wotsChain`, `wotsEnds`, `wotsLeaf` | `wotsStep_layout`, `wotsStep_kat`, `wotsChain_two`, `wotsLeaf_length`; `wotsEnds_sign` | through `SigOk`'s negatives |
| `sigHeight`, `sigNode`, `sigRoot` | `sigNode_kat`, `sigRoot_bits`, `sigRoot_one`; `sigRoot_sibs` | `sigOk_path_length` (not 16 siblings) |
| `SigOk` | **`sigOk_sign`** (every `sk`, `j < 2^16`), `sigOk_sign_ref` | `sigOk_idx_out_of_range`, `sigOk_ots_length`, `sigOk_path_length`, **`sigOk_key_unique`**, `sigOk_other_key` |
| `OProg`, `runLog`, `queries`, `bind`, `Log` | `prog_queries`, `prog_runLog`, `prog_runLog'`, `prog_runLog_first` (v3) | `prog_runLog_miss`, `runLog_reads_log` |
| **`runSeq`** | `prog_runSeq`, `prog_runSeq'` (honest trace), `prog_runLog_of_runSeq` (bridge) | `prog_runSeq_swapped`, `prog_runSeq_short`, **`prog_runSeq_extra`** (exact consumption), `prog_runSeq_wrong_query`, `runSeq_reads_trace`, `ret_runSeq_nonempty` |
| `KState`, `KS`, `errorCap`, `logCap`, `Fintype Digest` | `ws_ks vk`, `ws_kstate_trivial`, `mono_control`, `rejectAll_ks`, `ks1`; Potential's `twoLucky_ks`, `collision_ks`, `v24_ks` (v3) | `queryThenAccept_ge_one`, `acceptAll_no_kstate_*`, `jumpAll_ge_one`, `oneQuery_not_KS`; Potential's `*_no_bool_kstate` (v3) |
| `failProb`, `CompleteWithError`, `completenessCap` | `ws_complete vk`, `grind_exact`, `grind128_complete`, `fixed_complete_half` (v3) | `grind127_not_complete`, `fixed_not_complete`, `rejectAll_not_complete` |
| `Word`, `clmul`, `XOp`, `XStmt`, `XProg`, `exec`, `run`, `memFor`, `size` | `Controls/Machine` (v3: `eval_kat`, `straight_run`, `count_run`, `poke_affine`, …) | `straight_short`, `count_short`, `mem_charged`, `poke_const`, `spin_run` |
| `toWord`, `ofLE`, `packBytes`, `bytesWords`, `logWords`, `extractorInput` | `extractorInput_kat` (v3, unchanged tape); `wordByte_packBytes`, `packBytes_wordsBytes` | `decodeWit_long_proof` (a length word past the output) |
| `Reader`, `readNat`, `wordBytes`, `readBytes`, `readString`, `readDigest`, `readList`, `readEntry`, `readTrace`, `readSig`, `readSigned`, `readWit`, `decodeWit` | `decodeWit_leaf_kat`, **`decodeWit_node_kat`**, `witWords_node_kat`, `decodeWit_trailing`; `decodeWit_witWords` (every fitting witness) | `decodeWit_bad_tag`, `decodeWit_empty`, `decodeWit_short_leaf` (strict), `decodeWit_long_proof`, **`decodeWit_long_trace`** (a malformed trace length, V4-A7 (c)), `decodeWit_short_sig` |
| `extractorBudget`, `outCap`, `progCap`, `Computes` | `ws_computes`, `ws_run_exact`, `halt_computes`, `scan_computes` (v3) | `ws_fuel_short`, `halt_not_ws`, `spin_computes_nothing`, `toolong_not_computes`, `enum_no_computes`, `scan_fuel_short`, `big_program_no_certificate` |
| `treeLevel`, `treeRoot` | `treeRoot_one…eight`, `treeRoot_recursive`, `treeRoot_kat`; `treeRoot_append` (Compose) | `treeRoot_order` |
| `Submission`, **`acc`** | `acc_leafSigned`, **`acc_query_at_cap`** (a signed one-entry trace with a query of exactly `queryCap` bytes), `ws_acc_leaf`; `accF_eq` | `acc_over_cap`, `acc_query_over_cap`, `deep_accepted_but_capped`, `acc_bad`, `child_other_key`, `child_trace_nonempty`, `acc_changed_answer` |
| `queryCap`, `proofCap` | `acc_query_at_cap`, `deepProof_check` (accepted within the cap) | `acc_query_over_cap`, `acc_over_cap`, `deep_accepted_but_capped` |
| **`Certificate`** (with `∀ vk`), `Declared`, `CertificateR` | `ws_certificate`, `ws_certificateR`, `choice_certificate`, `Backdoor.certified`; `sigTrust_ks_unsignable` (why `∀ vk` bites) | `fuel_low_claim`, `fuel_over_budget_claim`, `rejectAll_no_certificate`, `acceptAll_no_certificate`, `error_one_*`, `delta_one_*`, `fuel_over_budget_*`, `big_program_*`, **`sigTrust_no_certificate`**, `sigTrust_certificate_opens` |
| What the model does not exclude | `acc_rejects_all_certified` (an `acc` that accepts nothing is certified), **`Backdoor.backdoor`**: a verifier that compares the answer to the empty query with its public BLAKE2s is certified, and its `acc` accepts the 32-byte magic proof of every statement on the signed trace `[(empty, BLAKE2s(empty))]` | **`magic_needs_trigger`**: only on that trace, which the keyed service never signs (in the design, on paper) |

**About the `∀ vk` control** (the stage brief asked for it, or for a precise statement of why it
cannot be stated). It is stated, as `sigTrust_no_certificate`: a verifier that accepts any proof
carrying a `vk`-valid signature on the statement, with an extractor that returns nothing, is not
certified. With an arbitrary extractor, the strongest true statement is
`sigTrust_certificate_opens`, and Library's `sigTrust_kstate_iff` says the knowledge state exists
iff every digest has a witness. As with v3's accept-all verifier, no digest can be shown to lack
one, so it is the named extractor (`Computes`) that excludes it. The twin
`sigTrust_ks_unsignable` shows the quantifier is what does the work: under a key with no valid
signature the same verifier is knowledge-sound. That twin is stated for every such key, because
no such key can be exhibited without evaluating BLAKE2s.

## 4. Speed of the badge path (C9, C10, C-m3, V4-A7 (d))

Compiled and measured on this VM (`logs/A-speed-final.log`, `lake -f scripts/speed/lakefile.toml
build speed && .lake/build/bin/speed 7`):

| Function | Contract (reference) | Library twin (proved equal) | Speed-up |
|---|---:|---:|---:|
| `compress` (one compression) | 1,136 ns | `compressF` **280 ns** (232–280 across runs) | 4× |
| BLAKE2s-256 of 64 B (one block) | 6,316 ns | `digestB` 675 ns | 9× |
| BLAKE2s-256 of 1 MiB, per compression | 5,488 ns | `digestB` **402 ns** | 14× |
| `wotsStep` (43 B) | 6,131 ns | `wotsStepF` 659 ns | 9× |
| `traceDigest`, 2^16 queries of 100 B (9.2 MB) | 1,268 ms | `traceDigestF` **72 ms** | 17× |
| `SigOk`, valid signature (about 300 compressions) | 2.01 ms | `SigOkF` **0.23 ms** | 9× |
| `acc`, witness-sending root over two signed 2^10-step leaves (3 signatures) | 10.8–12.8 ms | `accF` 9.3–9.9 ms | — (see below) |

v3 measured about 5 µs per compression for the reference. That matches the 5.5 µs per block
here: the reference compression itself is about 1 µs, and the rest is the list-based message
path. The target of "about 1 µs or less" is met by the twins. The harness runs `accF`
(`accF_eq`), and its trusted share is about 0.23 ms per signature plus about 0.5 µs per 64 bytes
of trace.

The witness-sending `acc` barely improves because its own verifier dominates:
- `decodeF` of the 9,752-byte node proof takes 4.2 ms, and decode plus re-encode 8.0 ms, about
  0.4–0.8 µs per byte;
- the two 2^10-step chains (`chainEndF`, 594 ns per step) take 1.2 ms.

`Word` is `BitVec 64`, a `Nat` at run time, so words above `2^63` are bignums. This is the
submitter's code in the witness-sending entry (and the decoder on the liveness path), not the
trusted badge path. Open question 1 covers it.

**Signer**:
- `.lake/build/bin/signer` builds the whole key tree (2^16 keys, about 48 M compressions) in **57–62 s**
  (`logs/A-signer-time.txt`). The first, list-based version took 115 s.
- **Its output, `vk` and the 151 lines of one signature, is byte-identical to the independent
  Python reference `scripts/speed/signer_ref.py`**, which took 41 s. Seed `00…1f`, `j = 5`, the
  message being the empty trace's digest. This checks the byte layouts of BRIEF §4.2 and V4-A4
  end to end, against hashlib.

## 5. How to call the executable signer (V4-A4)

```sh
lake -f scripts/speed/lakefile.toml build signer
.lake/build/bin/signer <seed-hex, 32 bytes> <j < 65536> <message-hex, 32 bytes>
```

It prints one line each:
- `vk` (hex);
- `idx` (decimal);
- the 133 chain values and the 16 path digests (hex);
- `true` (its own `SigOkF` check).

The chain starts are `chainStartF seed`, proved equal to the contract-side reference `chainStart`
(V4-A4). The tree is `buildTree` (= `node`), and the signature is `Tree.sign` (= `Signer.sign`).
Stage B can turn it into a `[[lean_exe]]` of the main lakefile (root `scripts/speed/Signer.lean`).

## 6. Deviations from the BRIEF, with reasons

1. **`runSeq` requires exact consumption.** I implemented it before the stage C amendment arrived
   and reported it as a deviation; it is now V4-A3. Reason: with trailing entries allowed, `Rel`
   has witnesses with traces of every length, so `∀ w` completeness fails for every fixed-size
   node prover, the witness-sending one included (C-M3). `queryCap` and the conjunct order of
   V4-A3 are implemented too.
2. **The output decoder reads strictly.** v3 read missing words as `0` and capped the two child
   proof lengths at `proofCap`. With nested variable-length fields (traces), every declared
   length would need such a cap. Strict reading instead bounds everything decoded by the length
   of the output, and the decoder is linear-time in compiled code (C9). Consequence:
   `[0, s₁…s₄]` without the length word no longer denotes a leaf (`decodeWit_short_leaf`). No
   witness is lost, since `decodeWit_witWords` covers every fitting witness. The
   `child ≤ proofCap` check in the decoder is gone; `acc` still enforces it in `Rel`.
3. **The signature has fixed counts in the output format** (133 + 16 digests, no count words). A
   valid signature has exactly these, so every witness of `Rel` can be denoted.
4. **Names added to the trusted base**:
   - trace and signature: `traceBytes`, `msgDigits`, `wotsChain`, `wotsEnds`, `sigRoot`,
     `wotsLen`, `sigHeight`;
   - the output readers: `Reader`, `readNat`, `wordBytes`, `readBytes`, `readString`,
     `readDigest`, `readList`, `readEntry`, `readTrace`, `readSig`, `readSigned`, `readWit`;
   - `logWords`, which also serves the input tape.

   **Removed**: `wordByte`, `digestAt`, `bytesAt` (v3's decoder internals; `wordByte` is now in
   the Library), `run`, `tagRO`, `blake2sOracle`, `Submission.Vb`.
5. **`Hash/Blake2s.lean` header**: one sentence updated, code byte-identical. Machine, Tree and
   Security have header notes only.
6. **lakefile**: not edited. The default target already builds everything through
   `RecursionFast.lean`. The probe and signer executables use a separate config (`lake -f`), so
   the main lakefile keeps only its `[[lean_lib]]`, as the stage brief required.
7. **C-m1's control** uses a verifier that trusts a signature on the statement itself. The review
   sketched one that trusts "a signed trace agreeing with the oracle on one query"; the
   impossibility and the proof are the same, and this form is shorter.
8. **`Compose.Forgery`** records `SigOk` and "trace not contained in `L`". "Met on the walk"
   holds by construction of `walk`; it is not a field of the type.

## 7. Amendments V4-A3, V4-A4, V4-A7 (stage C)

- **V4-A3**: done.
  - Exact consumption: `runSeq`, with the controls `prog_runSeq_extra` and
    `ret_runSeq_nonempty`.
  - `queryCap = 2^20` in `acc`, with the controls `acc_query_at_cap` and `acc_query_over_cap`.
  - The conjuncts are ordered size, queries, `SigOk`, `runSeq`.
  - The Library lemmas the orchestrator asked for:
    - `traceBytes_inj` and `traceDigest_eq`: injectivity on accepted traces, a relation-internal
      fact because `queryCap < 2^64`;
    - `runSeq_length_le`: a functional accepted trace has at most `qV` entries.
- **V4-A4**: done.
  - `chainStart` uses tag `S`, with the seed as the BLAKE2s key, independent of the PRF key.
  - `SigOk` is unchanged.
  - The executable signer is in `SignerFast` with its CLI (§5), and it is cross-checked against
    Python.
- **V4-A7**: done.
  - (a) `sigTrust_kstate_iff` and its controls.
  - (b) `node_of_two_leaves` with the Lean signer, symbolic.
  - (c) The negatives:
    - another key: `child_other_key`, `sigOk_other_key`;
    - a changed answer: `traceDigest_changed_answer`, `acc_changed_answer`,
      `runSeq_reads_trace`;
    - `|ots| ≠ 133`: `sigOk_ots_length`;
    - a malformed trace length: `decodeWit_long_trace`, `decodeWit_short_sig`.
  - (d) The word-level twin and `accF_eq` (§4).

## 8. Open questions

1. **The witness-sending verifier's codec** costs about 0.4 µs per byte to decode, and about the
   same again to re-encode (§4): about 0.8 s for a 1 MiB witness-sending proof, above any `T_V`
   cap. This is fine for the smoke shape. A byte-level parser (little-endian lengths read with
   `UInt64`), proved equal to `decodeWit ∘ packBytes`, would remove it if stage B needs
   witness-sending entries at larger shapes.
2. **`Word = BitVec 64` is a `Nat` at run time** (a bignum above `2^63`). The extractor
   interpreter and `decodeWit` on the liveness path pay for it. Should stage B measure them? A
   `UInt64` twin of the decoder is possible; the machine's semantics are trusted and stay as
   they are.
3. **`KS`'s query bound quantifies over oracle functions** (`queries H`). A non-functional
   accepted trace, which needs a forged signature or a key whose secret the adversary holds,
   follows no oracle's path, so `qV` does not bound it (`runSeq_length_le` needs
   functionality). Honest signed traces are functional. Should the query bound be stated over
   answer sequences instead, a contract change, so that node circuits can be sized from `qV`
   alone? Or is it the submitter's business to bound their `V` on every answer sequence?
4. **`outCap = 2^24`** admits two children with `2^16` queries of up to 960 bytes each (with both
   proofs at `proofCap`). Since `queryCap = 2^20`, a verifier with long queries is not
   certifiable, because its node witnesses cannot be extracted (C-m11 calls this intended).
   Should the design document state the bound, as the Extractor header does?
5. **`Controls/Extractor` takes 116 s** of kernel evaluation of the 1,216-word node KAT. Keep it,
   since it is the format's known answer for the runner's Python twin, or replace it with a
   smaller symbolic control?
6. **The shared package tree is empty** (§0). Other stages need a built tree; my copy at
   `recursion.fast-v4/.lake/pkgs-local` can be reused, and the copy took 43 s.
7. **`Signer.chainStartF_eq` needs a non-empty seed**, because RFC 7693 keys have 1–32 bytes.
   The service draws 32 bytes, so this is true for the deployment; I note it for the
   service's input validation.
8. **The probabilistic split of `Compose`'s forgery outcome** into an EUF-CMA forgery or a
   collision of trace encodings is on paper (V4-A8). It is stated in the module header.

# Stage A (v4) golf: proofs of `Library/` and `Controls/`, build time, badge-path speed

Golf agent, 2026-10-22/23, on `v4/srom-rules` at `85f0985` (uncommitted, as the stage protocol
asks). Scope: proofs only; no statement, definition value, public name or docstring claim was
changed, `Contract/` was not edited. Two helper agents (Opus) golfed disjoint file sets in
parallel: helper A `Library/{WitnessSending,Compose,Signer,SigTrust}` and the ported Library
files, helper B `Controls/{Backdoor,Certificate,Security,WitnessSending,Oracle,LogScan}` and the
ported Controls files. The session restart interrupted both before they reported; their edits
were intact and green (`logs/orch-verify-golf-partial.log`), and what they did is summarised
below from the diff. I did the build-time work and the remaining files, and checked everything.

## Results

| | before | after | log |
|---|---:|---:|---|
| Cold build, wall (`lake build`, this package's outputs deleted) | **3 min 26 s** | **1 min 18 s** | `logs/golf-A-build-cold-baseline.log`, `logs/golf-A-build-cold-after.log` |
| Cold build, user CPU | 7 min 25 s | 4 min 31 s | same |
| Sum of module times | 471 s | 263 s | same |
| No-op build | 2.7 s | 2.7 s | `logs/golf-A-build-noop.log` |
| Code lines, `Library/` + `Controls/` (`scripts/loc.py`) | 3,809 | 3,653 (−156) | |
| Total lines, same files | 6,245 | 6,106 (−139) | |
| Naked `;` in proofs | | 83 removed, 4 added (all moved `by rw [..]; omega` arguments) | |
| Contract code lines | 355 | 355 (untouched) | |

The two cold builds ran back to back on this VM (32 vCPU; load average 9 and 11 at their
starts); the baseline is `git archive 85f0985` built in a scratch directory against the same
package copy. `lake build` is green (1,263 jobs: one new module, `Controls/Hex`).

**Axiom audit**: `lake env lean --run scripts/AxiomAudit.lean` passes on every module
(`propext`, `Classical.choice`, `Quot.sound` only; `logs/golf-A-axiom-audit.log`). The count of
axiom-free theorems moves 154 → 152 only through auto-generated equation lemmas (`*.eq_1`): no
hand-written theorem changed its axioms (checked with `collectAxioms` on both trees).

**Statements**: `logs/golf-A-probes/StmtDump.lean` dumps kind, name and type (and a hash of the
value of every definition) of all 1,599 non-internal `RecursionFast.*` constants; before/after
dumps are in `logs/golf-A-probes/stmts-{before,after}.txt`. Every theorem and definition type is
unchanged; no definition value changed except `Compose.extract`, whose change is in proof terms
only (`.inl ⟨w, proof⟩`, `False.elim proof`; helper A, see below). Differences otherwise are
auto-generated `match_n`/`eq_1` helpers, the new `Controls.Extractor.nodeKat_fits`, and
`hex`, `hexBytes`, `hexDigit` moving module (same names). One private lemma was deleted
(`Compose.forall₂_append`, replaced by Mathlib's `List.rel_append`).

## Build time: what dominated and what changed

### `Controls/Extractor`: 131 s → 6 s (RA-m2)

Splitting the file into one file per known answer (`logs/golf-A-probes/golf-A-ext-split-*.log`)
showed one theorem, `decodeWit_node_kat`, costs about 93 s; everything else is under 2 s,
including `witWords_node_kat` (the encoder on the 1,216-word node, 2 s) and
`decodeWit_short_sig` (the decoder over all of `nodeKatWords.dropLast`, 1.4 s). So decoding is
not what is slow. What is slow is `decide`'s comparison of the decoded witness with `nodeKat`:
the 302 digests come out as `Vector.ofFn fun i => b.getD i 0` over lazily unpacked words, and the
kernel forces and compares every byte through `Array`'s decidable equality (micro-benchmarks:
about 0.3 s per decoded digest compared as a vector, 0.14 s as a list).

`decodeWit_node_kat` is now `witWords_node_kat ▸ decodeWit_witWords nodeKat nodeKat_fits`,
the fix RA-m2 proposes. The statement is unchanged. The kernel still evaluates the node format
word by word, as the encoder KAT `witWords_node_kat` (the runner's reference), and still runs the
decoder's field boundaries over these words (`decodeWit_short_sig`); the bytes of the decoded
digests follow from the round trip proved for every fitting witness. `nodeKat.Fits` is now a
lemma (`nodeKat_fits`, six `decide`/`rfl` per child), shared with `decodeWit_trailing`, which
becomes one line. I did not take RA-m2's second suggestion (restate `decodeWit_short_sig` on the
signature words alone): it changes a statement, and the control costs 1.4 s.

### `Controls/Relation` 83 s → 21 s, `Controls/Signature` 24 s → 9 s: hash KATs through the twins

Each hash known answer (`chain1/2/16_kat`, `leafStmt_kat`, `nodeStmt_kat`, `start_ne_end`,
`node_statement_mismatch`; `traceDigest_kat`, `traceDigest_empty_kat`,
`traceDigest_changed_answer`, `wotsStep_kat`, `sigNode_kat`) keeps its statement on the
contract's function and now reads `rw [← chainEndF_eq]` (or `leafStmtF_eq`, `nodeStmtF_eq`,
`traceDigestF_eq`, `wotsStepF_eq`, `sigNodeF_eq`) and then `decide +kernel`. The kernel then
evaluates the word-level twin, proved equal to the contract's function symbolically in
`Library/Fast.lean`, instead of the list-based reference: `chain16_kat` alone went from about
24 s to 5–11 s depending on load (`logs/golf-A-probes/golf-A-rel-split.log`). The theorem proved is the
same, so nothing is weakened; what changes is which of two provably equal programs the kernel
runs. `Controls/Signature` imports `Library/Fast` for this. **Orchestrator's choice**: if the
layout KATs should evaluate the contract's own code, revert these twelve proofs to
`by decide +kernel` (about 60 s of CPU back; `Relation` would again be the long pole).

`Controls/Blake2s` (49 s, v3's KATs of the trusted hash) is deliberately unchanged: it is the
direct test of the contract's BLAKE2s, and the keyed and short-digest variants have no twin.

### `Controls/Hex` (new, 8 code lines): `hex` no longer waits for the BLAKE2s KATs

`Signature`, `Relation` and `Tree` imported `Controls/Blake2s` only for `hex`, so the chain
`Blake2s (50 s) → Signature → Relation → Certificate` was the critical path. `hexDigit`,
`hexBytes` and `hex` moved verbatim (same namespace `RecursionFast.Controls.Blake2s`, same names,
same import `Contract.Hash.Blake2s`, identical value hashes) to `Controls/Hex.lean`;
`Controls/Blake2s` imports it and keeps `hex_pos`; the three importers import `Hex`. Now
`Controls/Blake2s` runs beside the Library instead of before the Relation controls. One header
sentence of `Controls/Blake2s` points to the new file. **Orchestrator's choice**: this is a move
of three v3 definitions to a new module (44 modules instead of 43), not a proof golf; it is
self-contained and can be dropped.

### Not changed, with the reason

- `Library/Blake2sFast` (23 s): `initialState_eq`'s `rfl` takes about 6 s and `compressF_eq`
  about 2 s of tactic and 3 s of kernel (`set_option profiler`, `Elab.async false`); the
  definitions themselves take about 6 s (typeclass inference and `get_elem_tactic` on literal
  indices). `ext`/`interval_cases`/`simp` alternatives for `initialState_eq` either time out in
  `whnf` or leave the `Vector.set (h ++ iv)` chain unsolved; since theorems elaborate in
  parallel, the gain would be a few seconds. Left as is.
- `Controls/Tree` (v3-identical; 25 s → 17 s only from the import change): its two KATs could go
  through `nodeStmtF_eq`, but `treeRoot` would have to be unfolded first and the module is off
  the critical path.

## Execution speed of the badge path

No definition on the badge path changed (`Blake2sFast`, `Fast`, `accF`, `Contract/`: value hashes
identical), so the RESULT's numbers stand. I looked for a clear speed-up of the twins' message
path with a standalone compiled copy of `compressF`, `blockAt`, `loopB`, `outBytes`, `digestB`
(`logs/golf-A-probes/TwinVariants.lean`, `leanc -O3`; `logs/golf-A-speed-variants.log`):
`compressF` about 250 ns, `digestB` of 64 B about 730–850 ns, of 1 MiB about 530 ns per block
(this run, a loaded VM). `outBytes` costs about 220–250 ns of the single-block figure; it
already compiles to a presized array and 32 pushes. The obvious rewrites are slower:
`Vector.ofFn` for the output bytes (750–920 ns), a full-block fast path for `blockAt` with
`Vector.ofFn` (1.0–1.8 µs per 64 B, 880 ns per block of 1 MiB). I found no clear speed-up that
keeps the equality proofs, and made none.

## Per file

Lines (total, code) from `scripts/loc.py`; module time from the two cold-build logs.

| File | total | code | module time (s) |
|---|---:|---:|---:|
| `Controls/Backdoor.lean` | 263 → 229 | 184 → 150 | 3.9 → 3.6 |
| `Controls/Blake2s.lean` | 160 → 150 | 52 → 47 | 50.0 → 49.0 |
| `Controls/Certificate.lean` | 261 → 236 | 160 → 135 | 4.4 → 4.4 |
| `Controls/Completeness.lean` | 190 → 190 | 120 → 120 | 3.9 → 3.8 |
| `Controls/Extractor.lean` | 244 → 246 | 128 → 124 | **131.0 → 6.1** |
| `Controls/Hex.lean` (new) | 0 → 23 | 0 → 8 | — → 0.8 |
| `Controls/LogScan.lean` | 401 → 399 | 293 → 291 | 7.6 → 7.3 |
| `Controls/Machine.lean` | 203 → 200 | 115 → 112 | 5.0 → 4.0 |
| `Controls/Oracle.lean` | 107 → 107 | 43 → 43 | 6.0 → 7.2 |
| `Controls/Potential.lean` | 624 → 624 | 448 → 448 | 7.0 → 7.7 |
| `Controls/Relation.lean` | 348 → 356 | 193 → 201 | **83.0 → 21.0** |
| `Controls/Security.lean` | 221 → 218 | 102 → 99 | 3.4 → 3.3 |
| `Controls/Signature.lean` | 154 → 163 | 66 → 75 | **24.0 → 9.2** |
| `Controls/Tree.lean` | 55 → 55 | 22 → 22 | 25.0 → 17.0 |
| `Controls/WitnessSending.lean` | 169 → 159 | 103 → 93 | 3.9 → 4.1 |
| `Library/Blake2s.lean` | 34 → 34 | 13 → 13 | 0.9 → 0.8 |
| `Library/Blake2sFast.lean` | 242 → 242 | 153 → 153 | 23.0 → 23.0 |
| `Library/Completeness.lean` | 102 → 100 | 63 → 61 | 3.3 → 3.3 |
| `Library/Compose.lean` | 243 → 224 | 154 → 136 | 5.4 → 5.8 |
| `Library/Fast.lean` | 210 → 203 | 128 → 121 | 3.5 → 3.4 |
| `Library/Machine.lean` | 169 → 168 | 113 → 112 | 3.3 → 3.2 |
| `Library/Oracle.lean` | 55 → 55 | 29 → 29 | 1.8 → 1.9 |
| `Library/PaperTheorem.lean` | 160 → 157 | 113 → 110 | 5.5 → 6.3 |
| `Library/Security.lean` | 269 → 269 | 166 → 166 | 4.3 → 4.6 |
| `Library/SigTrust.lean` | 91 → 86 | 45 → 40 | 3.3 → 3.0 |
| `Library/Signer.lean` | 145 → 137 | 73 → 65 | 4.7 → 5.4 |
| `Library/SignerFast.lean` | 167 → 164 | 99 → 96 | 4.2 → 4.1 |
| `Library/Trace.lean` | 170 → 154 | 110 → 94 | 4.3 → 3.7 |
| `Library/Tree.lean` | 55 → 55 | 33 → 33 | 2.2 → 2.3 |
| `Library/WitnessSending.lean` | 386 → 364 | 252 → 228 | 5.5 → 4.9 |
| `Library/Words.lean` | 347 → 339 | 236 → 228 | 4.0 → 4.2 |
| **Total** | **6,245 → 6,106** | **3,809 → 3,653** | **471 → 263** (sum) |

Module times under 10 s vary by about ±1 s between runs (machine load); `Relation` and
`Signature` grew in lines because each KAT now has a `rw` line before its `decide +kernel`.

### What changed, file by file

**Mine.**
- `Controls/Extractor`: `decodeWit_node_kat` from the encoder KAT and the round trip;
  `nodeKat_fits` (new lemma); `decodeWit_trailing` one line (`congrArg (Prod.fst <$> ·)`).
- `Controls/Relation`: the seven hash KATs through the twins (above); `child_other_key` and
  `child_trace_nonempty` as `fun h => by simpa [acc_eq, …] using h.2.1`; the `Blake2s` import
  becomes `Hex`.
- `Controls/Signature`: the five hash KATs through the twins; `sigOk_other_key` is
  `Bool.eq_false_iff.mpr fun h => hne (sigOk_key_unique h h')`; imports `Library/Fast` and `Hex`.
- `Controls/Blake2s`, `Controls/Tree`, `Controls/Hex`: the `hex` move (above).
- `Library/Words`: `enc64_length`, `wordBytes_length` are `List.length_ofFn`; `enc64_inj` one
  `rw` chain instead of `have` + `rwa`; `unpack_packBytes`'s second goal one `rw` (no detour
  through two `have`s); `decodeWit_witWords` a term
  (`List.append_nil _ ▸ congrArg (Prod.fst <$> ·) (readWit_witWords w h [])`).
- `Library/Trace`: `runLog_of_runSeq` and `runSeq_map_fst` read the `if` of `runSeq` with
  `Option.ite_none_right_eq_some` and `obtain ⟨rfl, h⟩` instead of `split`/`rename_i`/`subst` and
  a dead `cases h` branch; the `find?`-is-some step of `runLog_of_runSeq` and `runSeq_length_le`
  is `Option.isSome_iff_exists.mp (List.find?_isSome.mpr …)` instead of a `cases … with` block;
  `runSeq_length_le` ends in one `simpa` with `Eq.trans_le`; `traceBytes_inj`'s two length cases
  one `simpa` each (no `omega`, no `;`); `traceBytes_cons` is `List.flatMap_cons ..`;
  `traceDigest_eq` is `(em _).imp_right …`.
- `Library/Fast`: `wotsStepF_eq`, `wotsLeafF_eq`, `sigNodeF_eq`, `chainStepF_eq`,
  `leafStmtF_eq`, `nodeStmtF_eq` each one `simp […]` instead of a `rw` chain followed by `simp`;
  `foldl_pushDigest_data`'s step one `simp`.
- `Library/SignerFast`: `levelUp_get` reads entry `k` with `Array.getElem?_eq_getElem` and
  `Array.getElem_ofFn` and uses `hl` directly (the `hl'` detour through `getD`/`getElem?` and two
  `have`s are gone); `Tree.sigOk_sign` a term (`Tree.pk_eq sk ▸ Tree.sign_eq … ▸ …`).

**Helper A** (from the diff).
- `Library/WitnessSending`: `check_canonical` and `check_sound` share one private
  `exists_of_check` (they had duplicated the whole case split), and `check_iff` is
  `⟨exists_of_check, …⟩`; `size_encode`, `decodeF_eq`, `acc_eq`, `complete_perfect` terms;
  `check_encode` one `cases w <;> simp`; `runSeq_ret_eq` by `rfl` per case; `unfold … ; simp
  only` and `rw …; simp only` pairs merged in `extractorInput_eq`, `pre_mem`, `ext_run`,
  `computes`; `intro … rfl` for a `subst`.
- `Library/Compose`: proofs inside `walk` and `extract` as `▸`/`Option.some.inj`/`hex.elim`
  terms (the computational content of both is unchanged); `forall₂_append` replaced by Mathlib's
  `List.rel_append`; `treeRoot_of_iterate` one `rw` chain instead of a `le_total` split;
  `iterate_treeLevel_append`, `length_iterate_treeLevel_pow`, `treeRoot_map_split` shorter.
  No statement touched.
- `Library/Signer`: `sigRoot_sibs` without the `hup` restatement (`congr 1` on the rewritten
  goal); `wotsEnds_sign` one `conv_rhs`; `sigOk_sign` one anonymous constructor.
- `Library/SigTrust`: `sigOf_sigProof` two lines; `Nat.two_pow_pos 64`; `k.empty ▸ one_pos`;
  `sigTrust_ks_of_unsignable` without a dead branch.
- `Library/Completeness`, `PaperTheorem`, `Machine`, `Security`, `Tree`: `by`-blocks that were
  one `refine`/`rw`/`exact` turned into terms (`exists_consistent`, `failProb_le_one`, the six
  `exec_*` step lemmas as `Nat.add_comm m 1 ▸ rfl`, `unfold run; simp only` merged).

**Helper B** (from the diff).
- `Controls/Backdoor`: `runSeq_V` one `rcases` and one `by_cases … <;> simp` (was two copied
  `match` arms); `acc_eq` a term; `check_sound`, `check_encode` through `← acc_eq` in `simp`;
  `boolState`'s `empty`/`step` terms (`List.forall_mem_append`); `bounded` without the
  `Subsingleton` instance; `certified.cap` reuses `WitnessSending.certificate.cap`;
  `decode_magic` without `generalize`; `magic_needs_trigger` with `rintro`.
- `Controls/Certificate`: `Echoice_eq` with `split_ifs` (no nested `split`/`rename_i`);
  `choice_certificate` rewrites `Echoice` to `E` and reuses `certificate`; `sigTrust_*` and
  `big_program_no_certificate` terms; `big_secure`, `big_complete`, `big_computes`,
  `acc_rejects_all_certified` shorter; `by simp [extractorBudget]` → `by decide` where the goal
  is closed.
- `Controls/WitnessSending`: `appended_rejected` from `check_iff` (one decode instead of two);
  `Bool.eq_false_iff` instead of `cases h : … · rfl`; `cases hd ▸ hd'` for `rw … at; cases`.
- `Controls/Security`: `jump` facts with `ite_eq_left`/`ite_eq_right`; `queryThenAccept_ge_one`
  without `by_contra`; `ks1.final` with `obtain rfl`.
- `Controls/LogScan` (`words_eq_iff`, `decode_outW`), `Controls/Machine` (`spin_run` matches on
  `f - 1` directly).
- Not reached (unchanged): `Controls/Oracle`, `Potential`, `Completeness`.

## Trusted code (`Contract/`): proposal only, not applied

1. `Contract/Extractor.lean`, `wordBytes`: `def wordBytes (w : Word) : List UInt8 := enc64 w.toNat`
   (checked: `example (w : Word) : wordBytes w = enc64 w.toNat := rfl`). Same line count; the
   output's bytes are then visibly the 8-byte little-endian encoding already used for every
   length the contract hashes, and one formula fewer is trusted twice. `Library/Words`'
   `ofLE_wordBytes` would read `rw [wordBytes, ofLE_enc64, …]`.

Nothing else in the contract is shorter with identical meaning without changing how a decision
is computed (for example, `SigOk` as one `decide` of a conjunction would be one line shorter but
is a different term). RA-m3's `abbrev Trace := Log` is the reviewer's.

## Declined or noted

- Unused declarations, kept (removal is not golf): `Fast.pushAll`, `pushAll_data`,
  `Blake2s.digestL`, `digestL_eq` (no user in `RecursionFast/` or `scripts/`).
- `OProg.runLog_eq_run` (`Library/Oracle`): the `find?`-is-some rewrite saves one line only.
- `SignerFast.levelsFrom_get`: its two `u = 0` cases are duplicates, but merging them needs a
  helper lemma or `<;>` over different goals.
- No `@[simp]` added, no `set_option`, no `native_decide`, no attribute; lines ≤ 100 chars.

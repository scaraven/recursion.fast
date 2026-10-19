# V3-S1 golf: Library and Controls of the v3 contract (Stage V3-S1)

The golf agent wrote this on 2026-10-19, on branch `v3/s1-contract`, over the implementer's
uncommitted tree. Nothing is committed.

**What changed.** Only proofs, in four library files (`Library/Oracle`, `Security`, `Words`,
`WitnessSending`) and five control files (`Controls/Relation`, `Security`, `Certificate`,
`Extractor`, and one blank line in `Machine`).

- **Unchanged.** No theorem statement, definition, definition body, import or docstring changed,
  and no public declaration was added, removed or renamed. The trusted contract
  (`Contract.lean`, `Contract/*.lean`, `Hash/Blake2s.lean`) is byte-identical, still 320 code
  lines, so `scripts/olean-manifest.sha256` is unaffected by this pass. `Controls/Blake2s`,
  `Oracle` and `Tree` are byte-identical.
- **Added.** Eight `private` proof helpers, none of them a statement anyone relies on:
  - seven in `Words.lean`: `digestAt_cons`, `digestAt_append`, `bytesAt_cons`,
    `bytesAt_append`, `digestAt_zero`, `bytesAt_zero`, `bytesAt_nil`, under a new
    `/-! Reading at an offset … -/` section comment;
  - one in `Controls/Relation.lean`: `deepProof_check_succ`, with a docstring.
- **How "no statement changed" was checked.**
  - The original tree was rebuilt in a scratch copy (`/tmp/rf-golf-orig`, deleted afterwards; the dumps and timings it produced are in `logs/V3-S1-golf/`).
  - `logs/V3-S1-golf/tools/Dump.lean` ran in both trees. For every constant of the golfed
    modules and of `Contract/*`, it hashed the type and, for definitions, the value.
  - The 451 user-named declarations have identical type and value hashes
    (`sig-before.txt` = `sig-after.txt`). The only differences are compiler-generated
    auxiliaries (`_proof_n`, `_simp_n`, `match_n`, equation lemmas realised in a different
    module) and the private helpers above (`dump-{before,after}.txt`).
  - A textual signature diff (`tools/sigs.py`) agrees.
- **Records** (`logs/V3-S1-golf/`):
  - originals in `orig/`, diffs in `*.diff`;
  - timings in `time-before.txt` (standalone, before any edit) and `time-interleaved.log`;
  - profiles in `prof-{before,after}-Words.log`;
  - line counts in `loc-{before,after}.txt` and `loc-contract.txt`;
  - axiom audit in `axiomaudit.log` and `noaxiom-{before,after}.txt`;
  - `hygiene.log`.

## Checks

| Check | Result |
|---|---|
| `lake build` (default targets) | Green after each file was installed. The last rebuild of the changed modules and their dependants took 1 min 10 s (`Controls.Relation` 49 s of it). |
| Diagnostics | `lake env lean` on every changed file: no error, no warning, no linter message. |
| Axiom audit | **PASS.** This is the implementer's `logs/V3-S1/AxiomAuditV3.lean`, run unchanged over Contract, Library and Controls: everything is within `propext`, `Classical.choice`, `Quot.sound`. |
| Axiom-free theorems | 62, against 67 before. The whole difference is compiler-generated equation lemmas. Six are no longer generated: `rejectAll.eq_1`, `oneQuery.eq_1`, `OProg.queries.eq_{1,2,def}`, `extractorBudget.eq_1`. They existed only because `simp [f]` proofs unfolded those definitions, and the replacement terms no longer do. One, `enc64.eq_1`, is now generated. No named theorem changed its axioms. |
| `scripts/check-hygiene.sh` | OK. |
| Lines over 100 characters | None added. One was removed (`Words.lean` line 76). The two that remain are pre-existing: `WitnessSending.lean` (`extractorInput_eq` statement) and `Controls/Relation.lean` line 60 (a hex KAT). |

## Summary

Code lines are `python3 scripts/loc.py`; "lines" are `wc -l`.

| File | Lines before → after | Code before → after | Theorems |
|---|---:|---:|---:|
| `Library/Oracle.lean` | 41 → 38 | 24 → **21** | 3 |
| `Library/Security.lean` | 73 → 64 | 38 → **29** | 6 |
| `Library/Words.lean` | 257 → 209 | 202 → **145** | 20 (+7 private) |
| `Library/WitnessSending.lean` | 299 → 288 | 201 → **190** | 21 |
| **Library, in scope** | 670 → 599 | **465 → 385 (−80, −17 %)** | 50 → 57 |
| `Controls/Relation.lean` | 169 → 163 | 87 → **79** | 15 (+1 private) |
| `Controls/Security.lean` | 131 → 120 | 61 → **50** | 11 |
| `Controls/Certificate.lean` | 69 → 66 | 33 → **30** | 7 |
| `Controls/Extractor.lean` | 123 → 111 | 69 → **57** | 11 |
| `Controls/Machine.lean` | 75 → 74 | 34 → 34 | 8 |
| `Controls/{Blake2s,Oracle,Tree}.lean` | 269 → 269 | 95 → 95 | 34 |
| **Controls** | 836 → 803 | **379 → 345 (−34, −9 %)** | 86 → 87 |
| **Contract** (`loc.py` on the budget files) | 772 → 772 | **320 → 320** | — |

## Timings

All runs are `lake env lean <file>`. The original and golfed files are interleaved, each against
its own tree's imports (original: `/tmp/rf-golf-orig`; golfed: the working tree), over two rounds,
on a machine with load average about 1.2–1.6. Each time includes the 2.5–4 s import
(`time-interleaved.log`).

| File | Original (s) | Golfed (s) | Peak RSS |
|---|---|---|---|
| `Controls/Relation.lean` (kernel-evaluated) | 54.68, 52.74 | **54.50, 51.92** | 4.18 GB (same) |
| `Controls/Tree.lean` (kernel-evaluated, unchanged) | 18.91, 18.34 | 20.19, 18.41 | same |
| `Controls/Security.lean` | 6.18, 5.95 | 5.97, 6.13 | same |
| `Controls/Certificate.lean` | 6.17, 5.76 | 6.28, 5.96 | same |
| `Controls/Extractor.lean` | 6.24, 5.94 | 6.24, 6.02 | same |
| `Controls/Machine.lean` | 6.19, 5.57 | 5.89, 5.47 | same |
| `Library/Words.lean` | 6.61, 6.42 | 7.13, 6.33 | same |
| `Library/WitnessSending.lean` | 8.12, 7.23 | 8.01, 7.40 | same |
| `Library/Security.lean` | 6.08, 6.38 | 6.40, 6.03 | same |
| `Library/Oracle.lean` | 4.22, 4.15 | 4.30, 4.07 | same |

- **No control is slower.** The kernel-evaluated controls are unchanged or within noise:
  - `Controls.Relation`: its edited proofs are symbolic, and every `decide +kernel` is as before.
  - `Controls.Tree` and `Controls.Blake2s`: not touched, and their imports are unchanged.
- **`Words.lean`'s wall time is within noise, but its work moved.** In the profile, kernel type
  checking went from 0.28 s to 0.54 s, because `decodeWit_witWords` is now proved by `simp`, and
  `simp` went from 0.99 s to 1.05 s. This is the one cost of the pass.

## Changes, by file

### `Library/Words.lean` (202 → 145)

- **`decodeWit_witWords`** (71 → 44 lines, with the helpers).
  - **Before.** The proof restated the output list in seven re-associated forms (`e`, `e1`,
    `e5`, `e9`, `e10`, `em`, `e11`) and rewrote each field.
  - **Helpers.** Seven `private` "read at an offset" lemmas:
    - drop a word: `digestAt (a :: l) k = digestAt l (k - 1)` when `0 < k`, and the same for
      `bytesAt`;
    - drop a segment: `digestAt (X ++ l) k = digestAt l (k - X.length)` when
      `X.length ≤ k`, and the same for `bytesAt`;
    - read a packed field at offset `0`: `digestAt_zero`, `bytesAt_zero`, `bytesAt_nil`.
  - **After.** Each case is one `simp (disch := omega)` over the unfolded output, using these
    lemmas with core's `List.getElem?_append_right`, `List.getElem?_cons`, `ite_eq_right` and
    `Nat.mod_eq_of_lt`. `omega` discharges the length side conditions from the
    `packBytes_digest_length` facts in context.
  - **Trade-off.** One automated step replaces explicit rewriting. It is robust to the layout,
    and the format has no hand-written offset arithmetic left.
- **`wordByte_packBytes`** (20 → 16 lines).
  - The bound `ofLE … < 2^64` is one term: `(ofLE_lt _).trans_le (Nat.pow_le_pow_right … : _ ≤ 256 ^ 8)`,
    replacing a `calc`.
  - The `getElem?` rewriting is one `rw` (`List.getElem?_take_of_lt`), replacing
    `simp only` with a `have h8`.
  - The "past the end" branch is two `getD_eq_default` rewrites and `simp`.
- **`packBytes_append8`**: the `simp only`/`rw`/`congr`/`map_congr_left` tail (6 lines) is one
  `simp […, List.drop_left' h]`.
- **`ofLE_ofFn`**: the successor case is one `simp` (was `rw`, `simp only`, `rw`, `simp`).
- **`wordsBytes_length`**: `simp [wordsBytes, wordBytes, List.length_flatMap, mul_comm]`, with
  no induction.
- **`bytesAt_packBytes`** (12 → 6 lines): `refine ByteArray.ext (Array.ext' (List.ext_getElem
  (by simp) fun i _ h => ?_))` and one `rw`; the `hs` restatement of `π.size` is gone.
- **`toUInt8_mod`**: a term, `UInt8.toNat_inj.mp (by simp [Nat.toUInt8])`.

### `Library/WitnessSending.lean` (201 → 190)

- `encode_data`: `rfl`.
- `size_eq_length`: `Array.length_toList.symm`.
- `Vb_eq`: `simp [Submission.Vb, submission, V, OProg.run]`, replacing `unfold`, `split <;>
  simp_all`.
- `enc64_mod`: `simp only [enc64, List.ofFn_inj]` replaces `unfold` and `congr 1`.
- `rel_norm`, leaf case: one `rwa [norm, Rel, …]`, replacing `show`, `rw`, `exact`.
- `kstate.final`: `check_sound (Option.some.inj h)`. The `runLog` of a `ret` reduces, so no
  `simpa` is needed.
- `ks`: its query bound is `fun _ _ _ => le_rfl`.
- `complete`: a term.
- `computes`:
  - `hm` is stated directly;
  - `List.ext_getElem` is one `refine`;
  - the output-cap bullet is `unfold outCap proofCap at *` and `omega` (was 4 lines).
- `certificate.cap`: terms (`zero_le`, `Nat.le_add_right_of_le (by decide : 8 ≤ 2 ^ 40)`), not
  `simp`/`omega`.

### `Library/Security.lean` (38 → 29)

- `card_digest`: `simp [Nat.card_congr digestEquiv]`.
- `KState.bounded_of_not_bad`: `fun L q => by simp [h]`. The `IsEmpty` instance was not
  needed.
- `KState.one_le_of_bounded`: `(le_mul_iff_one_le_left (by positivity)).mp hb`, replacing two
  `have`s, `le_of_mul_le_mul_right` and two `simpa`.
- `errorCap_lt_one`: a term (no `unfold`).

### `Library/Oracle.lean` (24 → 21)

- `runLog_eq_run`:
  - the `none` case is `simpa using List.find?_eq_none.mp hf e he`;
  - the one-use `hm` is inlined.

### `Controls/Relation.lean` (87 → 79)

- `second_child_rejected`: one `rw […, Bool.and_eq_true] at h` and `of_decide_eq_true`.
- `Vb_over_cap`: the term `ite_eq_right (by omega)`.
- `deepProof_size`:
  - `obtain ⟨m, hm⟩ : 8 ∣ … := by …` replaces `have h8` with a later `obtain`;
  - `pow_succ` is folded into the `simp only`;
  - `omega` uses `hm` without `rw [hm] at ih ⊢`.
- `deepProof_check` and `deep_accepted_but_capped` repeated the same 4-line "node over two
  accepted children within the cap" step. That step is now the private
  `deepProof_check_succ`, and both proofs call it. `hsize`/`hcap` are gone, and
  `deep_accepted_but_capped` is one anonymous constructor.

### `Controls/Security.lean` (61 → 50)

- `rejectAll_ks`:
  - a term;
  - the `final` law is `nomatch h`: `some false = some true` reduces to a constructor clash;
  - the query bound is `le_rfl`.
- `badAll.final`: `nomatch h`.
- `rejectAll_not_complete`: `Bool.false_ne_true (h … rfl)`.
- `acceptAll_kstate_iff`: an anonymous-constructor term. `classical` was not needed.
- `badAll_not_capped`: `(… .trans hc).not_gt errorCap_lt_one`.
- `oneQuery_not_qV0`: `Nat.not_succ_le_zero 0 (h …)`.

### `Controls/Certificate.lean` (33 → 30)

- `flipped_image`: `simpa […] using h.img`.
- `acceptAll_no_certificate`: `(…acceptAll_no_kstate_none S.Vb).false (hV ▸ hE ▸ h.secure.1.choose)`.
- `error_one_no_certificate`: `(hε ▸ h.cap.1).not_gt errorCap_lt_one`.

### `Controls/Extractor.lean` (69 → 57)

- The three instantiations at the zero tape fit on one line, using `.empty` for
  `ByteArray.empty` (the same elaborated term).
- `ws_fuel_7`: `cases (show run img tape0 7 = none by decide +kernel).symm.trans ho`. It is the
  same kernel evaluation, without a separate `have`.
- `halt_not_ws`:
  - the tape-length obligation is `simp [extractorInput_eq, packBytes_length, hs]`
    (was `rw` + 7-lemma `simp only` + `decide`);
  - `cases (halt_run _ 0).symm.trans ho` replaces `rw [show 1 = 0 + 1 …, halt_run] at ho`;
  - the end is `nomatch hd.trans (decode_encode …)`.
- `noCode_computes_nothing`: `cases (noCode_run _ _).symm.trans ho`.
- `toolong_run`: `exact ⟨_, rfl, (length_readWords _ _ _).trans (by simp)⟩`. A plain `simp
  [readOut, …]` hits the recursion limit on the 3-instruction state, so the lemma is applied first.
- `toolong_not_computes`: `cases ho.symm.trans ho'`, then `absurd (hl' ▸ hl) (by decide)`.

### `Controls/Machine.lean`

- One doubled blank line removed. No code change.

## Declined

1. **The trusted contract.** It has almost no proofs. The only one is the length field of
   `blake2sDigest`, which is one line already. The two shortenings that do not change any term
   were left alone:
   - **`KState.Bounded`'s binders** could be `{R V E}` instead of the three typed implicits
     (−1 code line). Checked: the type and value are `==` to the current ones. Declined because
     the trusted file should show the auditor the types.
   - **`Contract.lean`** could import only `Certificate` and `Tree`, since the other six are
     transitive (−6 code lines). Declined because the reading-order imports are deliberate
     (V3-S1-A1).
2. **`Contract/Machine.lean`**: semantics, out of scope; it has no proofs.
3. **`WitnessSending.run_img`** and **`Controls/Extractor.toolong_run`**. These are
   instruction-by-instruction traces, where each step is a `rw [execute_step …]` plus a `simp`
   with a step-specific set. A macro or `iterate` would hide the trace and save nothing without
   semicolons. In `run_img`, the `fin` abstraction stays: it keeps `simp` off the 14-deep
   `setReg`/`setPC` state. Inlining it was not tried; in `toolong_run`, a `simp [readOut, …]`
   on the final state hits the recursion limit.
4. **Kept as they were**: `check_sound`, `check_encode`, `fits_norm`, `img_fetch`,
   `extractorInput_eq`, `Words.ofLE_div_mod`, `digestAt_packBytes`, `getD_append_*`,
   `packBytes_wordsBytes`, `Controls/Relation.node_of_two_leaves`, `spin_run`, `halt_run`. Each
   is already 1–5 direct lines, and every variant tried was the same length or used heavier
   automation for one line.
5. **`Controls/Blake2s`, `Oracle`, `Tree`**: one `decide`/`decide +kernel`/`rfl` per theorem;
   nothing to shorten.
6. **Tried and failed**:
   - an `Option.isSome_iff_exists` route in `runLog_eq_run` (the `find?` predicate does not
     unify);
   - `one_le_of_bounded` as a single term (`positivity` cannot see through `simpa`);
   - `simp` in place of `rw [readOut, length_readWords]` in `toolong_run` (recursion limit).
7. **Statement-level shortenings** that the brief excludes. `deepProof_check`'s bound `k ≤ 12`
   could be `k ≤ 13`, since level-12 children are within the cap. Then
   `deep_accepted_but_capped` would be `deepProof_check 13`. Kept, and handled with the private
   helper instead.

## For the orchestrator: shorter only by changing a statement

- **`Rel`'s leaf clause.** The pending bound on `n` would also delete library code: about
  20 lines of `WitnessSending` (`norm`, `rel_norm`, `enc64_mod`, `chainEnd_chainEnd`, the leaf
  half of `fits_norm`) and the `n mod 2^64` paragraph of its header.
- **`Submission.Vb`** as `decide (π.size ≤ proofCap) && (S.V c π).run blake2sOracle`. It is
  propositionally, not definitionally, equal to the current `if … then … else false`. It is not
  shorter in the contract, but it would turn the library's `Vb_eq` into `rfl` (−1 line). That
  is the form every control reads `Vb` through.
- **`blake2sDigest`** needs a length proof only because `blake2s256` returns a `List`.
  `Hash/Blake2s.lean` is out of scope.
- **`OProg.queries`** takes the program before the oracle, unlike `run H` and `runLog L`. Making
  the order consistent is a statement change, for consistency rather than length.

## For the orchestrator: statements against their docstrings

No trusted statement says more or less than its docstring; I re-read every docstring in
`Contract/` against its definition. Three control headers are slightly stronger than the
theorems they name:

1. **`Controls/Extractor.lean` header, `ws_run_8`.** The header says it "halts in exactly 8
   steps". The theorem `run img tape0 8 = some []` shows *within* 8. The 7-step `none` that
   makes it exact exists only inside `ws_fuel_7`'s proof, not as a theorem of its own.
2. **`Controls/Relation.lean`, `wrong_end` and `tags_separate`.** The docstrings read
   generically ("a leaf statement committing to the start …"). Both are proved for one instance
   (`s0`, `n = 1`). That is fine for a control, but the wording could say so.
3. **`Contract/Tree.lean`, `treeRoot`.** "`|cs|` levels always suffice" is true but unproved
   anywhere. The controls cover 0–4 and 8 digests by `rfl`. It is a claim in a docstring, not in
   a statement.

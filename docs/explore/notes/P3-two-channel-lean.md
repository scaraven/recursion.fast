# P3: Lean probe of the two-channel model (W5, the channel split)

Probe author: Lean implementer agent, 2026-10-20. Code: `RecursionFast/Explore/TwoChannel/`
(`Model.lean`, `Merkle.lean`, `Backdoor.lean`), imported by the root `RecursionFast/Explore.lean`.
It answers W1 §7.7: can the two-channel knowledge laws be met by a natural Merkle verifier that
extracts from the `pub` entries, and is the CGH backdoor uncertifiable on the public channel?
Every claim is **kernel** (file and theorem named) unless marked **paper**. `SP` is the scratchpad
of the brief; logs are in `logs/p3/`.

## Conclusions

1. **Verdict on `pubStep`: it holds in the strong form, with equality.** It is not the
   load-bearing law. The natural potential prices each secret answer against the log as it was
   before that answer (`ofHist`). A later `pub` entry adds no secret answer and leaves every
   earlier prefix unchanged, so `μ (L ++ [pub m a]) = μ L` for every verifier and every bad-answer
   predicate (`ofHist_pub`). For the Merkle verifier this is `Merkle.merkleState_pubStep`.
2. **The load-bearing law is `final`'s escape set. W1 §7.1's form (witness or a collision) is
   unsatisfiable for the Merkle verifier.**
   - There is no state at any `ε < 1` for the natural extractor (`Merkle.col_no_kstate`, and
     `col_no_kstate_blake2s` for concrete BLAKE2s values). This holds even with the fallback
     `pubStep` "... or the new entry completes a collision".
   - Every extractor that certifies it inverts BLAKE2s (`col_extractor_inverts`).
   - The attack is a *late preimage*. The adversary squeezes on an honest root it has not
     evaluated, then evaluates the selected leaf's hash and the root. The verifier accepts. The
     other leaf appears in no entry, and the log has no collision.
   - W1 §7.4 item 1 assumes the root is explained by the log when it is squeezed. Nothing in the
     model forces that.
3. **With late preimages as a second escape, the natural Merkle verifier is certified.**
   - The escape `Esc.late j m a` says: digest `a` occurs in the input of entry `j`, no entry up to
     `j` produces it, and a later `pub` entry does. This is the event that preimage awareness
     excludes.
   - With it, the verifier has a `KState2` at `ε = 1/2` for the extractor that decodes the tree
     from the first logged preimages or else returns an escape it finds in the log
     (`Merkle.merkleState`, proof in `merkle_final`).
   - `1/2` is tight (`merkle_eps_ge`). Honest proofs are extracted to a witness, not escaped
     (`honest_extracts`).
4. **The verifier's own BLAKE2s evaluations must be in the log.**
   - In the probe, `runLog` answers a verifier's `pub` query from the log.
   - Read literally, W1 §7.1 has the verifier hash outside the log, so that `runLog` reads only
     `sec` entries. The same Merkle check written that way (`Vpure`) has no state in either escape
     mode at any `ε < 1` (`pure_no_kstate`), and every certifying extractor inverts BLAKE2s
     (`pure_extractor_inverts`).
   - This is the same rule as v3, where the verifier's queries are part of the final log.
5. **CGH on the public channel is closed in the kernel.**
   - On a consistent log, a verdict read from the log is the deployment verdict
     (`TProg.runLog_run`). So the backdoor's comparison "my BLAKE2s of `q0` equals the channel's"
     is true in the model exactly as in deployment (`Backdoor.bd_runLog`, `bd_run`). The magic
     proof is accepted at potential `0` with nothing to extract.
   - The natural extractor fails at **any** error (`bd_no_kstate`).
   - Every extractor would have to be a total inverter of the Merkle root map
     (`bd_extractor_inverts`).
   - For a relation with 256 witnesses, no extractor works at all (`bdW_no_kstate`). Without the
     backdoor, the same verifier is certified (`wsState`).
   - The same backdoor on the **secret** channel *is* certified at `errorCap` (`bdSecW_kstate`). In
     deployment it fires exactly when the secret oracle answers `q0` with `trigger`
     (`bdSecW_run`). On that channel CGH is closed by the deployment (a keyed PRF the submitter
     cannot evaluate, **paper**, W1 §7.3), not by the model.
6. **What W5's contract `final` should say (paper, from 2–4):** "witness, or a collision between
   two logged evaluations, or a late preimage", with the verifier's evaluations in the log.
   - The deployment claim then names three hash assumptions: PRF security of the secret channel,
     collision resistance of BLAKE2s, and preimage awareness in the concrete form "no BLAKE2s
     output is used before it is evaluated".
   - W1 treated the third as a remark about modelling. The probe shows it has to appear in the
     conclusion.
   - Equivalent placements (not built): a hypothesis on logs, or an exception to `pubStep`.

## Theorems

Namespace `RecursionFast.Explore.TwoChannel` omitted; `Merkle.`/`Backdoor.` prefixes name the
file.

| Lean name | File | Meaning |
|---|---|---|
| `Entry`, `Log2`, `pubConsistent` | Model | A log entry is `sec q a` (secret answer) or `pub m a` (BLAKE2s evaluation). A log is consistent when every `pub` entry is correct. |
| `TProg`, `TProg.runLog`, `TProg.run` | Model | Programs with `sec` and `pub` queries. `runLog` answers both from the log, using the first entry, and fails if the entry is absent. `run O` answers `sec` with `O` and `pub` with BLAKE2s. |
| **`TProg.runLog_run`** | Model | A verdict read from a consistent log is the deployment verdict under every secret oracle that agrees with the log's `sec` entries. |
| `Esc`, `EscValid`, `Collision`, `LatePre`, `Mode` | Model | Escapes as data pointing into the log. `col m m' a`: two distinct logged inputs with output `a`. `late j m a`: as in Conclusion 3. Mode `col` allows collisions only, mode `colLate` allows both. |
| **`blake2s_collides`** | Model | BLAKE2s has a collision (pigeonhole), so a "witness or collision" with a bare collision proposition would be vacuous. |
| `escSearch`, `escSearch_sound`, `escSearch_complete` | Model | A finite search over the log returns a valid escape exactly when one exists. |
| **`KState2`** | Model | Potential `μ` with four laws. `empty`: `μ [] = 0`. `step`: on a consistent log of fewer than `logCap` secret entries and potential below `1`, a fresh secret query raises `μ` by at most `ε` on average over its `2^256` answers. `pubStep`: `pubConsistent (L ++ [pub m a]) → μ (L ++ [pub m a]) ≤ μ L`. `final`: on a consistent log below `1`, every proof `V` accepts is mapped by `E` to a witness or a valid escape. |
| `KState2W`, `KState2.toW`, `KState2W.toColLate` | Model | The same laws with the fallback `pubStep` "`≤ μ L` or the new entry completes a collision". The strong form implies it, and a collision-only state is a state with both escapes. |
| `BadLog`, `histμ`, **`KState2.ofHist`**, **`ofHist_pub`** | Model | The builder: potential `1` iff some secret answer was bad for the log before it. `pubStep` holds with equality. `step` reduces to counting bad answers. |
| `KState2W.le_of_pubTail`, `final_tail`, `card_le`, `one_le_of_fail`, `exists_valid` | Model | The negative pattern. From a log of potential `0`, if every answer to a fresh query is followed by evaluations, completing no collision, after which `V` accepts a proof the extractor does not open, then `ε ≥ 1`. The same holds for any extractor: some answer leads to a log where it returns a valid output. |
| `MRel`, `V`, `Vpure`, `P`, `E`, `treeWit` | Merkle | The toy. `c` is the root over two leaves, and `MRel c (d₀, d₁)` says `c = root d₀ d₁` with both leaves good (first byte `0`). `V` squeezes `0x73 ‖ c`, takes the position from the low bit, and checks the opening (leaf, sibling hash) with two `pub` evaluations. `Vpure` does the same check with hashing outside the channel. `P` is the honest prover, which evaluates the tree before the squeeze. `E` decodes the tree from first logged preimages or searches for an escape. |
| `Merkle.complete` | Merkle | The honest proof is accepted under every secret oracle. |
| `Merkle.treeWit_sound`, `Merkle.card_bad` | Merkle | A decoded tree is a witness on a consistent log. At most half the answers to any query are bad. |
| **`Merkle.merkle_final`** | Merkle | On a consistent log with no bad squeeze, an accepted opening is extracted, or the log has a collision (a second preimage of the root or of the leaf hash), or a late preimage (of the root, used in the squeeze, or of the leaf hash, used in the root's input). |
| **`Merkle.merkleState`**, **`Merkle.merkleState_pubStep`** | Merkle | `KState2 .colLate MRel V (E .colLate) (1/2)`. Its `pubStep` is an equality. |
| `Merkle.honest_accepts`, `honest_extracts`, `honest_extracts_blake2s` | Merkle | On the honest log, `V` accepts and `E` returns a witness, not an escape, unless a leaf hash equals the root. The concrete leaves are checked in the kernel. |
| **`Merkle.merkle_eps_ge`** | Merkle | Every `KState2W .colLate` of `V` for `E` has `ε ≥ 1/2`. The test log commits a (good, bad) tree, all evaluated before the squeeze, and has no escape (decided by the kernel). |
| **`Merkle.col_no_kstate`**, `col_no_kstate_blake2s`, `kat` | Merkle | No `KState2W .col MRel V (E .col) ε` for `ε < 1`. The hypotheses are good `d₀`, `d₁` with `leafH d₀ ≠ leafH d₁` and neither leaf hash equal to the root. `kat` checks these for two concrete leaves with `decide +kernel`. |
| **`Merkle.col_extractor_inverts`**, `inverts_or_collides` | Merkle | Every extractor of a collision-only state returns, on some late log, a Merkle preimage of the root. That is either a preimage of the unopened leaf hash, which no entry evaluates, or a BLAKE2s collision with the root's input. This holds for every good pair whose leaf hashes differ from the root, so hardcoding a few pairs does not help. |
| **`Merkle.pure_no_kstate`**, `pure_extractor_inverts` | Merkle | `Vpure` has no state in either mode for `E` at `ε < 1`. Every extractor returns a Merkle preimage of any good root from one leaf, the other leaf's hash, and a log holding only the squeeze. |
| `Backdoor.bdV`, `bd_runLog`, `bd_run` | Backdoor | The public-channel backdoor: evaluate `q0` on the channel, and accept `magic` when the result is the locally computed `trigger`. It accepts on every consistent log that records `q0`, and in deployment under every oracle. |
| **`Backdoor.bd_no_kstate`** | Backdoor | No `KState2W` for the natural extractor, in either mode, at **any** `ε`. |
| **`Backdoor.bd_extractor_inverts`**, `kstate_of_total` | Backdoor | Every extractor returns, for every `c`, a good Merkle preimage of `c` from `magic` and the one-entry log. Conversely, if every digest had a witness, the choice extractor would certify every verifier at `ε = 0`. |
| `Backdoor.R1`, `wsV`, **`wsState`** | Backdoor | A one-byte-witness relation `c = BLAKE2s(0x77 ‖ x)`. Witness-sending checked on the public channel, certified at potential `0`. |
| **`Backdoor.bdW_no_kstate`**, `exists_unwitnessed`, `bdW_run` | Backdoor | The backdoored witness-sending verifier has no state for **any** extractor at any `ε`. 256 witnesses cannot cover `2^256` digests. It accepts `magic` in deployment. |
| **`Backdoor.bdSecW_kstate`**, **`bdSecW_run`** | Backdoor | The same backdoor on the secret channel is certified at `errorCap`. In deployment it fires iff `O q0 = trigger`. |

## `#print axioms`

`lake env lean logs/p3/P3Axioms.lean` (`logs/p3/p3-axioms.log`): 38 declarations, 24 on
`[propext, Classical.choice, Quot.sound]`, 14 on `[propext, Quot.sound]`, none other. No `sorry`,
`native_decide`, `implemented_by`, `extern` or `csimp` in the three files (grep).

```
[propext, Quot.sound]
  TProg.runLog_run, escSearch_sound, escSearch_complete,
  Merkle.complete, Merkle.treeWit_sound, Merkle.honest_accepts, Merkle.honest_extracts,
  Merkle.honest_extracts_blake2s, Merkle.inverts_or_collides, Merkle.kat,
  Backdoor.bd_runLog, Backdoor.bd_run, Backdoor.bdW_run, Backdoor.bdSecW_run
[propext, Classical.choice, Quot.sound]
  blake2s_collides, KState2.toW, KState2.ofHist, ofHist_pub, KState2W.le_of_pubTail,
  KState2W.one_le_of_fail, KState2W.exists_valid,
  Merkle.card_bad, Merkle.merkle_final, Merkle.merkleState, Merkle.merkleState_pubStep,
  Merkle.col_no_kstate, Merkle.col_extractor_inverts, Merkle.col_no_kstate_blake2s,
  Merkle.pure_no_kstate, Merkle.pure_extractor_inverts, Merkle.merkle_eps_ge,
  Backdoor.bd_no_kstate, Backdoor.bd_extractor_inverts, Backdoor.kstate_of_total,
  Backdoor.exists_unwitnessed, Backdoor.wsState, Backdoor.bdW_no_kstate, Backdoor.bdSecW_kstate
```

## Check times and size

**Measured** (`logs/p3/p3-check-times.log`, `p3-merkle-profile.log`, `p3-loc.log`), with
`timeout 600 lake env lean <file>` against prebuilt imports:

| File | Wall | Code lines | Theorems |
|---|---|---|---|
| Model | 11.3 s | 376 | 35 |
| Merkle | 21.3 s | 488 | 54 |
| Backdoor | 8.5 s | 142 | 19 |

- `lake build RecursionFast.Explore.TwoChannel.Backdoor` took 37 s to rebuild all three modules
  after an edit to Model.
- Each file's import takes about 3 s.
- Merkle's time is BLAKE2s in the kernel, about 14 s of type checking
  (`-Dtrace.profiler=true`): `kat` 5.4 s, `kat_c` 3.1 s, `kat_h0` 1.7 s, `kat_hb` 1.7 s, and the
  literal decisions `tight_esc` 0.7 s and `tight_treeWit` 0.5 s. Without them the file would take
  about 8 s.
- Model's remaining time is spread across elaboration, chiefly the derived `DecidableEq` and the
  `Decidable` instance of `EscValid` (about 0.5–1.1 s each). Nothing in it is pathological.
- The probe is 1,006 code lines, against W1 §7.7's estimate of about 150. The rest is the escape
  machinery, the negatives and the controls.
- Pitfall: a local hypothesis of type `a ∈ Finset.univ.filter …` over `Digest` makes the
  `constructorNameAsVariable` linter (or the elaborator) unfold the `2^256`-element `univ`
  (maximum recursion). The counting is therefore done with `Fintype.card` of subtypes.

## Abstractions and deviations

1. **The verifier's evaluations are read from the log** (`TProg.pub`, answered by `runLog` from
   `pub` entries). W1 §7.1 reads only `sec` entries. Reason: `pure_no_kstate`. Without this, the
   log of an accepted opening can hold no evaluation at all, and `final` must extract from
   nothing. In the paper game the verifier's evaluations are appended after the adversary's, at
   no cost by `pubStep`.
2. **Escape set extended by late preimages** (`Mode.colLate`). Reason: `col_no_kstate`; the
   fallback `pubStep` does not rescue the collision-only form (the negative is for `KState2W`).
   The collision-only form is kept as `Mode.col` so that the negative is stated against exactly
   W1's law.
3. **Escapes are data.** `E` returns `W ⊕ Esc`, and an escape must name entries of the log: a
   collision by its two inputs and output, a late preimage by the index of the entry using the
   digest and the later evaluation. A bare "BLAKE2s collides" would be true (`blake2s_collides`).
   An escape anywhere in the log counts, not only on the opened path. The escapes are hash events
   independent of the verifier, so the extra term of the paper bound is the same for every
   submission.
4. **`step` also assumes `pubConsistent L`.** Games produce only consistent logs, so this spares
   submitters obligations on impossible logs. The paper theorem is unaffected. The length guard
   counts `sec` entries only (`secCount`, W1 §7.4 item 2). `final` also assumes consistency.
5. **Types.** Queries and messages are `List UInt8`, not `ByteArray` (decidable equality for the
   escape search). Proofs and witnesses are typed (`Opening`, `Digest × Digest`;
   `Option (Fin 256)`, `Fin 256`), not the contract's bytes and `Wit`. There is no `proofCap`, no
   `qV` bound (no `KS2` is defined), and no extractor image or fuel. Domain tags `0x6C`, `0x6E`,
   `0x73`, `0x77` are disjoint from the contract's.
6. **The toy is minimal**: two leaves, one squeeze, one opening, `ε = 1/2`. The potential is the
   history potential (`bad`: the squeeze selected a position that was known-good while the other
   was not, judged on the log before the squeeze). The brief suggested counting unrecoverable
   positions below the squeeze and "the squeezed position is unrecoverable" after it (**paper**,
   why not):
   - Below the squeeze no root is fixed, so the potential must be `0`.
   - After it, "unrecoverable" is `1` on every answer for an unexplained root, so `step` fails.
   - It is also `1` on positions that can never be opened, which is pointless.
7. **Concrete BLAKE2s values** are used only where a negative or a tightness claim needs specific
   digests. `kat` holds three inequalities, and `kat_h0`, `kat_hb`, `kat_c` match `hashlib`. The
   positive results and the general negatives never unfold `blake2sDigest`; they hold for any
   public hash.
8. **The "every extractor" results.** For `MRel` the strongest result is "a total inverter"
   (`bd_extractor_inverts`, `col_`/`pure_extractor_inverts`). `kstate_of_total` shows that ruling
   out every extractor would need a BLAKE2s fact. With `2^496` good leaf pairs for `2^256` digests,
   totality is in fact expected (**estimate**). The full "no extractor" result is proved for the
   small relation `R1` (`bdW_no_kstate`).

## What the probe does not show

- **That consistent logs, in evaluation order, model a real adversary.** That is preimage
  awareness or observability of BLAKE2s (Dodis–Ristenpart–Shrimpton 2009), which no Lean
  statement can capture. The probe makes it explicit as the `late` escape, but the claim that its
  probability is small is an **assumption**, as is the bound on `Collision`.
  - For a uniform adversary whose BLAKE2s outputs come only from evaluations, a late preimage
    means predicting an output before computing it.
  - For a non-uniform adversary it costs nothing: hardcode a pair `(y, BLAKE2s y)`, use the digest
    in a query, then "evaluate" `y`. The bound is then vacuous for that adversary, as in the ROM
    without auxiliary input.
  - Collision resistance has the same problem only for a hardcoded *collision*, which nobody
    knows ("human ignorance"). So the late-preimage assumption is strictly stronger than
    collision resistance, and it is idealised.
- The two-channel paper theorem: P[accept ∧ no witness ∧ no valid escape] ≤ `(Q_sec + qV)·ε`,
  with `pub` steps as zero-cost supermartingale steps. Not built. **Paper**: `Library/PaperTheorem.lean`
  rerun with `pubStep`.
- Composition across tree levels, W4 attestation of child challenge lists, and multi-squeeze IOPs
  (Fiat–Shamir transcripts, many openings). The history builder covers any per-squeeze bad set,
  but `final` for a real multi-round verifier is not done.
- The secret-channel half of CGH closure. It is a PRF and deployment argument (**paper**). The
  kernel only shows that the model certifies a secret-channel backdoor (`bdSecW_kstate`) and when
  it fires (`bdSecW_run`).
- Efficiency of extractors. The knowledge laws bound no extractor, so the "inverts BLAKE2s"
  results bite only once the contract's image and fuel bound applies (decision Q1). A
  noncomputable choice extractor certifies anything whose relation is total (`kstate_of_total`).

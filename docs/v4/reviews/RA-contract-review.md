# Stage R, part A: adversarial review of the v4 contract, library and controls

Reviewed: branch `v4/srom-rules` at `85f0985` (stage A, `docs/v4/stages/A-contract-RESULT.md`),
against `docs/v4/BRIEF.md` (§3 decisions, §4 interfaces, §5a amendments), `docs/DESIGN-v4-srom.md`
§1–§2 and §5, `docs/v4/reviews/C-design-attack.md`, the v3 contract on `origin/v3/contract-archive`,
and the Python reference `scripts/speed/signer_ref.py`. Method: `adversarial-review` (passes A
specification, B fidelity, C hygiene, run independently) and `lean4:review`. Statements and
definitions were reviewed, not proof style (a golf agent was shortening proofs concurrently).
Probes: `logs/ra-probes/` (gitignored), each run with `timeout 600 lake env lean`.

## 0. Summary

The trusted base says what the brief and the design say. `Rel`, `runSeq`, `Submission.acc` and
`Certificate` are character for character the brief's §4.1 (with V4-A3's exact consumption,
`queryCap` and conjunct order); the byte layouts of `traceDigest`, the WOTS digits and checksum,
`wotsStep`, `wotsLeaf`, `sigNode`, `sigRoot` and `SigOk` match BRIEF §4.2 and the independent
Python reference line by line; `Security`, `Machine`, `Tree` and `Hash/Blake2s` are code-identical
to v3 (comment-only diffs, checked with `diff` on the code after the header). 355 code lines
(`scripts/loc.py`), standard axioms only on all 43 modules (`logs/ra-probes/axiom-audit.log`),
no forbidden token or attribute anywhere in `RecursionFast/`. The controls are non-vacuous and
test the contract's definitions, not Library twins. The strict decoder loses no witness and
admits no new one.

Two findings are major, both cheap to fix and both about a **statement being weaker than the
prose that cites it**, not about a wrong definition: the composition theorem's propositional
form is trivially true for every key a signer knows (the content is the computable `walk`,
which the design should name as such, and `Forgery` should carry the query cap the paper split
needs); and a sentence in the trusted `Certificate.lean` header, repeated in the design, claims
every accepted trace has at most `qV` entries, which is false for non-functional traces. Four
minors.

## 1. Pass A: specification (non-vacuity, semantics)

### RA-M1 (major). `Compose.compose` is vacuous for every signer's key; `Forgery` lacks the cap the paper reduction needs

**Claim.** `Library/Compose.lean`'s `compose` concludes
`(∃ ss, …) ∨ Nonempty Collision ∨ Nonempty (Forgery vk L)`. For every `vk = Signer.pk sk`, and
so for the deployed key, the third disjunct is provable with **no hypothesis**: anyone holding
`sk` signs a one-entry trace whose query is longer than every query in `L`. The design document
calls `compose` "the composition theorem" (§0 line 67, §2.4 table, §2.7 item 4) and a reader who
takes the proposition at face value gets nothing from it; the kernel content is the **type of
`walk`** (a function from the hypotheses to an `Outcome` computed from the root proof through
`S.E`), which is a `def`, not something the documents name as the theorem.

**Evidence.** `logs/ra-probes/P1_forgery_trivial.lean` (exit 0, axioms `propext`,
`Classical.choice`, `Quot.sound`):

```lean
theorem forgery_trivial (sk : ℕ → ℕ → Digest) (L : Log) :
    Nonempty (Compose.Forgery (Signer.pk sk) L)          -- no hypothesis
theorem compose_conclusion_free (sk) (L) (n) (hs) :
    (∃ ss, List.Forall₂ (fun s h => chainEnd s n = h) ss hs) ∨ Nonempty Collision ∨
      Nonempty (Compose.Forgery (Signer.pk sk) L)       -- compose's conclusion, free
```

Second part of the claim: `Forgery` records `sig : SigOk vk (traceDigest p.tr) p.σ = true` and
`notIn`, but not `∀ e ∈ p.tr, e.1.size ≤ queryCap`. The paper split of this outcome (design §2.4
last table row, V4-A8) into an EUF-CMA forgery or a trace-digest collision applies
`traceBytes_inj`, which needs the cap on **both** traces; the service's trace has it by the wire
cap, the forgery's only because `walk` built it from an `acc`-accepted proof, a fact the type
drops. The reducer can re-check the data, but the statement should carry it.

**Fix.**
1. Add to `Forgery` the field `cap : ∀ e ∈ p.tr, e.1.size ≤ queryCap` (available in `extract`
   from `acc_parts`; extend `acc_parts` to return it).
2. Either delete `compose`, or rename it `compose_exists` with a docstring saying it is the
   existential shadow of `walk`, trivially true for every signable key, kept only as a
   readability corollary. Add `forgery_trivial` to a new `Controls/Compose.lean` as the negative
   control recording what the proposition does not say.
3. Design §0 (line 67), §2.4 table and §2.7 item 4, and RESULT §1: name `walk` as the kernel
   content ("the computable `walk`, whose type is the statement: from a knowledge state, a
   functional log within `logCap` with potential below 1, and an accepted root proof, it returns
   the leaf starts, an explicit collision, or an explicit capped signed trace not in the log,
   computed from the root proof"), and `compose` as its corollary.
4. (Recommended, same file.) A positive control for `walk`: with `WitnessSending.submission`,
   `WitnessSending.kstate vk`, `L = []`, `r = 0` and the leaf proof `Controls.Relation.leafSigned`,
   `walk` returns `.starts [s]`; and for `r = 1` with `node_of_two_leaves`' node. Symbolic, no
   hash evaluated (`decode_encode`, `sigOk_sign`). Today no control exercises `walk`
   (`Controls.lean` has no `Compose` module; RESULT §3 lists only `treeRoot_append`).

### RA-M2 (major). The trusted header says every accepted trace has at most `qV` entries; it does not

**Claim.** `Contract/Certificate.lean` lines 35–37: "Used up exactly, the trace of an accepted
child is the verifier's own queries, at most `qV` of at most `queryCap` bytes". Design §1.2
("at most `qV` entries, fixed by the verifier's own design") and the C-M3 fix text ("every
accepted trace has at most `qV` entries") say the same. `KS`'s bound is over oracle **functions**
(`∀ H, (queries H).length ≤ qV`); `runSeq` accepts any answer sequence, functional or not, and a
non-functional trace follows no function's path. `Library/Trace.lean` already knows this:
`runSeq_length_le` assumes `Log.Functional tr`, and RESULT open question 3 names it. The sentence
in the trusted header is false as written.

**Evidence.** `logs/ra-probes/P2_qV_nonfunctional.lean` (exit 0, axioms `propext`,
`Quot.sound`): a verifier that asks `q` until two consecutive answers agree asks exactly 2
queries under every `H`, so `qV = 2` holds in `KS`'s sense, yet

```lean
theorem probe : (∀ H c π, ((V c π).queries H).length ≤ 2) ∧
    ∃ tr : Trace, tr.length = 4 ∧ (V 0 ⟨#[]⟩).runSeq tr = some true
```

With a signature on that trace, `acc` accepts it; under `vk = pk sk` such witnesses are in
`Rel (acc vk)`. Consequence for C-M3: the witness space of a verifier whose query count is
unbounded over *non-functional* answer sequences is still unbounded, so a fixed-size node prover
for such a `V` is not complete. This bites no verifier with a bounded query schedule, and
service-signed traces are functional, so the harness's and the circuit's sizing from `qV` is
right for honest traces; but the trusted text must say which traces it speaks of.

**Fix** (one of two; the orchestrator chooses).
- Wording: in `Certificate.lean` and design §1.2, "the trace of an accepted child is the
  verifier's query sequence on that trace's answers; on a functional trace (every trace the
  service signs) it has at most `qV` entries (`Library/Trace.lean`, `runSeq_length_le`); for
  completeness the submitter bounds `V`'s queries on every answer sequence, which `qV` does not
  do". Also correct the C-M3 fix sentence where it is quoted.
- Contract: state `KS`'s query bound over traces, `∀ c π tr b, ((V c π).runSeq tr = some b) →
  tr.length ≤ qV` (one line, replaces the function form, which it implies through
  `runSeq_queries`). Then the header is true as written, node circuits are sized from `qV`
  against every accepted trace, and the witness space is bounded for every certified `V`. This
  changes a v3-verbatim definition (`KS`), so it needs the V4-1 ledger line and the controls
  `oneQuery_not_KS`, `queryThenAccept_ge_one` re-read (they should go through unchanged).

### Checked and found right (Pass A)

- `Rel`: leaf clause v3's; node clause `c = nodeStmt c₁ c₂ ∧ acc c₁ p₁ ∧ acc c₂ p₂`, identical to
  BRIEF §4.1. No vacuity: `node_of_two_leaves` (every `sk`, every two starts and lengths) and
  the six negatives are all under the contract's `Rel`/`acc`, not a twin.
- `Submission.acc`: the four conjuncts of V4-A3 in the amended order; `≤ proofCap`, `≤ queryCap`
  (both `≤`, `acc_query_at_cap` checks the boundary), `SigOk vk (traceDigest tr) σ`,
  `runSeq tr = some true`. `&&` is `@[macro_inline]`, so compiled rejection stops at the first
  false conjunct as the header says.
- `Certificate`: `∀ vk` on `secure` and `complete`; `computes` and `cap` v3's. The `∀ vk`
  controls do the advertised work: `sigTrust_no_certificate` instantiates `vk := pk (fun _ _ => 0)`
  and uses `sigOk_sign`, so it is not vacuous; `sigTrust_ks_unsignable` is a conditional on a key
  nobody can exhibit, correctly stated as such in RESULT §3.
- `KState`, `KS`, `failProb`, `CompleteWithError`, caps: byte-identical to v3 (V4-1).
- `runSeq`: exact consumption, both `ret` clauses as V4-A3 writes them.
- `decodeWit` (deviation 2): strict; every `Rel` witness that fits `outCap` is denoted
  (`decodeWit_witWords` with `Wit.Fits`; `acc` supplies `π.size ≤ proofCap < 2^64`,
  `|q| ≤ queryCap`, and `SigOk` the counts `idx < 2^16`, `|ots| = 133`, `|path| = 16`); nothing
  new is denoted that `Rel` would accept (a decoded child above `proofCap` fails `acc`). The
  dropped `proofCap` check in the decoder is therefore safe. Reading is linear: `readList` runs
  in `StateT (List Word) Option` and stops at the first failure, `readBytes` takes `⌈n/8⌉`
  words then checks the count. `outCap` arithmetic in the header re-done:
  `9 + 2·(1 + 2^17) + 2·1 + 2·597 = 263,351`, remainder `16,513,865 ≥ 2·2^16·125` for 960-byte
  queries. `Computes` still excludes enumeration (`enum_no_computes`, v3's).
- `Compose.walk`'s hypotheses are exactly those the design §2.4 states (functional `L`,
  `|L| ≤ logCap`, `μ L < 1`, `n ≤ chainCap`, `2^r` leaves, root accepted by `S.acc vk`); it
  recurses with the same `L` and the same event, as §2.4 item 4 says; `extract` computes the
  witness through `S.E`, not by choice. `leafCollision`/`nodeCollision`/`leafNodeCollision`
  are explicit tagged preimages.
- `runLog_of_runSeq`, `traceBytes_inj`, `traceDigest_eq`, `sigOk_sign` (every `sk`,
  `j < 2^16`, every `m`), `sigTrust_kstate_iff`, `accF_eq`: statements as the design quotes them,
  with the hypotheses the design names and no other.
- `Controls/Backdoor`: `backdoor` and `magic_needs_trigger` are the v3 probe under v4, as
  described; the control is honest about being what the model does not exclude.

## 2. Pass B: fidelity (byte layouts, v3 port)

Read `signer_ref.py` first, then the Lean.

| Item | Python (`signer_ref.py`) / BRIEF §4.2 | Lean | Verdict |
|---|---|---|---|
| `enc64` | `(n % 2**64).to_bytes(8,'little')` | `List.ofFn fun i : Fin 8 => (n / 256^i).toUInt8` | same |
| trace item | `enc64 |q| ‖ q ‖ a` under `0x54` | `traceBytes`, `traceDigest` | same; `traceDigest_kat` against hashlib |
| digits | `(b >> 2t) & 3`, `t = 0..3`, byte order | `b.toNat / 4^t % 4`, `flatMap` over bytes | same; `wotsDigits_order` (0x1B → 3,2,1,0) |
| checksum | `Σ(3 − d)`, digits `(C >> 2t) & 3`, `t = 0..4` | `(d.map (3 - ·)).sum`, `C / 4^t % 4` | same; `wotsDigits_zero` (384 → 0,0,0,2,1) |
| `F(j,i,s,x)` | `b'W' + e64(j) + bytes([i, s]) + x` | `tagWots :: enc64 j ++ [i.toUInt8, s.toUInt8] ++ x` | same, 43 bytes; `wotsStep_kat` |
| signature | `chain(j, i, 0, d_i, start)` | `sign`: `wotsChain j i 0 d (sk j i)` | same |
| verification | `chain(j, i, d_i, 3 − d_i, ots_i)` | `wotsEnds`: `wotsChain j i d (3 - d)` | same; tied by `sigOk_sign` |
| leaf | `b'K' + e64(j) + ends` | `wotsLeaf` | same, 4,265 bytes |
| node | `b'M' + l + r` | `sigNode` | same; `sigNode_kat` |
| path | `levels[t][(j >> t) ^ 1]`, left iff bit `t` is 0 | `sigRoot`: `j % 2 = 0 → sigNode x s` | same; `sigRoot_bits` |
| `SigOk` | `j < 2^16`, 133, 16, root = `vk` | four `decide`s | same |
| chain start | `blake2s(b'S' + e64(j) + bytes([i]), key=seed)` | `Signer.chainStart`: `blake2s seed 32 (0x53 :: enc64 j ++ [i])` | same (V4-A4); Library, keyed |
| tags | `C L N T W K M` = `43 4C 4E 54 57 4B 4D` | `Relation.lean` | same; `tags_separate` |

End to end, RESULT §4 reports the Lean signer's `vk` and signature byte-identical to the Python
reference (`logs/A-signer-time.txt`); since `sigOk_sign` ties `SigOk` to `sign`, that also checks
`SigOk` against an independent implementation.

v3 port: `Security`, `Machine`, `Tree`, `Hash/Blake2s` code-identical (`diff` on everything from
the first `import`/`namespace`); the header changes are accurate (Blake2s: "not the oracle", and
the keyed mode named). `Relation`, `Oracle`, `Extractor`, `Certificate`: the changes are those the
RESULT §1 and §6 list, nothing else (`tagRO`, `blake2sOracle`, `Vb`, `run`, `wordByte`,
`digestAt`, `bytesAt` gone; `queryCap`, tags `T W K M`, `Trace`, `Sig`, `Signed`, `runSeq`,
`logWords`, the readers added). The extractor input tape is definitionally v3's (`logWords`
factored out; `extractorInput_kat` unchanged). Pass B found nothing.

## 3. Pass C: hygiene and controls

- **Axioms.** `lake env lean --run scripts/AxiomAudit.lean`: PASS, every declaration of the 43
  `RecursionFast.*` modules within `propext`, `Classical.choice`, `Quot.sound`
  (`logs/ra-probes/axiom-audit.log`). Both probes also standard.
- **Forbidden tokens.** `grep` over `RecursionFast/` for `sorry`, `native_decide`,
  `implemented_by`, `extern`, `export`, `initialize`, `csimp`, `cpass`, `computed_field`,
  `unsafe`, `partial`, `opaque`, `admit`, `axiom`: only the words "partial table" and "partial
  product" in prose. No attribute and no `set_option` in `Contract/`.
- **Line budget.** `scripts/loc.py`: 355 code lines, 0 theorems in the contract.
- **Docstrings.** Every trusted definition has one, and they say what, not how (`readBytes`,
  `wotsEnds`, `sigRoot`, `acc` checked in particular).
- **Controls cover V4-A3** (`prog_runSeq_extra`, `ret_runSeq_nonempty`, `acc_query_at_cap`,
  `acc_query_over_cap`, `child_trace_nonempty`), **V4-A4** (`node_of_two_leaves_ref`,
  `sigOk_sign_ref`, `chainStartF_eq`), **V4-A7** (a)–(d) as RESULT §7 lists; each tests the
  contract's own definition (checked that no control is stated on a Library twin alone: the
  `F`/`B` twins appear only on the right of an `_eq`).

### RA-m1 (minor). The checksum argument has no control; `wotsEnds` has no negative

`Signature.lean` header: "Raising a message digit lowers a checksum digit, so no signature can be
advanced along its chains to sign another message." This is the one combinatorial lemma of the
WOTS argument (design §2.5 "Why"), it is kernel-provable without a hash, and nothing proves it.
RESULT §3 gives `wotsStep … wotsLeaf` the negative "through `SigOk`'s negatives", but those
(`idx`, lengths, other key) never reach `wotsEnds`; the positive `sigOk_sign` is what is
sensitive to the positions. **Fix:** Library theorem, cited from the header and listed as the
negative control of `wotsDigits`/`wotsEnds`:
`wotsDigits_dominates : m ≠ m' → ∃ i < wotsLen, (wotsDigits m')[i]! < (wotsDigits m)[i]!`
(digits injective on messages; if no message digit of `m'` is below `m`'s and they are not all
equal, `C' < C`, and `C' < C` forces some base-4 digit of `C'` below `C`'s).

### RA-m2 (minor). `Controls/Extractor` costs 116 s for one known answer evaluated twice

`decodeWit_node_kat` and `witWords_node_kat` each kernel-evaluate the 1,216-word node format;
`decodeWit_short_sig` runs the reader over all of `nodeKatWords.dropLast`. **Fix:** keep the
encoder KAT (`witWords nodeKat = nodeKatWords`, the runner's reference) and derive
`decodeWit_node_kat` from it with `decodeWit_witWords` as `decodeWit_trailing` already does;
state `decodeWit_short_sig` on the second child's signature words alone (`readSig` on 596
words). About half the module's time, answering RESULT open question 5 without losing the KAT.

### RA-m3 (minor). `Trace` and `Log` are two names for one type

`Relation.lean` `abbrev Trace := List (ByteArray × Digest)`; `Oracle.lean` `abbrev Log :=
List (ByteArray × Digest)`. Two trusted names, one type, definitionally interchangeable (the
Library passes a `Trace` where a `Log` is expected, `Log.Functional tr`). Minimality allows one
name, or `abbrev Trace := Log` with the docstring saying a trace is a log read in order. Not a
defect; one line.

### RA-m4 (minor). `lakefile.toml`'s header still says the library is an empty skeleton

The comment predates stage A and the stage D draft already on the branch (`07f6c14`); RESULT §1
defers it to stage D. It is outside `[[require]]` and can be corrected without `lake update`.

## 4. Verdict

**Pass, with RA-M1 and RA-M2 to fix before the stage is closed.** Neither changes a trusted
definition unless the orchestrator takes RA-M2's contract option; both are statements or
sentences weaker than the prose that cites them. The trusted base is the brief's and the
design's, byte for byte against the Python reference and code for code against v3 where
"verbatim" is claimed; the controls are non-vacuous and test the contract; axioms and tokens are
clean; the amendments V4-A3, V4-A4 and V4-A7 are implemented with the controls they asked for.

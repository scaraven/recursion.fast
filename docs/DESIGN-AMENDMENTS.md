# DESIGN amendments (for the orchestrator to patch into `docs/DESIGN-v3.md`)

Each item is tagged with the stage that produced it. It gives the agreed change and the wording to
put into `docs/DESIGN-v3.md`. The implemented Lean is the reference.

The v2 ledger (143 amendments, S1-A1 … S9-A44, applied to v2's `docs/DESIGN.md`) left the tree
with the v2 artifacts; git keeps it at the tag `v2-archive`
(`git show v2-archive:docs/DESIGN-AMENDMENTS.md`). The v2 finding and amendment IDs cited in code
comments and in the design resolve there.

## V3-S1 (the v3 contract and its controls; DESIGN-v3 §11 step 1, 2026-10-19)

For the orchestrator to patch into `docs/DESIGN-v3.md`. The implemented Lean is the reference;
`docs/stages/V3-S1-RESULT.md` has the measurements. Items marked **open** need a decision.

- **V3-S1-A1 (file order; §1.1, §8).** `Oracle.lean` uses `Digest`, so the reading order is
  `Hash/Blake2s` · `Relation` · `Oracle` · `Security` · `Machine` · `Extractor` · `Tree` ·
  `Certificate` (`RecursionFast/Contract.lean`). §8 table: 320 code lines in all (`scripts/loc.py`):
  Contract.lean 8, Hash/Blake2s 68, Relation 22, Oracle 19, Security 23, Machine 110,
  Extractor 33, Tree 7, Certificate 30.
- **V3-S1-A2 (Machine; §8, §10).** `Machine.lean` imported the deleted `Field.lean` for `Word` and
  `K.clmul`. `clmul` moved into `Machine.lean` verbatim (namespace `K` dropped); `Word` is the
  vendored model's global notation for `BitVec 64` (v2's `abbrev` denoted the same type, and a
  new `abbrev Word` cannot be declared after the vendored import). The header's tape paragraph no
  longer describes field elements. No instruction semantics changed; the v2 machine controls are
  re-run (`Controls/Machine.lean`). §8: "unchanged" → "unchanged semantics, `clmul` moved in"
  (109 → 110 code lines).
- **V3-S1-A3 (hashing a byte string to a digest; §2.1, §3.2).** `Hash/Blake2s.lean` is unchanged
  (`blake2s256 : List UInt8 → List UInt8`). The relation and the oracle hash through
  `blake2sDigest : List UInt8 → Digest` (`Relation.lean`). §2.1's code reads
  `blake2sDigest (tagLeaf :: h.toList ++ enc64 n)`, `blake2sDigest (tagNode :: c₁.toList ++ c₂.toList)`,
  `chainEnd s n = (fun d => blake2sDigest d.toList)^[n] s`; §3.2's `Vb` uses
  `blake2sOracle q = blake2sDigest (tagRO :: q.data.toList)`.
- **V3-S1-A4 (Digest representation; §2.1).** `abbrev Digest := Vector UInt8 32`, not
  `Fin 32 → UInt8`. A function-typed digest is a closure that compiled code re-evaluates on every
  byte read, so a chain step costs 32 evaluations of the previous step: measured (interpreter)
  600 ms for 2 steps and 15.5 s for 3 steps, i.e. `32^n` (`logs/V3-S1/digest-probe/`); the
  vector computes 1,000 steps in 428 ms and is faster in the kernel too (16-step chain: 28.7 s
  against 35.5 s). `Nat.card Digest = 2^256` is a library theorem (`Library/Security.lean`,
  `card_digest`), not part of the contract.
- **V3-S1-A5 (tags and encodings; §2.1, §3.4).** One-byte prefix tags `tagLeaf = 0x4C` ('L'),
  `tagNode = 0x4E` ('N'), `tagRO = 0x52` ('R'); `enc64 n` = the 8 little-endian bytes of
  `n mod 2^64`. Preimages: leaf 41 bytes, node 65 bytes, oracle query `1 + |q|` bytes.
- **V3-S1-A6 (open: chain steps are not domain-separated from oracle queries; §3.4).** §3.4 says
  "the proof system never queries a string the relation hashes". Chain steps hash untagged
  32-byte strings, so an oracle query of 31 bytes (instantiated input `tagRO ‖ q`, 32 bytes)
  equals the chain step of every digest whose first byte is `0x52`. No prefix scheme avoids a
  32-byte oracle input. Options: (a) tag the chain, `chainEnd` hashes `tagChain ‖ d` (33 bytes,
  still one compression, no cost; the leaf workload becomes a tagged chain); (b) instantiate the
  oracle with keyed BLAKE2s (separated at the parameter block from every unkeyed call; one extra
  compression per query); (c) accept and say so in §3.4/§5.4 (it touches only the ROM heuristic,
  not the theorem). Recommendation: (a). Not implemented: `Rel` is "exactly as §2.1".
- **V3-S1-A7 (extractor tape and output; §4.4).** Normative formats, in `Extractor.lean`'s header.
  - Input `extractorInput c π L`: `c` (4 words), `|π|`, π packed, `|L|`, then per entry `|q|`, q
    packed, the answer (4 words). Bytes are packed 8 per word little-endian (`packBytes`); every
    field is word-aligned; numbers are their low 64 bits.
  - **Deviation.** `ImageComputes` does not require the output to *equal* a serialisation of
    `E c π L`; the output must **denote** it through the contract's total decoder `decodeWit`
    (`[]` and unknown tags: `none`; tag 0 leaf: start, length word; tag 1 node: two digests and
    two length-prefixed proofs). Reason: §7.3's baseline image "copies its input to its output".
    With an exact serialisation the image must validate the proof and print `[]` on garbage; with
    the decoder, the witness-sending extractor `E := decodeWit ∘ packBytes` is computed by an
    8-instruction image that outputs the proof's words in place (`tests/asm/proofwords.S`). The
    encoder `witWords` and `decodeWit (witWords w) = some w` are library facts
    (`Library/Words.lean`).
  - A leaf length is one output word, so an output denotes only `n < 2^64`. Nothing is lost: a
    leaf statement with `n ≥ 2^64` also has the witness `(chainEnd s (n − n mod 2^64), n mod 2^64)`
    (`enc64` reads `n mod 2^64`; `WitnessSending.rel_norm`).
- **V3-S1-A8 (tree convention; §5.1).** `treeLevel` pairs adjacent digests with `nodeStmt` and
  carries an odd last digest up unhashed; `treeRoot cs = (treeLevel^[|cs|] cs).headD 0`: one
  digest is its own root, the empty list has the zero digest. The runner always has `2^r` leaves
  (r ≥ 0) and the Python twin must follow the same definition; known answer for four leaves in
  `Controls/Tree.lean` (`treeRoot_kat`).
- **V3-S1-A9 (`CompleteWithError` not in the contract; §4.3, O-23).** Only perfect completeness
  is defined. The counted form and its cap `δ ≤ 2^-64` wait for O-23; a submission needing
  grinding cannot be certified until then.
- **V3-S1-A10 (`Declared`, `CertificateR`; §3.2).** `Declared = {img, ε, qV, fuel}` (the image a
  literal rendered from the submitted files, the numbers rendered from the claim; `fuel` a
  rendered function of `(|π|, |L|)`). `CertificateR D S` extends `Certificate S` with
  `S.img = D.img` and `S.ε ≤ D.ε ∧ S.qV ≤ D.qV ∧ ∀ p l, S.fuel p l ≤ D.fuel p l`: the record
  reports the declared numbers as bounds that hold. The harness's liveness check may run the image
  with `D.fuel`, since more fuel does not change a halting run (`Library/Machine.lean`,
  `run_mono`).
- **V3-S1-A11 (`ImageComputes` domain, output cap, image cap; §4.4, §6.6).** (1) The domain adds
  "the input tape has at most `2^60` words": the machine addresses `2^60` tape words, so no image
  could answer for a longer tape (queries are unbounded, so `L ≤ 2^24` entries does not bound the
  tape). (2) The output cap is a conjunct: the output has at most `outCap = 2^24` words.
  (3) The image cap `imageCap = 2^20` bytes is the fourth conjunct of `Certificate.cap`
  (§3.2 has three).
- **V3-S1-A12 (budget; §4.4, O-21).** `extractorBudget p l = 2^40 + 2^8 · (p + l)` with `p` the
  proof's bytes and `l` the log's entries (as in §4.4). Justification and its limit, in
  `Extractor.lean`'s header: `2^8` steps per entry suffice to index the log by answer (32-byte
  keys) and `2^40` covers a quasi-linear decoder of a `2^20`-byte proof; an extractor that compares
  query *contents* entry by entry can exceed the budget on an adversarial log of `2^24` long
  queries. If O-21 wants robustness to that, make `l` the log's size in words.
- **V3-S1-A13 (the accept-everything control; §4.2 "Vacuity controls").** "A verifier that
  accepts everything admits no `KState` (final fails on a statement with no witness)" cannot be
  kernel-checked for `Rel`: it needs a digest outside the images of `leafStmt` and `nodeStmt`, and
  if `nodeStmt` is onto (2^512 inputs, 2^256 outputs) there is none, and then the accept-all
  verifier has a knowledge state with an unbounded (choice) extractor. The control proves the
  exact statement (`Controls/Security.lean`, `acceptAll_kstate_iff`: a knowledge state exists for
  some extractor iff every statement has a witness) and the two instances that hold (empty
  relation; extractor returning nothing). What excludes the accept-all verifier is `computes`:
  an image within `B p l` steps would have to invert BLAKE2s. §4.2's reading should say that
  `KState` makes knowledge soundness and `ImageComputes` makes it efficient, and the second is
  load-bearing.
- **V3-S1-A14 (open: completeness over every chain length; §2.1, §2.2, §4.3).** `Complete`
  quantifies over every `Rel` witness, so over leaves of every length `n ∈ ℕ`, while §2.2 calls
  `2^4 … 2^20` the range of `n`. A SNARK whose leaf circuit covers a range of `n` must accept
  honest proofs for every other `n` too, by a fallback (e.g. sending the witness); then `Vb`
  accepts fallback proofs, a node's children may be fallback proofs, and the node circuit (which
  cannot recompute an unbounded chain) needs a fallback as well. The witness-sending argument is
  complete for every `n` (`rel_norm`). Options: (a) bound `n` in `Rel`'s leaf clause, e.g.
  `n ≤ 2^20` (then also `n < 2^64`, and V3-S1-A7's remark disappears); (b) keep `Rel` and supply a
  library fallback combinator (S4). Recommendation: (a).
- **V3-S1-A15 (the witness-sending argument is a library module; §7.3, V3-9).**
  `Library/WitnessSending.lean` is the argument of §7.3 with a full `Certificate` (`certificate`;
  `ε = 0`, `qV = 0`, `fuel = 8`, an 8-instruction image). Its proof of `w` is the bytes of
  `witWords w`; a proof over `r` levels has `136 · 2^r − 88` bytes (34,728 at `r = 8`; it passes
  `proofCap` at `r = 13`, `Controls/Relation.lean`, `deep_accepted_but_capped`). Its prover
  normalises `n` (V3-S1-A7). Here it is the certificate's positive control (a harness fixture,
  like v2's toy), not an entry (V3-12); the baseline entry that S2 builds in the submissions
  repository (§7.7) can import it from the library or copy it.
- **V3-S1-A16 (for S3, the harness).** (1) The extractor's log in the liveness check must contain
  the verifier's queries as well as the prover's (the `final` law reads `V` from the log;
  `Library/Oracle.lean`, `runLog_eq_run`). (2) The Python decoder of the output is `decodeWit`.
  (3) `scripts/AxiomAudit.lean` imports `RecursionFast.Bridge`, which is deferred: `lake exe
  axiomaudit` fails until S4 or until its module list drops it (V3-S1 ran a copy over
  Contract, Library, Controls: PASS). (4) The gate's allowlist and manifest still name the v2
  contract modules; the challenge stubs `RecursionFast/Challenge/*.lean.in` and the renderer are
  v2's.
- **V3-S1-A17 (legacy and deferred targets; §10, §11).** The v2 Library and Controls modules that
  no longer build moved unchanged to `legacy/v2/` (not a lake target; `legacy/v2/README.md`);
  `Library/Blake2s.lean` and `Controls/Blake2s.lean` stay; the machine lemmas and controls were
  re-homed (`Library/Machine.lean`, `Controls/Machine.lean`). `RecursionFast/Bridge/` and
  `RecursionFast/Clean/` stay in place with their lake entries. Deferred targets:
  `RecursionFastCandidate` (S2: the baseline moves to the submissions repository, §7.7),
  `RecursionFastHarness`, `RecursionFastSmoke`,
  `harness-linkcheck` (S3), `RecursionFastBridge`, `RecursionFastClean` (S4).
- **V3-S1-A18 (note: `Complete` is about `V`, `Rel` about `Vb`; §4.3).** A verifier that accepts
  only proofs above `proofCap` can be certified (its `Vb` rejects everything, so no node witness
  exists and completeness is about leaves only), but no run scores, since the root check uses
  `Vb`. Requiring `|P c w| ≤ proofCap` in `Complete` would close this and would also exclude the
  witness-sending baseline (a node's honest proof can exceed the cap even when both children are
  under it), so it is not done.

## V3-S1 fix pass (after the review `docs/reviews/V3-S1-review.md` and the orchestrator's decisions, 2026-10-19)

The design text of `54140d1` already carries decisions (a)–(d) and O-25; these items record what
the Lean does and where it differs from that text.

- **V3-S1-A19 (decision c: the chain step is tagged; closes A6).** `tagChain = 0x43` ('C');
  `chainStep d = blake2sDigest (tagChain :: d.toList)` (33 bytes, one compression);
  `chainEnd s n = chainStep^[n] s`. Four tags with distinct first bytes (0x43, 0x4C, 0x4E, 0x52):
  no chain, leaf or node preimage is an oracle input; the relation hashes oracle inputs only
  inside `Vb` in the node clause (the recursion). Control `tags_separate` states this
  structurally (review m7). All chain known answers recomputed with `b'C'+d`.
- **V3-S1-A20 (decision b: `chainCap`; closes A14).** `chainCap = 2^20` in `Relation.lean`; the
  leaf clause is `n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n`, the bound first. `enc64` is kept
  (injective on the admitted range). The library's normalisation (`norm`, `rel_norm`,
  `enc64_mod`, `chainEnd_chainEnd`) is deleted: every witness of the relation fits the output
  format (`WitnessSending.fits_of_rel`), and the honest prover sends the witness unchanged. Also
  closes the submissions agent's finding that a proof declaring a huge `n` could drive a
  chain-recomputing verifier past its time cap.
- **V3-S1-A21 (decision d and review M3: the budget is over the tape; no entry bound).**
  `extractorBudget t = 2^40 + 2^8 · t`, `t` the input tape's length in words;
  `Submission.fuel`, `Declared.fuel : ℕ → ℕ` of the tape length; `ImageComputes` runs the image
  with `fuel (extractorInput c π L).length` and quantifies over every log whose tape fits the
  machine's `2^60` words (the `2^24`-entry bound is gone, so efficient extraction covers up to
  `2^58` entries); `Certificate.cap` reads `∀ t, S.fuel t ≤ extractorBudget t`. Review m9:
  `CertificateR.bounds` also requires `D.fuel t ≤ extractorBudget t`, since the harness runs the
  image with the declared fuel. The name `CertificateR` is kept ("the certificate against the
  rendered claim"); its v2 meaning (recursion board) is gone, which S3's gate, renderer and stubs
  must not carry over. **Design text still to align:** §3.2's code block (`fuel : ℕ → ℕ → ℕ`,
  `∀ p l, S.fuel p l ≤ B p l`), §8's table (`B p l`) and O-21's text.
- **V3-S1-A22 (review m5: `decodeWit` caps child lengths).** A node output whose child length
  exceeds `proofCap` denotes `none`, so no 10-word output denotes a `2^63`-byte proof (a
  memory-exhaustion vector for the Python twin). No witness of the relation is lost. `Wit.Fits`
  for a node is now "both proofs within `proofCap`". The extractor header now says that the
  decoder's leniency on malformed proofs (zero reads, ignored trailing words) is what lets the
  witness-sending image output its proof in place (the submissions agent's finding).
- **V3-S1-A23 (decision a and review M1: what the certificate does not exclude).** The
  `Security.lean` and `Certificate.lean` headers now say: `KState` alone excludes little
  (`acceptAll_kstate_iff`, now in `Library/Security.lean`); the knowledge content is `KS` with the
  named extractor, its image and budget; and a `V` that recognises the deployment oracle is
  certified (O-25). `Controls/Backdoor.lean` is the review's `Probe.Backdoor2`, adapted, as a
  known-gap control: `backdoor : Certificate S ∧ ∀ c, S.Vb c (magic c) = true ∧
  (magic c).size = 32`, kernel-checked.
- **V3-S1-A24 (`OProg.queries` argument order; §3.1).** `queries (H) : OProg α → List ByteArray`,
  the oracle first, as `run H` and `runLog L` (the golf report's note). Every use reads
  `(V c π).queries H` and is unchanged; §3.1's signature line should follow.
- **V3-S1-A25 (review M4: the committed state builds what it lists).** `RecursionFast/Bridge*`
  and `RecursionFast/Clean*` moved to `legacy/v2/` (`git mv`). In `lakefile.toml` nine blocks are
  commented out, each with the stage that restores it: `RecursionFastBridge`, the `Clean` path
  requirement, `RecursionFastClean` (S4); `RecursionFastCandidate` (S2, the baseline moves to the
  submissions repository); `RecursionFastHarness`, `harness-linkcheck`, `RecursionFastSmoke`,
  `smoke-verify`, `smoke-index` (S3). `lake-manifest.json` is unchanged and nothing needs
  `ext/Clean`. `scripts/AxiomAudit.lean` no longer imports the Bridge; `lake exe axiomaudit`
  passes as shipped. **S3 owes:** the olean manifest regenerated from a v3 organiser build,
  `scripts/org-build.sh` and `scripts/ci.sh` for v3 (steps 2, 3, 5–12 fail today), the gate's
  allowlist, the renderer and the challenge stubs.
- **V3-S1-A26 (trusted text and library).** Stale headers of `Hash/Blake2s.lean` and
  `Machine.lean` rewritten and three long lines wrapped (no definition changed; review m8, m12);
  `Library/Tree.lean` proves `treeRoot`'s docstring (`|cs|` levels suffice, and the root of two or
  more digests is the root of the level above).

## v2 removal (after V3-S1 merged into `main` at `069b1a6`, 2026-10-19)

- **V3-S1-A27 (the v2 tree removed; §8, §10, §11).** Everything v2-specific was deleted from the
  tree in one pull request after V3-S1 merged; git keeps it at the tag `v2-archive` (the merge
  commit `069b1a6`, the last with the v2 tree). Removed: `legacy/v2/` (A17, A25: the parked v2
  Library, Controls, Bridge and Clean modules); `submissions/baseline/` (`P_triv`, v2 S7; the
  baseline is the submissions repository's first entry, §7.7); `probes/` (the v2 stages' probes,
  s1–s9 and clean-build); `harness/` (`L_chain(n)`, the badge path, the smoke protocol, the v2
  runner, `reference-machine.md`); `audit/` (the v2 toy and the comparator configurations);
  `RecursionFast/Challenge/*.lean.in` (the v2 stubs); `tests/pipeline/`; the v2 scripts `ci.sh`,
  `harness.sh`, `org-build.sh`, `render-challenge.py`, `dummy-claim.py`, `toy-solution.py`,
  `test-render.sh`, `setup-clean.sh`, `tools.env`; the v2 data `olean-manifest.sha256`,
  `import-allowlist.txt`, `import-frontend.txt`; the images `tests/asm/{brute,copy,long,long32,
  section3}` that no v3 control uses; v2's `docs/DESIGN.md`, `docs/RESULT.md`,
  `docs/stages/S1–S8`, `docs/reviews/S1–S9`, `docs/upstream/` and the v2 part of this ledger. The
  nine commented-out `lakefile.toml` blocks (A25) and the `Clean` entry of `lake-manifest.json`
  are gone; the four pinned requires (CompPoly, ArkLib, VCVio, PolyFun) stay.
  - **Kept, as §10 carries them over unchanged:** `scripts/Gate.lean`, `source-rule.py` with
    `tests/source-rule/` and `TokenSweep.lean`, `AxiomAudit.lean`, `olean-manifest.py`,
    `bwrap-landrun.sh`, `check-vendor.sh`, `check-hygiene.sh`, `loc.py`; the eight images the
    controls assemble. `scripts/ci.sh` is new and minimal: the vendor check, hygiene, the
    source-rule fixtures, `lake build`, the axiom audit, the line budget. The full harness order
    (comparator, organiser package, manifest, gate, stubs, renderer, runner) is S3's, as A25 said.
  - **§8 item 1** names `scripts/olean-manifest.sha256`, which does not exist until S3 regenerates
    it from a v3 organiser build. **§8 "Not trusted"** names `Bridge/`, `Clean/`, `probes/` and
    the baseline, none of which is in the tree.
  - **§10 rows** "Clean bridge, ArkLib bridge: kept, untrusted" and "`gen-chain-layout.py`,
    `check-chain.py`, `L_chain(n)`: library examples" now read from the tag: S4 restores from
    `v2-archive:legacy/v2/RecursionFast/{Bridge,Clean}/` and `v2-archive:harness/` what it
    re-targets. The row "`submissions/baseline/` moves to the submissions repository" is done on
    this side; the entry itself is S2.
  - **§11 S2**: "allowlist and manifest regenerated" has nothing to regenerate from and is S3's
    with the rest of the harness. **§11 S5**: `docs/DESIGN.md` no longer exists; S5 is the v3
    handover `docs/RESULT.md` and this ledger.
  - **External pins that lived in `tools.env`** (for S3): leanprover/comparator `d03acab` (its
    lean4export `076e8e5`), ammkrn/nanoda_lib `3a24072`.
  - Module headers that named `legacy/v2/` paths (`Library.lean`, `Controls.lean`,
    `Library/Machine.lean`, `Controls/Machine.lean`, `scripts/AxiomAudit.lean`) now name the tag.
    No trusted file changed. The stage records (`docs/stages/V3-S1-RESULT.md`, the V3-S1 review
    and golf reports) are history and still say `legacy/v2/`; read that as the tag.

## V3-KS (the potential knowledge state and the log-length guard; branch `v3/ks-potential`, 2026-10-19)

A contract amendment from the submissions repository's SNARK-baseline ideation (its
`docs/snark-baseline/notes/F1-ks-feasibility.md` §1, §2, §4, kernel-confirmed by
`notes/ADV1-rules-review.md` ADV-M2, ADV-M3 with the probes in its `logs/adv-probes/`). The S1
counting form is unsatisfiable at `errorCap` for every Merkle-committing verifier (unbounded logs:
collision and late-preimage bad sets grow with the log) and for every query phase whose
positions span several answers (one bad set per answer charges the largest conditional). The
implemented Lean is the reference; `docs/stages/V3-S2-KS-RESULT.md` has the measurements. For the
orchestrator to patch into `docs/DESIGN-v3.md` (and its master in the design workspace).

- **V3-KS-A1 (the potential form; §1.1 figure, §4.1, §4.2).** `KState R V E ε` is a structure
  with a potential `μ : Log → ℝ≥0` and three laws: `empty : μ [] = 0`; `step : ∀ L q,
  L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst → ∑ a : Digest, μ (L ++ [(q, a)]) ≤
  (μ L + ε) * 2 ^ 256` (the literal since the fix pass, A7); `final : ∀ L c π, L.length ≤ logCap → μ L < 1 →
  (V c π).runLog L = some true → ∃ w, E c π L = some w ∧ R c w`. The error is a parameter of the
  structure; `KState.Bounded` is gone; `KS R V E ε qV := Nonempty (KState R V E ε) ∧
  ∀ H c π, ((V c π).queries H).length ≤ qV`. `Certificate` and `Complete` are unchanged.
  - **`Fintype Digest` in the contract** (Mathlib has none for core `Vector`): one instance,
    `Fintype.ofSurjective` of `Vector.ofFn ∘ UInt8.ofFin` from `Fin 32 → Fin 256`, three lines.
    Chosen over summing over `Fin 32 → Fin 256` in `step` because the law then reads as the
    average over the answers, and because any `Fintype` instance lists each digest exactly once
    (`Fintype` is a subsingleton), so the instance carries no trust. The bound is written with
    the literal `2 ^ 256` (A7); `Library/Security.lean` proves it is the number of digests
    (`fintype_card_digest`).
  - §4.1's "a state predicate on logs and a bad-answer predicate … the union bound" becomes "a
    potential on logs whose average rise per fresh query is at most `ε` …; a stopped
    supermartingale and Markov's inequality are the paper theorem". §4.2's code block is the
    contract's text; its **Reading** paragraph: "`μ L` measures how close the table `L` is to
    admitting an accepted-but-unextractable proof; `final` is the promise below `1`; `step` says
    that, below `1` and within `logCap`, the average over the `2^256` answers to a fresh query of
    the next potential is at most `μ L + ε`. A boolean state (`good`, `bad`, at most `ε·2^256` bad
    answers) is the potential `0`/`1` (`KState.ofBool`); the potential also prices a challenge
    spread over several answers, which no boolean state can (`Controls/Potential.lean`)." The
    controls sentence: "`bad := True` is `Bounded` only at `ε ≥ 1`" becomes "a potential that is
    `1` off the empty log needs `ε ≥ 1`"; the witness-sending argument's state is `μ := 0`.
  - §8 table: `Contract/Security.lean` 26 code lines (S1: 23); the contract 331 (S1 fix pass:
    328). Trust statement item 5: "the paper union bound of §4.5 from the counting form" → "the
    paper bound of §4.5 from the potential form (a stopped supermartingale and Markov)".
- **V3-KS-A2 (the log-length guard; §4.2, §4.5, §6.6).** `logCap = 2^96` (`Security.lean`;
  `2^64` before the fix pass, A6). `step` constrains logs of fewer than `logCap` entries, `final`
  logs of at most `logCap`. Reason: a Merkle commitment binds only up to collisions and late
  preimages, whose bad sets have one element per earlier digest of the log; over unbounded logs no
  state exists at `errorCap` (`Controls/Potential.lean`, `collision_no_bool_kstate`, the ADV1
  probe). **What the guard gives up:** S1's form claimed `(Q + qV)·ε` for every `Q`; the amended
  form claims nothing for `Q + qV > logCap`. (The first version said the theorem "says nothing
  once `Q + qV ≥ 1/ε` anyway"; at `ε = 2^-128` that is `2^128`, not `2^64`, so the sentence was
  false: review M1.) Within the guard a `t`-bit comparison costs about `logCap · 2^-t` per query,
  so the value of `logCap` fixes which collision-type events are chargeable at `errorCap`: at
  `2^96`, those of at least `224` bits (birthday cost `2^112`); a full digest costs `2^-160`
  (`colBool_below`), an honest Merkle verifier comparing at most `2^15` digests per query about
  `2^-145`. §4.5 becomes: "For every adversary making `Q` oracle queries with
  `Q + qV ≤ logCap`, the probability over the random oracle that it outputs `(c, π)` with
  `V^H c π = true` and `E c π L ∉ Rel c` is at most `(Q + qV)·ε`: along the fresh queries,
  `min 1 μ`, stopped when `μ` first reaches `1`, rises by at most `ε` in expectation per query
  (`step`), so it reaches `1` with probability at most `(Q + qV)·ε` (Markov); otherwise the final
  log is within `logCap` with potential below `1`, and `final` extracts (kernel-checked for a
  lazily sampled oracle: `Library/PaperTheorem.lean`, `paper`). At the caps an adversary with
  `2^64` queries has advantage `≤ 2^-64`, with `2^96` queries `≤ 2^-32`; nothing is claimed
  beyond `logCap`." §6.6 gains a row: "log length covered by the knowledge laws | `logCap = 2^96`
  (contract constant)". The extractor's tape bound (`2^60` words, V3-S1-A21) presupposes fewer
  than `2^58` entries for *efficient* extraction; `logCap` bounds the logs the laws cover, not the
  image's input.
- **V3-KS-A3 (library; §9).** `Library/Security.lean`: `BoolKState` (the S1 structure) with
  `Bounded` (the S1 bound), `BoundedBelow` (the same on logs shorter than `logCap`),
  `Bounded.below`, `bounded_of_not_bad`, `Bounded.mono`, `one_le_of_bounded`; `KState.ofBool`
  (a `BoundedBelow ε` boolean state is the potential `0` on good logs, `1` elsewhere, at error
  `ε`), `KState.ofBool_μ_eq_zero`; `KState.zero` (potential `0` when every accepted proof is
  extracted on every log, at every error), `KState.mono`; `step_of_hits` (a rise of at most `1`,
  only on a set `T` with `|T| ≤ ε·2^256`, discharges `step`); `KState.one_le_of_jump`;
  `fintype_card_digest`, `card_digest`; `no_kstate_of_empty` and `acceptAll_kstate_iff` now at
  every error. `Library/WitnessSending.lean`: `kstate := KState.zero 0 …`.
- **V3-KS-A4 (controls).** Every S1 control is ported with its meaning (the RESULT's table).
  New, `Controls/Potential.lean`: `twoLucky` (two fixed queries, accept iff both answers start
  with 12 zero bytes, empty relation; ROM error `2^-192`): a potential at `ε = 2^-192`
  (`twoLucky_kstate`, `twoLucky_ks` at the cap with `qV = 2`), and no boolean state below
  `2^-96`, even on short logs (`twoLucky_bool_ge`, `twoLucky_no_bool_kstate`): the potential, not
  the guard, is what admits it. `Vcol` (accept a proof naming two distinct queries with equal
  answers; ROM error `≤ (Q+2)²/2^257`): no boolean state at `errorCap` over unbounded logs
  (`collision_no_bool_kstate`), the boolean state "answers distinct" bounded at `2^-160` within
  the guard (`colBool_below`) and so a potential at the cap (`colState`, `collision_ks`): the guard
  is what admits it. **Simplified:** F1's `merkleToy` (dangling Fiat–Shamir transcripts, then a
  hit on one of `2^128 + 1` committed roots) is not built; `Vcol` is its collision half. Not
  kernel-checked: that a *potential* for `Vcol` (not only a boolean state) needs the guard at
  `errorCap` (F1 §4.1, third row). `Backdoor.lean` is unchanged in substance (`KState.ofBool` of
  its S1 state; the O-25 gap is unchanged).
- **V3-KS-A5 (documents outside this repository).** The submissions repository's `AGENTS.md` §4
  and `docs/baseline/BASELINE-TASK.md` §0 and §5 describe `good`/`bad`/`Bounded`; they follow the
  pin move (the baseline's state becomes `KState.zero 0 …`, `μ := 0`). `docs/DESIGN-v3.md` here and its master are left to the orchestrator (this ledger).

### V3-KS fix pass (after the review `V3-S2-KS-review.md` in the submissions repository and the orchestrator's decisions, 2026-10-19)

- **V3-KS-A6 (review M1: `logCap = 2^96`).** The value moves from `2^64` to `2^96` (the
  reviewer's recommendation), and every "says nothing once `Q + qV ≥ …`" sentence is corrected
  (contract header, A2). New controls (`Controls/Potential.lean`): `V24` (accept two distinct
  queries whose answers agree on 24 bytes, 96-bit generic security). Under `2^64` the review's
  `Probe.v24_ks` certified it at `errorCap`; under `2^96`, `v24_no_bool_kstate`: no boolean state
  is bounded at `errorCap`, even on short logs (a log of `2^64 + 1` distinct prefixes leaves
  `> 2^128` bad answers), while `v24_ks` holds at its natural `2^-96`. Not kernel-checked: that no
  *potential* of `V24` exists at `errorCap` under `2^96`. `colBool_below` becomes `2^-160`.
- **V3-KS-A7 (review m2, m3; the paper theorem).**
  - `step` reads `(μ L + ε) * 2 ^ 256` (the literal; Q1 of the RESULT). This removes
    `Fintype.card Digest` from every goal a submitter meets, which is what made naive tactics fail
    with "maximum recursion depth" (m2). The instance stays, for `∑ a : Digest`;
    `fintype_card_digest` is now `@[simp]`.
  - `Library/PaperTheorem.lean`: the review's kernel-checked paper theorem (`Probe.paper`, from
    the submissions repository's `logs/ks-review-probes/PaperTheorem.lean`), moved with only the
    constant changed: for a lazily sampled oracle and a game of at most `n ≤ logCap` queries, the
    probability that the verifier accepts on the final table and the extractor fails is at most
    `n · ε`. Cited in the contract header.
  - m3: the statement is kept; the docstrings of `step` and `final` say that `μ L < 1` in `step`
    and the length bound in `final` are redundant, with the library theorems
    `KState.step_unstopped` and `KState.final_unguarded` (the review's `Redundant.lean`); the
    header names `step`'s length bound as the load-bearing restriction.
- **Answered, not changed.** m1 (a control that the guard is needed for a *potential*): not built;
  for `Vcol` it is borderline false at exactly `2^-128`, and the candidate (`V31`) is a paper
  argument (`Controls/Potential.lean` header). m4 (`Fintype (Vector UInt8 n)` instances in
  CompPoly `Data/Bytes/Bias`, VCVio `SampleableType/Basic`, ArkLib `OracleReduction/Prelude`):
  **note for S3's allowlist regeneration**: admitting one of these modules is sound (subsingleton)
  but rewriting with its card lemma against a contract goal can unfold the instance; entries use
  `fintype_card_digest`. m5: `docs/DESIGN-v3.md` (core and master) is patched by the orchestrator
  from these entries; the submissions repository's `AGENTS.md` §4 and `BASELINE-TASK.md` §0, §5
  are stale until the pin moves (and `AGENTS.md` should name the tactics to avoid on
  `Fintype.card Digest`, m2). m6: the four unused boolean lemmas now have controls
  (`Controls/Security.lean`: `bool_bounded_ge_one`, S1's `bounded_ge_one` verbatim on
  `BoolKState`; `badAllBool_not_capped`; `rejectAllBool_bounded`; `rejectAllBool_μ`).

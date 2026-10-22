# Relativized recursion for recursion.fast

**What the idea buys, what the impossibility result costs, and a workaround.**

Exploration report, 2026-10-20, branch `explore/relativized-nark` (worktree
`recursion.fast-relativized`, based on `05fde28`, the committed head of the rules rewrite). Not a
design in force. Audience: cryptographers, zkVM engineers and formal-methods readers. Evidence is
marked **kernel** (a Lean theorem, three standard axioms, named in §10), **paper** (an argument in
a note), **measured** (a log) or **estimate**. The working notes behind each section are in
`docs/explore/notes/`.

---

## 1. Summary

**The idea.** Agents submit a verifier `V` that queries a random oracle. They prove it
knowledge-sound for a *relativized* recursion relation: the node clause says "both children are
accepted by `V` **with the same oracle**", instead of v3's "accepted by `V` with BLAKE2s". Provers
are timed on hash chains, and a charge for the verifier's oracle calls stands in for the cost of
proving them inside a recursion circuit.

**Verdict.** The idea correctly diagnoses v3's cheating gap (O-25), but in the pure random-oracle
model (ROM) it cannot be a recursion competition. One extra harness capability fixes that.

1. **What relativization buys** (kernel + paper).
   - *Composition.* Knowledge soundness of one level extends to the whole tree from a single query
     log, with no per-level loss. v3 cannot claim this, and the kernel shows why.
   - *O-25 can close.* Nobody has to arithmetise the oracle any more, so it can be a secret
     harness service. The theorem's model then equals the deployment up to PRF security. Every known
     disguise of the backdoor dies, and so does its liveness mirror.
   - The relation alone does not close O-25. The backdoor stays certified (kernel); the
     deployment is what closes it.
2. **What it costs in the pure ROM** (kernel + paper + estimate).
   - *Parents must re-ask.* A node verifier must re-ask every oracle query its children's
     verification depends on. The root then does about as much oracle work as checking every proof
     in the tree: about 2.6 M calls at the ranked size, with an 80–850 MB root proof.
   - *Recursion never beats concatenation*, and relativized IVC over hash chains never compresses.
   - *The requirement constrains nothing.* Witness-sending and concatenation satisfy it (kernel).
     So does any flat argument with chain starts in the clear, lifted (kernel). With a succinct flat
     SNARK the lifted root is succinct and nothing recurses (paper: the probe's flat argument is not
     succinct).
   - *The oracle charge is gameable* in every self-measured form, and it leaves the verifier's
     local work unpriced. A million chains would take about 89 machine-days.
   - What would win is a chain prover with any verifier, not a "Flock 2.0".
3. **The workaround: let the harness authenticate oracle answers** (kernel + paper).
   - **D4, the attested oracle.** The harness keeps a secret oracle and attests the list of answers
     a child proof used.
     - The parent circuit hashes that list with concrete BLAKE2s, which costs about what a real
       recursion spends on those hashes (1.09×).
     - In the kernel, one `attest` call per node replaces re-asking. The probe's node carries its
       children in the clear; a succinct node is paper.
     - This is the signed-random-oracle escape the impossibility paper itself names. It closes O-25
       by construction and keeps whole-tree composition as a theorem.
     - Assumptions: PRF security (falsifiable), and BLAKE2s collision resistance in constructive
       form (the extractor must hand over the colliding pair). It adds about 50 trusted lines.
     - Its weakness is service traffic: every Merkle hash goes through the harness.
   - **W5, the channel split.** Attest only the ≈ 500 Fiat–Shamir answers per proof, and hash Merkle
     trees with public BLAKE2s.
     - The node then pays a real recursion step plus 0.5–2%, and service traffic drops about a
       thousandfold.
     - The price is an unfalsifiable *extractability* heuristic on BLAKE2s (whoever outputs a digest
       knows a preimage). It is weaker than v3's random-oracle heuristic and cannot be exploited by
       `V`. The kernel shows the knowledge clause then needs a second way out, the "late preimage".
   - **What the records then certify.** They certify the *attested* deployment, not a public-hash
     one. Proofs are checkable only by the organiser, online, until the key is released after the
     record is frozen. A real-world recursion built from a winner still rests on the usual
     heuristic, which nothing can remove (CGH plus the impossibility result).
4. **What none of this fixes.** Issue #6 has two halves: (a) the trivial witness-sending root passes
   the succinctness cap `T_V`; (b) the benchmark does not reward recursion over proving a subtree
   flat.
   - (b) remains a benchmark-shape problem.
   - Routing the leaf chain through the oracle as well (D4+) closes (a) by the certified caps
     (paper), not by a measurement. It does not close (b): a relabelled flat proof of a subtree fits
     every cap.
   - Node extraction is still decoding (#7), and proof sizes are still tight (#8).

**Recommendation** (§9). Do not adopt D1/D2 as stated. Keep the user's central move, the relativized
node relation, and pair it with an attested secret oracle as the O-25 contract stage (D4). Deploy it
all-oracle first, or as W5 if the user accepts the extractability heuristic. Add D4+ for #6(a).
Handle #6(b) through the benchmark shape. The decisions only the user can take are listed in §9.

---

## 2. Why O-25 exists, in one chain of reasoning

v3's node clause reads `Vb c₁ π₁ = true ∧ Vb c₂ π₂ = true`, where `Vb` is `V` run with
`blake2sOracle`. Proving a node therefore means proving `V`'s BLAKE2s calls in-circuit, so the
oracle must be a public function. A verifier that knows the public function can test whether the
oracle *is* that function, and on a match accept a magic proof. Among all oracle functions that
match has probability `2^-256`, so the ROM theorem cannot see it: this is Canetti–Goldreich–Halevi
uninstantiability, and `Controls/Backdoor.lean` certifies such a verifier. The earlier O-25 memo (F2,
submissions repository) concluded: *"the only way to make the instantiation unknowable is to make it
external, which recursion forbids."*

The user's idea removes the premise. If the node clause runs the children **under the same oracle
as the game**, nothing in the relation needs a circuit for the oracle, so the oracle may be external
and secret. The rest of this report asks what that costs.

| | v3 | relativized, pure ROM (D1, D2) | relativized, attested (D4, W5) |
|---|---|---|---|
| Node clause | children accepted under BLAKE2s | children accepted on the game's log | same |
| Oracle at deployment | public BLAKE2s | secret harness service | secret service + attestation |
| How a parent knows its children's oracle answers | recomputes BLAKE2s in-circuit | must re-ask them (§6) | hashes an attested list in-circuit |
| O-25 | open | closed (deployment) | closed (deployment) |
| Composition across levels | heuristic | theorem | theorem |
| Root verifier | succinct | linear in all inner oracle calls | succinct |

---

## 3. Reading the prompt

The prompt's ambiguities, and how this exploration resolved each, are in `docs/explore/00-prompt-review.md`.
The resolutions that shape everything below:

- The **leaf hash stays concrete BLAKE2s**. A leaf over the oracle itself (`x = O^n(w)`) is the
  impossibility paper's hard relation family, and in the pure ROM its verifier needs about `n`
  oracle queries.
- **The deployment of the oracle is the decisive question**, and the prompt leaves it out.
- **"A million hash chains"** is read as a benchmark-shape parameter, and per-proof statistics are
  compared with whole-tree makespan.
- **Compressing** means less root-verifier work than witness-sending. Proof size cannot compress,
  because the witnesses are 48 bytes per leaf.

The variants studied: **D1** (relativized knowledge soundness certified, leaves timed, oracle calls
charged, recursion never run); **D2** (the same relation, v3's whole tree, a secret oracle service, a
charge per verifier call); **D3** (signed oracle); **D4** (attested oracle); **W5** (channel split);
**D4+** (oracle-chain leaf).

**Terms.**

| Term | Meaning |
|---|---|
| query log, `runLog L` | the oracle's answers so far, as a list of (query, answer); running `V` "on the log" answers its queries from that list and fails if one is missing |
| potential `μ` | a non-negative number per log, chosen by the submitter. It starts at 0 and rises by at most `ε` on average per fresh oracle answer. Below 1, every accepted proof must be extractable. The advantage bound `(Q + qV)·ε` is Markov's inequality on it |
| extractor `E`, `Computes` | the function that opens an accepted proof to a witness from the log; `Computes` is v3's requirement that a step-bounded program on the contract's machine computes it |
| decoding extractor | one that reads the child proofs committed inside a node proof, as any bounded node circuit forces (issue #7) |
| straight-line | extraction from one run's log, without rewinding the prover |
| escape | an extractor output other than a witness: a BLAKE2s collision, or a late preimage (§7.2). Used only in this sense below |
| board T, `T_V`, `qV`, `proofCap` | v3's ranked whole-tree wall-time board; the root verifier's time cap; the certified bound on verifier queries (`≤ 2^16`); the proof-size cap (1 MiB) |
| ranked shape | `r = 8`, `n = 2^14`: 256 leaves of `2^14` chain steps, 255 nodes |
| spartan-chain | the certified honest leaf SNARK in the submissions repository (Spartan + Ligero over GF(2^64), 5,156 oracle queries per proof) |
| Flock, WHIR, leanVM | Flock (Bünz–Rothblum–Wang, ePrint 2026/1329) proves BLAKE-family compressions over binary fields; snark.fast's "Flock Challenge" times BLAKE3 proving with a fixed verifier. WHIR is a hash-based polynomial commitment. leanVM is a zkVM that uses Flock for BLAKE2s |

---

## 4. The user's design, made precise

The probes define the relativized relation by reading the children's verdicts from the query log:

```lean
-- RecursionFast/Explore/Relativized/Defs.lean
def RelL (V : Digest → Proof → OProg Bool) (L : Log) : Digest → Wit → Prop :=
  RelWith fun c π => (V c π).runLog L = some true
-- leaf: n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n          (concrete BLAKE2s, as v3)
-- node: c = nodeStmt c₁ c₂ ∧ both children accepted, their oracle answers read from L
```

`KStateRel V E ε` is v3's potential-form knowledge state with one change. Its `final` law
concludes `RelL V L c w` instead of `Rel Vb c w`. In words: on any query log whose potential is
below 1, every proof `V` accepts is opened by the extractor `E` to a witness whose children `V` also
accepts *on that same log*. Everything else is v3's: `step` bounds the average rise of the
potential per fresh query by `ε`, and the paper theorem gives advantage `≤ (Q + qV)·ε`.

**Completeness has to move inside the game** (A1 m2, W2 M10, P4).
- `RelL` depends on the log, so the contract's `CompleteWithError`, which takes the relation as a
  proposition outside the lazily sampled oracle, is ill-typed for it.
- Node completeness from an arbitrary starting log is unsatisfiable for every Fiat–Shamir design.
- W2 §A.5's *context form* repairs both: the statement and witness are produced by a program run
  against the same oracle, and completeness holds for every such program.
- No probe proves whole-tree completeness. P2 proves node completeness for its toy.

---

## 5. What relativization buys

### 5.1 Whole-tree knowledge soundness becomes a theorem (kernel)

Because a child's verdict is read from the same log, `final` applies again to the extracted
children, at the same potential. One knowledge state therefore opens the whole tree:

- `compose`: below potential 1, every accepted proof is extracted on the same log to every depth.
- `compose_flat`: when the walk ends in leaves, the extracted chain starts hash up to the root
  digest. This is a flat witness for the whole tree.
- `paper_tree`: the probability that the root is accepted while some level fails to extract is at
  most `n·ε` for a game of `n` queries. There is one bound for the whole tree and no factor for
  depth.

This is the composition theorem of Chiesa–Guan–Samocha–Yogev (CGSY24, Thm 5.1) in the
competition's counting form. v3's relation cannot give it. `v3_no_compose` exhibits, on a log of
potential 0, a node proof that v3's certified backdoor verifier accepts but whose children its
certified extractor does not open, because they are accepted under BLAKE2s rather than on the log. DESIGN-v3 §5.4's first
heuristic, composition across levels, becomes a theorem.

Hidden conditions (T1 §5): the walk needs an explicit depth bound (a BLAKE2s cycle cannot be ruled
out by counting); a `nodeStmt`/`leafStmt` collision yields *a* witness, not necessarily the honest
decomposition; and `qV` of the root must count every query the root re-asks.

### 5.2 O-25 closes, but by the deployment, not by the definition

- **The definition does not close it (kernel).** `Backdoor.backdoor` ports v3's backdoor: it is
  relativized knowledge-sound at `errorCap` with one query, and under `blake2sOracle` it accepts a
  32-byte magic proof of every statement. Relativization changes what the theorem says about
  children, not what a ROM theorem can see about one oracle function.
- **A secret oracle does close it (paper).** The harness serves `PRF_k(q)`, BLAKE2s in its keyed
  mode (not `BLAKE2s(k ‖ q)`; A1 m6, A2 m11), with a key `k` that is fresh per evaluation and held by
  a separate process. The prover reaches the oracle only by calling it.
  - The winning condition the theorem bounds ("`V` accepts and `E` fails to produce a valid
    witness") can be decided with oracle access. A standard hybrid therefore moves the ROM bound to
    deployment, losing `Adv_PRF`.
  - CGH needs the seed to be public (CGH §4).
  - The hybrid's fine print (W2 §A.6–A.7, P2):
    - the distinguisher runs the whole evaluation and the extractor within its budget
      (`2^48 + 2^16·t` steps), so `Adv_PRF` is taken at that cost;
    - the step from a lazily sampled table to a random function, and to randomised adversaries, is
      on paper, as in v3;
    - the service is assumed correct;
    - the deployed whole-tree bound is about `2^-100` at `ε = 2^-128`, because `Q` counts every query
      of the evaluation.
- **What that kills.** Every disguise in F2 §1.2/§14: the literal trigger, the `evalPoly`
  recognition, the position channel, review evasion, and the post-hoc check over BLAKE2s wires. It
  also kills the liveness mirror (a verifier that rejects honest proofs only at deployment). None of
  them can single out the deployed function.
- **What it costs (A1 M9).**
  - Until the key is released, the competition is designated-verifier: nobody but the organiser
    can check a proof. Releasing the key after the record is frozen restores offline verification;
    only proofs produced after release could exploit it, and none of those is scored.
  - Key reuse across evaluations, or publishing answers before release, reinstates CGH.
  - The service is trusted runtime code.

---

## 6. What the impossibility result costs in the pure ROM

### 6.1 The result, and why its theorems do not apply verbatim

Barbara–Chiesa–Guan (ePrint 2024/728, TCC 2025) show
`DTIME^O[t] ⊄ NARG^O[vq = o(t)]` and `NTIME^O[t] ⊄ NARG^O[as = o(t)]`. The theorems also cover
interactive and computationally sound arguments. Both are separations for specific hard relations.
The competition's relation is different (T1 Prop. 1.4): if `V` is complete for every oracle, the
*language* of the node relation does not depend on the oracle, so plain soundness is cheap.

The obstacle returns through **knowledge**, by the paper's own technique. Flip one oracle answer
that a child proof's validity depends on. A verifier that does not ask that query cannot notice the
flip, but the extracted child proof is now invalid on the log.

### 6.2 The re-ask law (kernel + paper)

- **Kernel, the deterministic core.** A node verifier that judges its children against
  prover-supplied answers, without asking the oracle, accepts on the empty log. There `final`
  demands children accepted on the empty log.
  - `lazy_no_kstate`: for the natural extractor, no knowledge state exists at any error.
  - `lazy_extractor_collides`: *every* extractor of such a state must output, on the empty log,
    either a preimage of `nodeStmt c₁ c₂` under the leaf tag, or a second node preimage whose
    children are themselves lazy nodes. When `c₁` is a leaf statement, as in the probe's instance,
    each case is a BLAKE2s collision between distinct inputs.
  - The honest alternative, `deferState`, asks every supplied answer and is sound with the
    child's potential. `queries_defer` shows it asks at most the `|Q|` queries of the carried list,
    and all of them when it accepts. For an honest list that is the children's own query count:
    deferral compresses only local work.
- **Kernel, the general deterministic core** (P4, `reask`, `flip_reask`). Take an extractor that
  returns the children committed in the node proof. Suppose a committed child reads query `q`, and
  the log *with `q` erased* still has potential below 1. Then the parent must read `q` too.
  Otherwise erasing `q` from the log, or flipping the oracle there, makes `final` fail.
- **Paper (T1 Thm 2.2).** Decoding extractors of this kind are the only ones a bounded node circuit
  admits (issue #7). For them the parent re-asks each child query that the child's validity depends
  on, failing to do so with probability at most `(Q + qV)·ε` per query.
  - *Spot-checking saves nothing* at fixed error (T1 Prop. 2.4).
  - For comparison, L1 derives from the paper's Thm 4.1 that, for the paper's own hard language, a
    verifier at error `2^-128` may skip at most a `2^-63` fraction of the queries.

### 6.3 Consequences (estimate unless marked)

| Shape | What the relativized root must do | Compared with witness-sending (WS) |
|---|---|---|
| Ranked tree, `r = 8`, `n = 2^14`, deferral recursion | re-ask `511·h_V` = 2.6–13.2 M compressions; root proof 80–850 MB | 0.6–3.2× WS's `2^22` hashes: **no compression** |
| Same, concatenation of 256 leaf SNARKs | 1.3–6.6 M oracle compressions + 256 local checks (≥ 2 s; 210 s for spartan-chain) | dominates deferral in root work, size and prover work (T1 §3.2) |
| Long tree, `r = 4`, `n = 2^20` | deferral 35–90 ms | 9–22× better than WS: "compressing, not succinct" |
| IVC, one chain step per step | ≥ 1 query per step accumulates | never compresses; with `k` steps per IVC step, at most `k/qV` |

`h_V` is the number of 64-byte BLAKE2s compressions one verification feeds the oracle:
- 25.9k for spartan-chain (from its 5,156 **measured** queries);
- 9.2k for leanVM-class verifiers;
- 5–12k for WHIR-class verifiers (C1 §2.1, estimate).

**The unit decides the verdict** (A1 M3).
- Counted in *queries*, the ranked-shape root compresses about 3× (`n = 2^14` against
  `qV_leaf = 5,156`; T1 §3: "compressing but not succinct" exactly when `n > qV_leaf`).
- Counted in *compressions*, the unit an honest in-circuit cost and an unriggable charge must use,
  it does 0.6–3.2× witness-sending's work, so it **does not compress** (C1 row 4).
- The two counts agree in direction at `chainCap`, where the compression is about 200×.

In the pure ROM, recursion compresses only the verifier's local work, and for hash-based verifiers
that is the minor share.

### 6.4 The requirement is vacuous (kernel)

- `ws_ksRel`: the witness-sending verifier satisfies relativized knowledge soundness at potential
  0, error 0, with 0 queries.
- `concatState`: a verifier whose node proof is its two child proofs in the clear inherits the leaf
  verifier's potential and error.
- `lift`, `lift_runner_ws` (P4, T1 Thm 4.1). Take *any* knowledge-sound argument `V₀` for the
  oracle-free flat statement "this digest is the runner's `treeRoot` over these chain starts", with
  the starts in the clear (32 B per leaf).
  - It lifts to a relativized knowledge-sound verifier with `V₀`'s own potential, error and query
    bound. The extractor emits witness-sending children.
  - The lifted verifier asks exactly `V₀`'s queries and never calls itself on a sub-proof.
  - With a succinct flat SNARK, its root is succinct and nothing recurses. Spartan-chain-style leaf
    SNARKs show such arguments exist; the probe instantiates `V₀` only with a non-succinct check.
  - With the library's witness-sending format the lift covers trees of up to `2^14` leaves, because
    of `proofCap` on the children. A cap-free format removes the limit.
  - **Caveat: the lift's completeness is paper, not kernel** (P4).
    - It holds only against children whose clear statement is true. An adversarially chosen child
      that `V₀` accepted with a false shape breaks perfect completeness over every oracle.
    - So under a perfect-completeness clause the lift is not an entry. Under a probabilistic,
      adaptive clause in context form (§4) it is.
    - The vacuity conclusion does not depend on it: witness-sending and concatenation are perfectly
      complete (`concatV_node_run`).

So "knowledge-sound for the relativized recursion relation" does not mean "amenable to recursion".
In D1 the clause is dead weight and only the charge acts. In D2 the charge prices exactly what v3
already pays implicitly in `T_tree`, since every inner query is hashed in-circuit once by its parent
(T1 §0).

### 6.5 The oracle charge and the statistic (A1, C1)

| Way to measure `t_hash` (cost of proving one oracle call) | How it is gamed |
|---|---|
| `T_leaf / n` from the submitter's own leaf | witness-sending leaves make it ≈ 0 |
| marginal slope of `T_leaf` in `n` | pad to a fixed size (slope 0), or sleep (slope < 0) |
| fixed organiser constant, per call | one 512 KB query instead of 5,156 small ones (≈ 260 calls) |
| fixed constant per 64-byte compression | unriggable, but then it is a certificate quantity needing no run |

- **The charge leaves local work unpriced.** Chain recomputation, the verifier's field arithmetic and
  non-native arithmetic all go uncharged, so the gradient points away from in-circuit cost (A1 M4).
  Spartan-chain's verifier alone does about `3.1·10^7` field multiplications (C1 §3.4, estimate).
- **What a hash charge captures** of a real recursion step (C1 row 10): 93–99.6% for an
  R1CS-of-bits BLAKE2s verifier, 69–75% for FRI-based ones (Plonky2, Stwo), about 10% for leanVM,
  and under 1% with a non-native verifier field.
- **Addition is the dimensionally sound form** (time + calls × time per call). Multiplication
  rescales the board by a submitter-controlled factor.
- **A million chains** take 89 days at spartan-chain speed (7.4–8.0 s per leaf at `n = 2^14`,
  **measured**), and 9.4 h even at Flock's published speed. A ±1% median needs only 14–62 samples
  (C1).
- **Per-proof statistics measure the wrong thing.** They measure one-leaf latency with all cores,
  which is 8–41% of the real work of a tree. The only meaningful statistic is whole-tree makespan
  over fresh leaves: v3's board T.
- **D1 at the leaf level is inverted.** At `n = 2^14` a witness-sending leaf check (2.0 ms,
  **measured** class) beats any SNARK leaf check. A 4–16× separation appears only at `n ≈ 2^20`.

**Verdict on D1 and D2** (A1 M10). The winner would be a BLAKE2s chain prover with any verifier,
which is snark.fast's board (the Flock Challenge, which keeps out trash by fixing the verifier). The
verifier's hash-friendliness is never exercised, and the one signal the charge sees, compressions
per verification, can be read off the certificate without running anything. D2 is also unrunnable
under v3's caps beyond `r = 2`: its root breaks `qV ≤ 2^16` by 40× and `proofCap` by 250×.

---

## 7. The workaround: authenticate oracle answers in the harness

Re-asking is forced because, in the pure ROM, the only way to learn an oracle answer is to ask. The
harness can do something the ROM cannot: **vouch for a list of answers**. This is how relativized
SNARKs exist in other oracle models. The impossibility paper's §1.2 names the signed random oracle
(SROM, Chiesa–Tromer 2010, which already proposes "a trusted Internet service"). D4 is closest to
the SROM with an online check in place of signatures (L1). By analogy it is also CCS22/CCGOS23's
"accumulation of oracle queries" with the organiser as the trusted decider, though those
constructions rely on algebra or rewinding that D4 does not need.

### 7.1 D4, the attested oracle (W2; kernel P2)

- **Service.** The service holds a PRF key `k` and a set `S`, both fresh per timed run. It answers
  three calls:
  - `query(q)` returns `PRF_k(q)`;
  - `certify(xs)` checks every item of the list `xs` and adds `hashList xs` to `S`, where an item
    is an answer `(q, a)` or an attestation `h`, and `hashList` is BLAKE2s under a new tag `0x41`
    with a prefix-free encoding;
  - `attest(h)` returns whether `h ∈ S`.
  - Certification is recursive: a list may contain earlier attested hashes, so the root verifier
    makes **one** `attest` call. The flat variant carries all 511 hashes to the root, which is
    linear in the tree again.
- **Relation.** `Rel` and `Wit` are unchanged. Only the argument changes: v3's `Rel S.Vb` becomes
  `Rel (accepted on the log)`. A succinct node proof proves in-circuit that each child is accepted
  by `V` reading a list whose hash it computes, and `V` asks `attest` for that hash. That such a
  node satisfies `final` with a decoding extractor is a paper obligation (W2 §A.4), the same one as
  issue #7.
- **Knowledge state.** v3's `step` plus a deterministic `cert` law: a valid certification never
  raises the potential. `final` lets the extractor output either a witness **or a BLAKE2s collision
  as data**.
  - The bare proposition "a collision exists" is provable by pigeonhole, so it would make `final`
    trivial.
  - The collision must therefore be the output of the step-bounded extractor program. No one can
    exhibit one.
- **Why the impossibility does not apply** (T1 §6). The paper's proof needs two things that both
  fail here: simulating the honest prover under a flipped oracle, and indistinguishability of oracles
  that differ in a few places. A list with a flipped answer cannot be certified, and one flipped
  point changes `attest` on every list containing it.
- **What it deletes from DESIGN-v3 §5.4.**
  - Composition becomes a theorem (§5.1).
  - "BLAKE2s is a random oracle" is replaced by two assumptions. One is PRF security of keyed
    BLAKE2s, which is falsifiable. The other is collision resistance of BLAKE2s in constructive
    form: the extractor must hand over the pair. (Collision resistance of one fixed function is not
    an assumption with a challenger, so the constructive form is what gives it content.)
  - O-25 and the liveness mirror close.
  - F2's typed-interface programme and the intake review of `V` become unnecessary.
- **Cost.**
  - About 50 trusted lines over the rules worktree's 288-line contract (≈ 340 of the 500-line
    budget), plus a trusted service process. It is the first runtime component whose bug would be
    accept-all (W2 M8).
  - In-circuit, hashing a child's `(q, a)` list costs 1.09× what a real recursion spends computing
    those hashes for a spartan-chain child (0.79–1.56× per query), so the winning design transfers.
  - **The defect is traffic.** The key must stay unknown to the prover: if it rode in the proof, the
    two-query recognition of F2 §6 would be certified. So every Merkle hash of every proof is a
    service call, 6.7·10^7–2.7·10^8 per tree. Measured on the dev VM:
    - a batched single stream costs 1.2× in-process hashing; unbatched, 2.3× with spinning and 82×
      with futex wake-ups;
    - the whole machine does 10–12.5 M calls/s;
    - spartan-chain loses 0.3–1.2% to this; a Flock-class prover would lose 30–110%.

**Kernel results for the attested model** (P2, `RecursionFast/Explore/Attested/`):

- **The escape.** `attState` and `calls_node`: a node verifier that makes **one** `attest` call
  and judges its children on the carried list has a knowledge state with the child's potential and
  error.
  - Its extractor returns the node witness, or the carried and certified lists as a collision.
  - Compare `lazy_no_kstate` (no call: unsound) and `queries_defer` (re-ask: `|Q|` calls).
  - `att_W1`: the instance runs at error 0 with one call per verification at every level.
  - **Scope:** the probe's node carries its children and the list in the clear. The kernel therefore
    shows the call count and the laws, not the soundness of a succinct node (above, and W2 §A.4).
- **Composition.** `compose_all`: either the whole tree is extracted from one well-formed log, or
  the walk returns a named pair of bounded lists that is a BLAKE2s collision.
  - `Paper.paper_tree`: certifications cost nothing in the error bound.
- **The collision clause is only as strong as `Computes`** (`acceptAll_choice`). An extractor
  defined by `Classical.choose` of the pigeonhole certifies accept-all at error 0.
  - In v3 that needed an open fact about BLAKE2s (`acceptAll_kstate_iff`); here it is a theorem.
  - So D4's knowledge content rests entirely on the extractor being a step-bounded program, which
    must actually *compute* a collision.
- **"Collision" has to be stated with care** (`hashList_not_coll`). Two distinct lists can share a
  `hashList` through a re-parse at 2^64-byte queries. The clause must require both lists to be
  bounded (`IsColl`).

### 7.2 W5, the channel split, with a published log (W1; kernel P3; attacks A2)

A hash-based verifier uses the oracle for two things. Of spartan-chain's 5,156 queries, about
4,700 are Merkle-path hashes, which need only *binding*, and about 400–500 are Fiat–Shamir squeezes,
which need *unpredictability*.

- **Split the channels.**
  - The secret oracle serves challenges only.
  - Merkle trees use public BLAKE2s, computed locally by the prover and by `V`.
  - The service publishes each proof session's list of challenge answers to a log the harness owns,
    and releases `k` after the record is frozen (W4).
- **Node cost.** The node circuit verifies the child's Merkle paths in-circuit exactly as a deployed
  recursion does, plus about 2% for the attested challenge list. Merkle caps, shared prefixes and
  arity choices are rewarded, which D4's flat list hides.
- **Service load** is about 2.5·10^5 calls per tree.
- **Model.** The log gains `pub (q, BLAKE2s q)` entries for the adversary's public hashing. A new
  law, `pubStep`, says a deterministic entry never raises the potential. `final` outputs a witness or
  a collision. Composition carries over.
- **The model as first written (W1) is broken in three places** (A2, paper). All three are
  fixable.
  - *Stripped log* (M1). `V` must *query* the public channel, answered from the log, rather than
    hash privately. Otherwise a log stripped of its `pub` entries still makes `V` accept with nothing
    to decode. That is P1's `lazy_no_kstate` again.
  - *Late preimages* (M2). An adversary can squeeze on a root it merely wrote down, then log the
    paths afterwards. This breaks `pubStep` for the natural Merkle potential unless the law assumes
    `pub` outputs never appear in an earlier input (an ordering hypothesis or an extractor escape).
  - *The collision clause* (M3) must be D4's constructive output.
  - Fixed, the trusted delta is +80–120 lines over the contract (A2's estimate).
  - *An honest prover may hash late* (A2 postscript). An honest prover that recomputes `leafStmt`
    or `nodeStmt` late makes the late-preimage escape valid on the honest log; column R's node mode
    is handed child digests, for example. Relation-tagged preimages must therefore be exempt from
    the ordering condition, or a liveness rule must reject escape outputs on honest proofs.
- **A modelling restriction** (A2 m6). Challenges must be bit-slices of the secret answers, because
  expanding a seed with local BLAKE2s is unprovable in `step`. Verifiers that expand seeds must be
  redesigned.
- **Assumptions.** PRF security (falsifiable) and constructive collision resistance, as in D4,
  plus an **extractability heuristic**: whoever outputs a BLAKE2s digest knows a preimage.
  - Its formal version, preimage awareness (Dodis–Ristenpart–Shrimpton), is defined relative to an
    ideal compression function. Assuming indistinguishability obfuscation,
    Bitansky–Canetti–Paneth–Rosen rule out extractable one-way functions with arbitrary auxiliary
    input in the standard model. So the heuristic is not a falsifiable assumption (A2 M4).
  - It is strictly weaker than v3's "BLAKE2s is a random oracle". It drops unpredictability, which
    is what CGH attacks.
  - D4's all-oracle form needs no such heuristic, because its service log *is* the trace.
- **Why the extractability gap does not reopen CGH** (A2 M4, paper).
  - The backdoor needs the model and the deployment to disagree about an answer `V` sees. On the
    public channel they agree by construction, and on the secret channel `V` cannot predict.
  - A competitor who controls both `V` and the prover gains nothing from the gap. A certified `V`
    accepting below potential 1 means the logged leaves decode to a witness for a *fresh*
    statement. Exploiting the gap would require breaking the SNARK's soundness under `PRF_k`.
- **Cost check** (A2 §6). The node costs 25.5k in-circuit plus 521 list compressions, against 25.9k
  for a real recursion step: +0.5%.
  - The binding service cost is *latency*, not throughput: about 476 sequential round trips per
    leaf, 1.4% (spin ring) to 52% (futex) of a 34 ms Flock-class leaf (A2 m9). The service must use
    a spinning shared-memory ring.
  - A2 found no strategy that games W5 without gaming D4 and v3 identically.
- **Session hygiene** (A2 M5). The prover must replay the final ≈ 500 queries in a fresh session and
  close that one, because grinding and retries fill raw sessions. Certification must be recursive,
  as in D4.
- **Kernel results for the corrected two-channel model** (P3, `RecursionFast/Explore/TwoChannel/`,
  a two-leaf Merkle toy with one squeeze):
  - *`pubStep` holds in the strong form, with equality.* For any potential that prices each secret
    answer against the log as it stood before that answer (`ofHist_pub`; for the toy,
    `merkleState_pubStep`). The law is not where the difficulty lies.
  - *W1's "witness or collision" clause fails* (`col_no_kstate`). For the natural extractor no
    knowledge state exists at any `ε < 1`. The adversary squeezes on a root it has not evaluated,
    then evaluates only the opened leaf's hash and the root. Any other extractor must invert
    BLAKE2s (`col_extractor_inverts`).
  - *A second escape fixes it.* With a "late preimage" escape (a digest used in an input before any
    entry produced it), the natural extractor works: `merkleState` certifies the toy at `ε = 1/2`,
    which is tight for that extractor (`merkle_eps_ge`). Honest proofs are extracted, not escaped,
    whenever neither leaf hash equals the root (`honest_extracts`). The kernel checks this condition
    for two concrete leaves (`honest_extracts_blake2s`).
  - *If `V` hashes privately,* without reading its BLAKE2s values from the log, the natural
    extractor has no knowledge state at any `ε < 1` (`pure_no_kstate`). Every other extractor must
    invert the Merkle root map from a log holding only the squeeze (`pure_extractor_inverts`).
  - *The CGH backdoor ported to the public channel cannot be certified* with its natural extractor
    (`bd_no_kstate`). Any other extractor must invert the Merkle root map (`bd_extractor_inverts`).
    The same backdoor on the secret channel *is* certified (`bdSecW_kstate`); there only the
    deployment closes it.
- **The late-preimage escape is the price, and it is idealised** (P3, paper). A non-uniform
  adversary that hard-codes one pair `(y, BLAKE2s y)` triggers the escape at no cost. Two cases:
  - such an adversary cannot use the pair to forge a commitment to data it does not know;
  - but the deployment bound gains a term that only the extractability heuristic controls.
  This is the concrete form of A2 M4.

### 7.3 D3, the signed oracle

D3 is the same idea with hash-based signatures verified in-circuit. A signature check adds 145
(leanSig XMSS) to 1,059 (WOTS+ worst case) compressions per child, 0.5–12% of the node. It also
needs a 100–200-line trusted signature specification, or 150–300 lines with the signing-oracle
model. D4/W4 dominates it unless proofs must be verifiable offline *during* the evaluation.

### 7.4 D4+, the oracle-chain leaf (W2 §D, A3)

Attestation removes the reason §3 kept the leaf concrete. Under D4+ the leaf chain is computed
through the oracle and certified as an `n`-item list. The leaf circuit then hashes that list: 1.16×
v3's chain cost with streamed 74-byte items (A3 m1). The chain digests are now PRF outputs, so no
root verifier can recompute them.

- **Closes #6(a), the trivial root, by the certified caps rather than a measurement** (A3, paper
  argument; no Lean theorem).
  - A root verifier sees at most `proofCap` bytes and `qV` answers, so it can recover at most
    ≈ `2^15 + qV` of the `2^22` chain digests. The rest must come from a SNARK.
  - `T_V` becomes a loose liveness cap. The CPU-time rule, its calibration against the best linear
    verifier, and the step-count upgrade (O-18) all become unnecessary.
- **Does not close #6(b), the recursion incentive** (A3 M1). T1's flat lift survives as "proof of
  parent":
  - one flat SNARK over a level-`j` subtree's attested lists serves as the proof of *every*
    statement in that subtree, with a path to say which one;
  - its extractor is straight-line, and it fits every cap;
  - the prover flattens to the memory limit, `j ≈ 3–4`, as in v3, and is 2.3–7.5× cheaper than full
    recursion at the ranked shape (estimate);
  - a per-level `T_V` cannot see it either: a relabelled flat proof verifies as fast as a recursive
    one.
- **Parameter conditions** (A3 M2).
  - At the stated cap `qV ≤ n`, a hybrid witness-sending node still exists at level 1. It re-queries
    one chain and carries the sibling's compact transcript in 524 KB.
  - Fix: `qV ≤ 2^13` (or `2^12` under W5), plus the shape invariant `proofCap < 64·n`. Raising
    `proofCap`, as issue #8 wishes, would reopen the hybrid.
- **Engineering** (A3 M3, M4).
  - The chain is `n` *dependent* service calls per leaf: 17 ms (spin) to 0.61 s (futex) per `2^14`
    leaf. A `chain(s, n)` service call evaluated in-process fixes this; it is modelled as `n` queries
    and charged to the prover.
  - Instances now depend on the key, so the key must be fresh per repeat and released afterwards
    (W4), so that anyone can check the tree was a tree of chains.
- **Cost.** About 6 trusted lines over D4.

### 7.5 What none of these fix

- **Issue #6(a), the succinctness cap, without D4+.** Witness-sending needs no service. Its check
  takes 37–43 ms threaded and 0.19–0.69 s on one core (**measured**/estimate). A real recursive root
  checks in 8–30 ms (estimate, on a machine with carry-less multiply), but takes 0.5 s on the dev VM
  without it.
  - At the ranked shape the raw ratio of witness-sending to real-recursion root time is 6–24×, so a
    one-core CPU-time cap leaves a margin of only about 2–2.5× on each side.
  - At `r = 4, n = 2^20` the raw ratio grows to 25–95×, and the margin per side to about 5× (C1 §2.3).
  - So without D4+ the benchmark shape matters more than the oracle model, and `T_V` must be
    calibrated on the reference machine.
- **Issue #6(b), the recursion incentive, with or without D4+.** Flattening to level `j ≈ 3–4` is
  certifiable under every design studied. Recursion costs 2.5–12.6× the work of proving the same
  compressions flat at the ranked shape, but only about 1.17× at `r = 4, n = 2^20` (C1).
  - The honest fix is the shape: fewer, longer leaves, where recursion is nearly free and memory
    forbids flattening. Otherwise say openly that flattening below `j ≈ 4` is allowed.
- **Issue #7.** Node extraction is decoding, and the extractor budget question is unchanged.
- **Issue #8.** Proof sizes are unchanged; D4 adds about 64 B per node.

---

## 8. Comparison

| | v3 | D1 priced | D2 pure-ROM tree | D3 signed | **D4 attested** | **W5 split + W4 log** |
|---|---|---|---|---|---|---|
| O-25 / CGH | open | closed only if the oracle is secret | closed | closed | closed | closed, both channels |
| Composition across levels | heuristic | n/a (no tree) | theorem | theorem | theorem | theorem |
| Root verifier | succinct | n/a | linear in all inner calls | succinct | succinct | succinct |
| Node in-circuit vs real recursion | 1.00× | nothing built | nothing built | 1.09× + 0.5–12% | 1.09× | **1.00× + 0.5–2%** |
| Recursion-friendly verifiers rewarded | yes, but flattening wins (#6b) | no | no | as D4 | yes; flattening still wins (#6b) | as D4, more faithfully |
| Trivial root (#6a) excluded | by a CPU cap only | by a cap only | — | by a cap | by a cap; **by the certified caps with D4+** (paper) | same as D4 |
| Service calls per tree | 0 | ≈ 0 | ≈ 10^8 | ≈ 10^8 | ≈ 10^8 | **≈ 2.5·10^5** |
| Assumptions beyond the counting form | BLAKE2s is a random oracle | PRF | PRF | PRF, EUF-CMA | PRF, constructive CR | PRF, constructive CR, extractability heuristic |
| Trusted lines added (estimate) | — | +10–15 | +10–15 | +150–300 (with the signing-oracle model) | ≈ +50 (+6 for D4+) | +80–120 |
| Third-party verification | yes | after key release | after key release | yes | after key release | after key release |

---

## 9. Recommendation, and the decisions only the user can take

**Recommendation.**

1. **Drop D1 and D2 as stated.** The relativized requirement, alone in the pure ROM, either
   constrains nothing (§6.4) or makes recursion impossible to rank (§6.3). The oracle charge is
   gameable (§6.5).
2. **Keep the user's central move**, the relativized node relation read from the log, and pair it
   with a secret oracle that the harness attests. As a contract stage this is W2's minimal version:
   - the log-relative `Rel`;
   - recursive `certify`/`attest`;
   - a constructive collision output under `Computes`;
   - completeness in context form;
   - deleting `Submission.Vb`, `blake2sOracle` and the §6.7 recognition rule.
3. **Deploy it all-oracle first.** The service is a separate process with a spinning, batched
   shared-memory ring, charged to the prover's cgroup. Its oracle is BLAKE2s in keyed mode, with a
   fresh key per timed run. Spartan-class provers lose 0.3–1.2% to it; Flock-class provers up to 2×
   on a naive service.
   - Add W4's published session log and key release after freeze, so that records become verifiable
     by third parties.
4. **Move to W5, the channel split, as a later contract stage** if the user accepts its
   extractability heuristic. Use the corrected model of §7.2:
   - `V` queries the public channel;
   - the knowledge clause has a collision escape and a late-preimage escape, with relation-tagged
     preimages exempt from the ordering condition;
   - challenges are slices of secret answers.
   It gives exact in-circuit costs and about 1/1000 of the service traffic.
5. **Add D4+** (the leaf chain through the oracle, `qV ≤ 2^13`, `proofCap < 64·n`, a `chain` service
   call). This closes #6(a) by the certified caps (a paper argument, not a measurement) and retires
   the CPU-time `T_V` rule.
6. **Handle #6(b) through the benchmark shape.** Use fewer, longer leaves (`r = 4, n = 2^20`), where
   recursion costs about 1.17× flat and memory forbids flattening. Otherwise state openly that
   flattening below `j ≈ 4` is allowed. No theorem studied here forces recursion below the memory
   limit.

**A staged plan.** Each stage follows the repository's implement → review/golf → fix protocol.

| Stage | Contract change | Closes |
|---|---|---|
| R1 | log-relative `Rel` (P1's `RelL`), D4's events and `KState` laws, escapes as extractor outputs, completeness in context form | composition heuristic |
| R2 | harness service (keyed-BLAKE2s oracle, recursive certify/attest), deployment theorem on paper, delete `Vb`/`blake2sOracle`/§6.7 rule | O-25, liveness mirror, "BLAKE2s is a RO" |
| R3 | D4+ leaf, `qV` and `proofCap` invariants, `chain` call | #6(a) by the certified caps |
| R4 (optional) | W5 public channel with its two escapes and the relation-tag exemption | service traffic, cost fidelity |

**Decisions for the user.**

1. Is leaving the pure ROM for a trusted harness capability acceptable? V3-5 says ROM only.
   - D4 adds PRF security of keyed BLAKE2s (falsifiable) and BLAKE2s collision resistance in
     constructive form.
   - W5 adds an unfalsifiable extractability heuristic, weaker than v3's random-oracle heuristic.
2. A designated-verifier window: proofs are checkable only by the organiser until the key is
   released after the record is frozen.
3. Is "witness, or a collision (or late preimage) computed by the extractor" acceptable as the
   knowledge clause? It is only as strong as the extractor's step bound (`acceptAll_choice`).
4. The benchmark shape, and an explicit policy on flattening below `j ≈ 4` (#6(b)).
5. Whether to replace v3's "prove `V` arithmetised with BLAKE2s" by the attested model, given that
   the competition's records then certify the attested deployment and not a public-hash deployment.
   A real-world recursion built from a winner still rests on the usual heuristic, which nothing can
   remove (CGH, plus the impossibility result).

---

## 10. Evidence index

**Lean probes** (untrusted, `RecursionFast/Explore/`, `timeout 900 lake build RecursionFastExplore`,
three standard axioms; notes `P1`–`P4`):

| Theorem | File | Shows |
|---|---|---|
| `compose`, `compose_flat`, `paper_tree` | `Relativized/Compose.lean` | whole-tree extraction from one log, one error bound |
| `V3.v3_no_compose` | `Relativized/Compose.lean` | v3's certified backdoor accepts a node proof whose children its certified extractor does not open |
| `ws_ksRel`, `concatState` | `Relativized/Concat.lean` | witness-sending and concatenation meet the requirement |
| `Backdoor.backdoor` | `Relativized/Backdoor.lean` | the O-25 backdoor is relativized-sound at `errorCap` |
| `lazy_no_kstate`, `lazy_extractor_collides` | `Relativized/Lazy.lean` | a parent that trusts supplied answers is unsound |
| `deferState`, `queries_defer` | `Relativized/Lazy.lean` | a re-asking parent is sound, but asks up to `|Q|` queries |
| `attState`, `calls_node`, `att_W1` | `Attested/Escape.lean` | with attestation, one call per node suffices (children in the clear) |
| `compose_all`, `Paper.paper_tree` | `Attested/Compose.lean`, `Attested/Paper.lean` | whole tree from one log, or a named collision; certifications are free |
| `acceptAll_choice`, `hashList_not_coll`, `encList_inj` | `Attested/Controls.lean`, `Attested/Model.lean` | the collision clause needs `Computes` and bounded lists; the list encoding is injective |
| `merkleState`, `merkleState_pubStep`, `merkle_eps_ge`, `honest_extracts`, `honest_extracts_blake2s` | `TwoChannel/Merkle.lean` | the corrected two-channel laws hold for a two-leaf Merkle verifier |
| `col_no_kstate`, `col_extractor_inverts`, `pure_no_kstate`, `pure_extractor_inverts` | `TwoChannel/Merkle.lean` | collisions alone are not enough, and private hashing fails (natural extractor; others must invert BLAKE2s) |
| `bd_no_kstate`, `bd_extractor_inverts`, `bdSecW_kstate` | `TwoChannel/Backdoor.lean` | the backdoor is uncertifiable on the public channel, certified on the secret one |
| `lift`, `lift_runner_ws`, `liftState_μ` | `Lift/Basic.lean`, `Lift/Tree.lean` | any flat argument with starts in the clear meets the requirement with its own error and queries |
| `reask`, `flip_reask` | `Lift/Deferral.lean` | a decoding extractor forces the parent to read every query a committed child reads |

Every theorem in this table (36 declarations) depends only on `propext`, `Classical.choice` and
`Quot.sound`. The audit is `docs/explore/probes/audit/audit-orchestrator.log`, produced by
`lake env lean docs/explore/probes/audit/Audit.lean`. The probe library is 21 modules, 3,008 code
lines by `scripts/loc.py` (5,196 lines in all). A cold rebuild of those modules against built
contract oleans takes 43.5 s wall on the 32-vCPU development VM
(`docs/explore/probes/audit/explore-cold-build.log`).

**Notes** (`docs/explore/notes/`):

- `L1`: literature;
- `T1`: what the impossibility rules out;
- `A1`: attacks on D1/D2;
- `C1`: the cost model and the oracle-service measurement (`docs/explore/probes/c1-cost/`);
- `W1`: workarounds and W5;
- `W2`: D4 made precise, and its attacks;
- `A2`: attacks on W5;
- `A3`: attacks on D4+;
- `P1`–`P4`: the Lean probes.

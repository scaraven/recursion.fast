# Can a certified v4 entry be insecure under recursion? Audit report

Branch `audit/recursive-ks-gap`, from `main` at 422f2f9 (v4 SROM with V4-A11). The question and the
decisions taken for the user are in `BRIEF.md`; this report supersedes `SYNTHESIS.md` and applies
both reviews (`review.md`: cryptographic, cited as "review M1", "review m3"; `review-lean.md`: Lean
fidelity, cited as "review-lean F1").

**Tags.** **kernel**: a Lean theorem, checked with only `propext`, `Classical.choice` and
`Quot.sound`. **paper**: a citation or a written argument. **measured**: a log under `logs/`
(gitignored). **estimate**: a calculation that was not re-proved.
**Notation.** `Q` is the number of oracle queries in one service lifetime, the signer's
re-evaluations included. `qV ≤ 2^16` is the verifier's query cap and `ε ≤ errorCap = 2^-120` the
certificate's error per query. `M = 96` is the number of stream steps, `E` the entry's extractor,
`L` the lifetime's query log, `B(t)` the extractor's proved step budget.

## 0. Answer

As v4 is run, no certified entry is insecure under recursion. v4 certifies knowledge soundness for
a self-referential relation, `Rel (S.acc vk)`, whose node clause is the exact acceptance predicate.
Its extractor is straight-line and reads the log. So a failed extraction at any member of any
output's extraction tree is itself a win of the one-level game. A single adversary that selects any
winning member then bounds the whole stream by `(Q+qV)·ε`, at any depth and for any number of
members. The gaps lie elsewhere. In an SROM deployment that drops v4's key discipline (T1′), the
repository's own certified backdoor fires at zero cost. In a port to public-hash Fiat–Shamir
recursion (T2), a planted circuit that computes the honest function keeps the certificate and proves
every statement. Neither is a failure of the certificate under recursion: both are deployment
conditions that no ROM certificate can see.

| Deployment | Insecure? | Ruling and evidence |
|---|---|---|
| **T1**: v4 as run (a fresh secret key per lifetime, drawn after `V` is frozen) | **No** | An extraction failure anywhere in any stream output is a win of the one-level game, so the ROM term is `(Q+qV)·ε` for the whole stream, whatever the depth and member count (**kernel**: `StreamBound.KS.exists_wins`, `stream_escape_le`, `stream_prob`, `stream_bad_prob`, `FirstEscape.escape_prob_le_first`; the walk is `CombCompose.combWalk`, its count `comb_prob`). The deployment adds `Adv^PRF + Adv^EUF-CMA + Adv^coll` (**paper**). This holds **within the efficient-extraction domain**: logs up to about `2^61` entries, `≈ 2^-59` at `2^61` queries, and `≈ 2^-90` at the deployed `≈ 2^30` (**estimate**). The `2^-55` at `2^64` queries is the ROM term alone (`stream_err_target`). Outside the domain a certified extractor may fail with probability 1 (review M1; seams-T1 F1). The reductions' running time grows with the member count, `(M²+2M)·B(t)` (review m3). "Extraction" in the deployment means the walk that runs only `E`. That this walk's failure lies inside the V-free event, a forgery or a collision is the one paper step not yet written out (review m4; review-lean F2) |
| **T1′**: a real-world SROM without the key discipline (a long-lived TEE or signing-service key, a key reused across runs, verifiers registered after anyone had oracle access) | **Yes, at zero cost** | The certified O-25 backdoor with its trigger set to an observed answer fires on every statement at every depth (review M2). **Kernel** ingredients: `Controls.Backdoor.certified`, `magic_needs_trigger`. The certificate for the observed trigger is **paper**: the same proof with a different constant. A variant on the extractor side voids the knowledge claim of an otherwise honest entry |
| **T2**: the same design ported to public-hash Fiat–Shamir recursion | **Yes, by a planted circuit** | **Kernel**: `T2Backdoor.accT2_magic`, `extract_magic`, `relT2_node_magic`, `comb_spine_magic`. **Paper**: KRS25 Thm 2 builds a functionally equivalent circuit. For an honest GKR/sumcheck entry, **no published mechanism applies**: every KRS route needs a BLAKE2s fixed point (`T2-gkr.md`). That is heuristic, and no ROM proof is possible (BCG25). Two caveats: the keyed oracle gave domain separation for free, and a port must add its own (review m8). In the binary-field class, a predictable challenge finishes the attack in one Gaussian elimination (**measured**, C3) |

## 1. Recommendation (diagnosis only)

**Stay with the rules for what they certify.** The gap the user feared, one-level security that
collapses under recursion, does not exist in v4's own deployment. It is excluded by construction:
the relation is self-referential and the extraction is exact and straight-line. What remains are
gaps of deployment and transfer:

1. **The key discipline is part of what a record certifies.** Every record, and any real-world SROM
   built on a winner, must state the conditions on `k`. It is drawn after `V`, `P` and `E` are
   frozen. It is fresh for each lifetime. It never serves a verifier chosen after any query. It is
   independent of the signing seed. It stays hidden, which on the prover's CPUs is an assumption
   that BLAKE2s runs in constant time. Design §2.3 lists most of these as conditions of the proof.
   RU-5 should list them as conditions of the claim (§4.1).
2. **A port to public-hash recursion needs its own review of the circuit.** No ROM certificate can
   see a planted circuit that computes the honest function (BCG25; KRS25 Thm 2). The review should
   check the circuit patterns of §4.3 and the domain separation of the Fiat–Shamir hash from the
   relation's tags.
3. **Incentives.** The score neither produces nor penalises a backdoor: it costs about `10^-5` of
   the score (**estimate**). It is free, and nothing detects it: no scored quantity, no certificate
   clause, no functional test and no reviewer sees it, and the repository ships a certified template
   (`Controls/Backdoor.lean`). The score selects the GF(2^128) sumcheck class (FB-9). That class has
   no margin in T2 if a challenge ever becomes predictable (review m9; C3).

## 2. Intuition

Recursion usually breaks knowledge soundness in one of three ways. v4 avoids each by a design
choice, and a fourth fact removes the depth factor from the bound.

- **Rewinding blow-up.** An extractor that rewinds the prover multiplies its cost at every level,
  so only constant depth is safe (BCCT13; CFP25 §1.3, **paper**). *v4:* `E` is straight-line. It
  reads the log once for each member, so its total cost is linear in the number of members.
- **Relaxed relations drifting with depth.** In accumulation schemes an extracted child satisfies
  only a weaker decider, and the slack compounds until a bad accumulator walks to a good one (BMNW24
  §2.1, **paper**). *v4:* the node clause of `Rel (S.acc vk)` is the same exact `acc`. A drifting
  verifier cannot certify at `2^-120`.
- **Relativization.** A node must check that a child is accepted under the oracle, so the node
  relation queries the oracle. No succinct relativized argument exists in the ROM (BCG25 Thms 4.1,
  5.1), and the KRS25 attacks exploit circuits that evaluate `H`. *v4:* children carry signed
  traces. For a fixed `vk` the relation checks signatures with public BLAKE2s, which makes it an
  ordinary NP relation (CT10's SROM trick).
- **Why depth costs nothing.** An escape at any member, anywhere in the stream, is a win of the
  one-level game. `KS` quantifies over unbounded adversaries, so an adversary that picks *some*
  winning member whenever one exists is admissible: CGSY24 Thm 5.1's first failing vertex, here
  `KS.exists_wins` (**kernel**). One selection pays `(Q+qV)·ε` once.

The stream at step `M`, its extraction tree, and the walk:

```
              c_M = nodeStmt c_{M-1} ℓ_M            ℓ_i = leafStmt (chainEnd s_i n_i) n_i
             /    \                                  c_1 = nodeStmt ℓ_0 ℓ_1
         c_{M-1}   ℓ_M         walk at each member (c, p), on the one log L:
          /   \                  E c p.π L  →  a Rel-witness: descend into the children
        ...    ℓ_{M-1}                      →  otherwise p's trace ⊄ L: a forgery (EUF-CMA or a
        /                                                               trace-digest collision)
      c_1                                                   or ⊆ L: an escape = a KS win
     /   \
   ℓ_0    ℓ_1                  members: M nodes + (M+1) leaves = 2M+1 = 193 at M = 96
```

## 3. T1 in detail

### 3.1 The chain, from the certificate to the deployment

1. **Certificate ⇒ `KS` at the deployed key.** `Certificate.secure : ∀ vk, KS (Rel (S.acc vk)) …`
   (**kernel**, a contract field). The adversary may depend on `vk` because it is quantified after
   it.
2. **The walk.** For any accepted output of step `k`, `CombCompose.combWalk` (**kernel**, a
   computable term) returns one of four outcomes, each carrying its proof: the leaf starts, an
   explicit BLAKE2s collision, an explicit capped forgery in the tree, or an escape at one of the
   `2k+1` comb paths. It handles a separate length for each leaf, and its shape matches
   `harness/rfh/bench.py` (`#guard` known answers against `rfh.digest`; review-lean §2).
   `comb_compose`, the proposition, is trivially true (§6).
3. **The depth-free bound.** `KS.exists_wins`: on the final log, the probability that some pair
   wins is at most `(Q+qV)·ε`. Hence `escape_any_le` (any escape on `L`), `stream_escape_le` (any
   member of any output's tree) and `stream_prob` (some accepted output's `combWalk` escapes), all
   `≤ (Q+qV)·ε` (**kernel**). `escape_prob_le_first` proves the same for one root and any finite path
   set. `comb_prob`, `(2M+1)·(Q+qV)·ε`, is the per-output union bound and is superseded. The bound
   does not depend on the comb: depth-freeness is a property of `KS` plus `Escape.wins` (review-lean
   F7). It also needs `E` to be one fixed function of the log for every member (review m7).
4. **A V-free event.** `stream_bad_prob` (**kernel**) bounds by `(Q+qV)·ε` the event "an accepted
   root has a comb member with no structural witness (`¬ StructOk`), and no forgery lies on a comb
   path". Deciding it runs the harness's capped `acc` on the roots, `E`, BLAKE2s, trace membership
   and `SigOk`, and never runs `V` on an extracted child. `escape_or_forgery_of_bad` turns a member
   without a structural witness into an escape or a forgery at itself or at its nearest accepted
   ancestor.
5. **Paper steps.** The E-only walk is `combWalk` with `Rel (fun _ _ => true)`. Its failure without
   an explicit collision or forgery lies inside step 4's event: mechanical, not written in Lean
   (review m4). The remaining steps are: forgery ⇒ an EUF-CMA forgery of WOTS/Merkle or a
   `traceBytes` collision (`traceBytes_inj` under `queryCap`); collision ⇒ `Adv^coll`; the PRF hybrid
   with a V-free distinguisher `D`; lazy sampling against a random function; randomised and
   concurrent provers. The last is the service: `SIGN` re-evaluates every query, so every signed
   trace is a sub-log of `L` (code: `service/src/main.rs` 170–175).

The result, for runs whose log stays within the domain (§3.3):

```
Pr_deploy[ some accepted stream output's E-only walk fails ]
    ≤ (Q+qV)·ε + Adv^PRF(D) + Adv^EUF-CMA + Adv^coll        (D and the forger B are V-free)
```

### 3.2 The seam ledger (`seams-T1.md`, condensed)

| Links | Verdict | Evidence |
|---|---|---|
| L1–L2: certificate ⇒ one member's `(Q+qV)·ε` | holds | **kernel**: `Certificate.secure`, `KS.select`, `Escape.wins`, `runLog_of_runSeq` |
| L3–L5: balanced `compose_prob` ⇒ comb ⇒ every output | holds; the comb is now **kernel** | `combWalk`, `stream_prob`; `SeamsT1.outputs_escape_le` (union over roots, superseded by `stream_escape_le`) |
| L6: the extractor reads `V`'s answers | holds at every depth | **kernel**: `Escape` needs `tr ⊆ L`; **paper**: no deployed verifier queries the oracle |
| L7, L15, L16: the service as the model's log; lifetimes; how `Q` is counted | holds | code: `main.rs` 170–175, 192; PROTOCOL §1, §2.2, §6; `bench.py` 376 (one service per stream) |
| L8–L10: forgery ⇒ EUF-CMA ∨ trace collision; `Adv^coll` | holds | **paper** (design §2.4–§2.5); **kernel**: `traceDigest_eq`, `Forgery.cap`; `2^-129` at `2^64` hashes (**estimate**) |
| L11: lazy sampling; randomised provers | holds | **paper** |
| L12: the PRF hybrid of design §2.3 | open as written; holds with the V-free event | §6 (b); **kernel**: `stream_bad_prob` |
| L13: the `Computes` domain | holds in T1; not covered at `2^64` | §3.3 |
| L14: arithmetic | holds; the union-bound margins are superseded | **kernel**: `stream_err_target`, `union_factors` |

### 3.3 The extractor domain (review M1)

`Computes` binds `E` only on tapes of at most `2^64` words. A log of `≥ 2^62` entries, or of
`≥ 2^47` maximal (`2^20`-byte) queries, is outside it (**kernel**: `SeamsT1.tape_out_of_domain`,
`max_queries_out_of_domain`). A run of `2^64` queries leaves the domain only if its log grows that
large, so the deployment claim at `2^64` is *not covered* rather than refuted (review-lean F8). It
can fail, though. Let `E_bad` be the honest `E` inside the domain, which outside it returns `none`
whenever the log is consistent with keyed BLAKE2s under some key. It keeps `KS`: in the ROM that
branch has probability `≤ 2^256·2^-256(m-1)` for `m` distinct entries, which `ε` absorbs (**paper**).
Yet it fails on every deployed log. The PRF, EUF-CMA and collision reductions run `E`, so they
cannot run above the domain either. T1 stays far inside: `Q ≈ 2^28`–`2^30` within
`stream_s = 1,920 s`, giving `(2^30+2^16)·2^-120 ≈ 2^-90` (**estimate**). At the domain's edge,
`2^61·2^-120 ≈ 2^-59`.

### 3.4 What the bound does not say

- **The reductions are not depth-free.** `D` and `B` run the E-only walk on every output:
  `M²+2M = 9,408` calls of `E`, each within `B(t)`. That is about `2^62` steps with short queries
  and up to about `2^76` with `2^20`-byte queries. Against keyed BLAKE2s the generic advantage is
  `T/2^256`, which is harmless (**estimate**, review m3).
- **What "extraction" means in the deployment** is the E-only walk, not the kernel `combWalk`.
  `combWalk` decides `Rel (S.acc vk)` through `Compose.extract`, so it runs `V` on extracted
  children (review-lean F2). It can also report an escape where the E-only walk returns starts: the
  children are well formed, `acc` rejects them, yet they open to good leaves (review m4). In `D`,
  `V` runs only in the root check, which uses the harness's capped compiled `acc`. That check implies
  the mathematical `acc` (design §2.7, trust item 5), so a timeout can only reject, the safe
  direction.
- **Knowledge is existential in the deployment.** The service keeps no table (V4-A5) and the
  harness keeps no query log (removed by V4-A9), so nobody holds `L` after a run. A record therefore
  guarantees that a witness exists and that a certified extractor would find it from a log that was
  not kept: soundness with a certified extractor, not extractability by the organiser (review m5).
- **False statements.** The harness never poses one, since every leaf is drawn from its start, and
  the canaries are mutations. The coverage comes from `escape_any_le`, which quantifies over every
  `c`: an accepted proof of a `leafStmt h n` without a chain preimage would be an escape (review m6).
- **Service residuals** (review m10). The model treats `SIGN`'s re-evaluation, query counting,
  per-lifetime keys and the forgery/collision split correctly (seams L7, L8, L15, L16). Two
  residuals remain. The ROM bound's `Q` must hold for every oracle function, which the deployment
  meets only through the time cap and the measured throughput (**estimate**). And the service runs
  on the prover's CPUs (PROTOCOL §1), so the hidden `k` is a constant-time assumption on BLAKE2s.

## 4. T1′ and T2 in detail

### 4.1 T1′: an SROM without the key discipline (review M2)

The PRF hybrid of design §2.3 needs `V`, `P` and `E` fixed before `k` is drawn, and `k` fresh for
each lifetime. v4 enforces both: a fresh service runs for each stream, and the entry is frozen at
submission. Realistic analogues often enforce neither: a TEE or signing service with a long-lived
key, several verifiers registered over time, a key shared across runs. **The attack** needs no
port:

1. Ask the live service one `QUERY` for the empty string `q0` and record `t = PRF_k(q0)`.
2. Submit the O-25 backdoor (`Controls/Backdoor.lean`) with `trigger := t`. Its certificate is the
   same proof: an answer equals any fixed digest with probability `2^-256` over random oracles
   (**paper**; review M2; not re-run in Lean).
3. Under this key, `acc` accepts the 32-byte magic proof of every statement on the signed trace
   `[(q0, t)]` (**kernel**, `magic_needs_trigger`: acceptance holds exactly on that trace). The
   service signs that trace honestly. Extraction fails (`decode_magic`). The attack covers every
   depth, because the root's magic proof is accepted directly.

The reduction cannot even be stated, since `D` would depend on its own challenge. **The extractor
side** gives a variant: honest `V` and `P`, and an `E` that returns `none` whenever the log contains
the observed pair `(q0, t)`. It is certified, since in the ROM that pair appears with probability at
most `Q·2^-256` (**paper**). Under that key it voids the knowledge claim of an otherwise honest entry.
The cost of either variant is the backdoor's, about `10^-5` of the score (**estimate**). The
countermeasure is a stated condition (§1, item 1), not a certificate clause.

### 4.2 T2: the planted backdoor under public-hash Fiat–Shamir

Model (`Explore/T2Backdoor.lean`): `Hpub q = BLAKE2s(q)` with no key and no signer.
`accT2 V c π = (V c π).run Hpub`, which is the replay a T2 node circuit runs (`runSeq_ownTrace`).
`RelT2` is `Rel` with plain child proofs. All **kernel**, standard axioms
(`logs/audit/writer-T2Backdoor.log`):

- `accT2_magic`: under every `vk`, the magic proof of **every** digest is accepted.
- `extract_magic`: the submission's own extractor, applied to the statement `c`, returns `none` on
  every log. This is a failure of the **named** extractor (review-lean F4). `S.E = decode` opens
  every honest proof, and no false leaf statement is exhibited, which would need a non-preimage of
  BLAKE2s. Finding leaf starts for arbitrary digests would invert BLAKE2s (**paper**).
- **The recursive content** is `relT2_node_magic` (a node with two magic children satisfies
  `RelT2`) and `comb_spine_magic` (so does every spine node of a comb of any length over arbitrary
  digests). `comb_collapse` and `tree_collapse` are only `accT2_magic` at the root, and no child is
  checked (review-lean F5). The attack needs no recursion at all, which makes the finding stronger.
- `node_wraps_magic`: if the v4 signature check is kept and the T2 prover holds the key, an honest
  v4 node proof with two magic children is accepted under `Hpub`.
- **The circuit version** (**paper**, KRS25 Thm 2): for any admissible circuit `C`, there is a
  functionally equivalent `C*` with `O(d_h log ℓ)` more depth and an accepting proof of any output.
  It is certifiable and passes every functional test. It is ideation C2 in GKR form.

*This round's Lean change (review-lean F3):* `extract_magic`, `comb_collapse`, `tree_collapse` and
`t1_vs_t2` used to pass `vk` as the extractor's statement argument, which was true only because
`S.E` ignores it. They now pass the statement (`S.E c …`, `S.E (combRoot d₀ ds) …`), and
`extract_magic` lost its unused `vk`. The proofs are unchanged.

### 4.3 T2: an honest GKR/sumcheck entry (`T2-gkr.md`)

**No published mechanism applies.** KRS Thms 1, 2, 9 and 10 and Fenzi26 Thm 2 all need a circuit
wire that equals an outer challenge by construction (**paper**). In a certified entry every outer
challenge binds `comm(w)` and `c`. If it did not, the adaptive `KS` game would break the entry by
one linear solve, so it could not be certified (C3). An honest node evaluates `H` only on child
transcripts and on tagged statement encodings. A wire equals a challenge only through (i)
`c₁ = nodeStmt c₁ c₂`, a BLAKE2s fixed point, and (ii) an input layer that contains its own
commitment, a second fixed point. Without them, only the chance event `2^-k` per trial remains, and
the ROM's `Q·ε` already prices it (**estimate**).

**Why this is not a proof.**

- (a) The class has no ROM proof and can have none (BCG25 §2.8). Its T2 safety is CGSY24 §2.3's
  heuristic, and KRS §5 leaves it open.
- (b) Nothing in the rules checks the premise that every in-circuit `H` input is a child prefix or a
  tagged statement encoding.
- (c) **The port must add domain separation** (review m8). `Hpub` is untagged, so
  `Hpub (tagLeaf ‖ h ‖ enc64 n) = leafStmt h n`, and the same holds for `nodeStmt` and `chainStep`.
  In T1 the keyed oracle separated the Fiat–Shamir domain from the relation's seven tagged domains
  for free.

**Circuit patterns that would void the verdict** (each reviewable, none visible to the
certificate): `H` gadgets fed from the parent's own statement or public input; recomputed Merkle
roots wired into `H` in a relation that allows `c₁ = c` (T2-4a); universal or VM circuits that run
code supplied in the witness (KRS Thms 9, 10); transcripts that are not domain-separated from
`nodeStmt`, `leafStmt` and chain inputs; sub-circuits functionally redundant with `C` (Thm 2).

**The binary-field amplifier** (C3, **measured**, `logs/audit/T2-gkr-c3.log`; seed 1, 1,000 trials
per row). Over GF(2^128), choosing `n` witness bits so that the multilinear extension at a known
challenge hits a target is 128 GF(2)-linear equations:

| `n` | solvable (measured) | exact for a random 128×n GF(2) matrix | time per instance (Python) |
|---|---|---|---|
| 128 | 0.616 | 0.6103 | 9.1 ms |
| 160 | 1.000 | `1 − 1.16·10^-10` | 18.0 ms |
| 256 | 1.000 | `1 − 2^-129` | 19.2 ms |

Any route that makes a challenge predictable therefore finishes in one elimination in this class.
Over a prime field the same step is a modular subset sum (**estimate**).

## 5. What the audit tried that did not work

One line each, with the reason and the source.

- KRS on an honest, fixed node circuit (ideation C1): two independent fixed points (T2-3).
- A partial commitment or batched roots (KRS Thm 10): the same fixed points; an unbound part is
  uncertifiable (T2-4). Recomputed roots in the child prefix (T2-4a): the attacker must guess query
  positions carrying `≥ λ` bits (**estimate**), and barrier (i) holds regardless.
- Weak Fiat–Shamir (challenges omit `comm(w)`, `c` or `y`): uncertifiable, one elimination in the
  adaptive game (T2-5c). Public-input layers holding `comm(w)`: a fixed point via the child's
  statement slot (T2-5d). Reused child challenges, two-phase commitments: case (c) or no gain
  (T2-5e). Fenzi26's generated statements: `vk` and the circuit are fixed and `c` is hashed (T2-1).
- Unbounded verifier branches in the PRF hybrid (C4): a hole in the proof, not an attack; closed by
  the V-free event (§6 b). Linear-in-`N` margins at the cap (C5): superseded by `stream_prob`.
- A node circuit that skips the child's signature or exact trace: uncertifiable, `Rel` demands
  `acc`. Committing the witness by one 1 MiB query: the bytes are in `π` and priced. Replaying a
  signed child, cross-step trace reuse, a degenerate `vk`: inside `∀ vk` and `KS.select`. Grinding
  to `δ = 2^-40`: completeness only. Signature-index exhaustion: the service refuses (`wots.rs`
  222); runtime, out of scope (all ideation C6; seams L9).
- Depth drift (BMNW24), rewinding (CFP25), relativization (BCG25): excluded by design (§2). MMZ's
  osROM: nothing v4 needs is missing. KRS25 or Fenzi26 in T1: the Fiat–Shamir function is `PRF_k`
  with `k` drawn after `V` (`literature.md` §§1, 3–5).
- The Python toy for C1: not built; the analysis decided the question (T2-7).

## 6. Corrections to the v4 design and library (not attacks)

- **(a) Design §2.4 and V4-A10's accounting: the union-bound factors are unnecessary.** `N = 193`
  (final output) and `9,408` (every output) can be dropped: `(Q+qV)·ε` covers the whole stream,
  re-timed outputs included (**kernel**: `stream_prob`, `stream_escape_le`; `union_factors`: the
  design's figures are `2^7`–`2^8` and `2^13`–`2^14` times too large).
- **(b) Design §2.3: the PRF distinguisher runs `V`.** *bad* as written runs `V` "where the walk
  runs it", on children chosen by `E`, and the contract does not bound `V`'s running time. A
  certified `V` that brute-forces `k` in a dead branch breaks the step (seams-T1 F2, **paper**). Fix:
  define *bad* by the E-only walk and the V-free event `stream_bad_prob`. The EUF-CMA and collision
  reductions need the same walk (review-lean F2). The harness's root check is the only place `V`
  still runs inside `D`, under the harness's own cap (review m11).
- **(c) `Library/Compose.compose` (on `main`) is trivially true as a proposition.** Its disjunct
  `Nonempty Collision` holds by pigeonhole; its docstring should say so and point to the term `walk`
  and the events of `compose_prob` (review-lean F1). This round fixed the same issue in the
  docstring of `Explore/CombCompose.comb_compose`.
- **(d) Stale numbers.** Design §2.4 and §6.2 compute at `M = 112` (225 and 12,768 members, `2^-82`
  and `2^-76`), while the season's `M` is 96 (193 and 9,408); §4.4's "a drawn `M ≤ 112`" makes them
  upper bounds, and (a) supersedes both. The header of `Contract/Security.lean` still says
  `513 · 2^30 · 2^-120` (the `M = 256` stream before V4-A11). `service/PROTOCOL.md` §0 still says
  "the tree run", which V4-A11 removed. The every-output union omits re-timed outputs (seams-T1
  F5), moot under (a).
- **(e) Normalisation wording** (seams-T1 F3). `Security.lean` and design §1.4 justify it by "the
  prover asked for every answer". For extracted members it comes from the walk's split on
  `tr ⊆ L`, whose other branch rests on EUF-CMA.
- **(f) Knowledge in the deployment is existential**: no log is kept (§3.4; review m5).
- **(g) The canaries do not cover false statements;** `escape_any_le` does (§3.4; review m6).
- **(h) Scope of the claim.** The domain condition (§3.3) and the key discipline (§4.1) belong in
  the stated claim (RU-5), not in a footnote of §2.3.

## 7. Evidence index

Lean theorems cited. "Faithful" and the caveats are review-lean's verdicts (§3 of that file).
Files are under `RecursionFast/`. All use only the standard axioms (re-printed this round:
`logs/audit/writer-*.log`).

| File | Name | Meaning | Verdict |
|---|---|---|---|
| `Contract/Certificate.lean` | `Certificate.secure` | a certificate gives `KS` for `Rel (S.acc vk)` at every `vk` | contract field |
| `Library/KS.lean` | `KS.select` | a selector applied to a bounded adversary's output pays `(Q+qV)·ε` | faithful (review-lean §2) |
| `Library/Compose.lean` | `Escape.wins` | an escape with `tr ⊆ L` is a win of the `KS` game | used by every bound |
| `Library/Compose.lean` | `compose_prob`, `escape_prob_le` | the balanced-tree walk's bound; the union over a path set | reused (L3) |
| `Library/Compose.lean` | `compose` | the balanced walk's proposition: **trivially true** | F1 (docstring fix, §6 c) |
| `Library/Trace.lean` | `runLog_of_runSeq` | a verifier replaying a sub-log asks nothing fresh | used (L2) |
| `Controls/Backdoor.lean` | `certified`, `backdoor` | the O-25 backdoor is certified at `errorCap` under every key | faithful |
| `Controls/Backdoor.lean` | `magic_needs_trigger`, `decode_magic` | `acc` accepts the magic proof exactly on the trigger trace; it decodes to nothing | used in T1′, T2 |
| `Explore/CombCompose.lean` | `combWalk` | the computable walk over the stream's comb, with typed outcomes | faithful; runs `V` (F2) |
| `Explore/CombCompose.lean` | `comb_compose` | the proposition: **trivially true**, now documented | F1 (fixed this round) |
| `Explore/CombCompose.lean` | `comb_prob`, `card_combPaths` | `(2M+1)·(Q+qV)·ε` for one output; 193 paths at `M = 96` | faithful with caveat (F2) |
| `Explore/FirstEscape.lean` | `escape_prob_le_first` | an escape on any finite path set costs `(Q+qV)·ε` | faithful |
| `Explore/StreamBound.lean` | `KS.exists_wins` | some winning pair on the final log costs `(Q+qV)·ε` | faithful |
| `Explore/StreamBound.lean` | `escape_any_le`, `stream_escape_le` | any escape on `L`; any member of any output's tree | faithful |
| `Explore/StreamBound.lean` | `stream_prob` | some accepted stream output's walk escapes: `≤ (Q+qV)·ε` | faithful; comb-independent (F7) |
| `Explore/StreamBound.lean` | `StructOk`, `escape_or_forgery_of_bad`, `combPaths_suffix` | the decidable structural check and its reduction to an escape or a forgery | faithful, with controls |
| `Explore/StreamBound.lean` | `stream_bad_prob` | the V-free bad event: `≤ (Q+qV)·ε` | faithful (the walk to it is paper) |
| `Explore/StreamBound.lean` | `stream_err_target`, `union_factors` | `(Q+qV)·ε ≤ 2^-55` at `2^64` (true value `≈ 2^-56`); the design's factors | faithful |
| `Explore/SeamsT1.lean` | `outputs_escape_le` | the union over many roots and path families | faithful (superseded) |
| `Explore/SeamsT1.lean` | `tape_out_of_domain`, `max_queries_out_of_domain` | `≥ 2^62` entries or `≥ 2^47` maximal queries exceed `Computes` | faithful (wording F8) |
| `Explore/SeamsT1.lean` | `final_output_err`, `every_output_err`, … | the union-bound figures at the target | checked; superseded |
| `Explore/T2Backdoor.lean` | `accT2_magic` | in T2 the magic proof of every digest is accepted | faithful |
| `Explore/T2Backdoor.lean` | `extract_magic` | the named extractor fails, at the statement | F3 fixed this round; F4 documented |
| `Explore/T2Backdoor.lean` | `relT2_node_magic`, `comb_spine_magic` | the recursive content: magic children satisfy `RelT2` at every spine node | faithful |
| `Explore/T2Backdoor.lean` | `comb_collapse`, `tree_collapse` | `accT2_magic` and `extract_magic` at a root | F3 fixed; F5 documented |
| `Explore/T2Backdoor.lean` | `node_wraps_magic`, `t1_vs_t2`, `runSeq_ownTrace` | an honest v4 node wraps fake children; the contrast with T1; `accT2` is the node's replay | faithful (F6) |

| Document | Content |
|---|---|
| `BRIEF.md`, `SYNTHESIS.md` | the question, decisions and chain to audit; the reviewed draft (superseded) |
| `literature.md` | MMZ, CGSY24, BCG25, KRS25, Fenzi26, CFP25 and BMNW24, read against v4 |
| `seams-T1.md`, `ideation.md` | the ledger L1–L16 and findings F1–F7; candidates C1–C6 |
| `comb.md`, `stream-bound.md` | the comb walk; the depth-free bound and the V-free event |
| `T2-backdoor.md`, `T2-gkr.md` | the planted backdoor under T2; the exposure of honest GKR, and C3 |
| `review.md`, `review-lean.md` | the cryptographic review (2 major, 9 minor); the Lean review (1 major, 7 minor) |

## 8. Method and budget

**Phases.** (1) Round 1 (commit cced3e0), four parallel agents: literature with the `FirstEscape`
probe, the T1 seam ledger with `SeamsT1`, attack ideation, the comb walk with `CombCompose`.
(2) Round 2 (fba00f9): the depth-free bound and V-free event (`StreamBound`), the T2 backdoor
(`T2Backdoor`). (3) Honest GKR under T2 with the C3 script, and the draft synthesis (ca80e06).
(4) Two parallel reviews, cryptographic and Lean fidelity. (5) This report, with the Lean clean-ups
for review-lean F1 and F3–F5. **Subagent runs: 10 of the 12 allowed** (2 of them Fable: ideation
and the cryptographic review; at most 4 in parallel).

**Lean.** Every check went through a capped runner (`leanrun.sh`: `systemd-run` with
`MemoryMax=8G`, no swap, three `flock` slots, a default timeout of 1,200 s), running
`lake env lean` on one file, never `lake build`. Wall times (**measured**; peak memory 2.0–2.3 GB):

| File | Checks | Wall time | Logs (`logs/audit/`) |
|---|---|---|---|
| `CombCompose.lean` | round 1 / review / olean re-compiled this round | 5.2 / 5.0 / 5.5 s | `comb-2`, `review-lean-CombCompose`, `writer-CombCompose` |
| `StreamBound.lean` | round 2 / re-checked against the new olean | 4.6 / 4.7 s | `stream-5`, `writer-StreamBound` |
| `T2Backdoor.lean` | round 2 / review / after the F3 change | 7.0 / 6.7 / 7.1 s | `T2Backdoor`, `review-lean-T2Backdoor`, `writer-T2Backdoor` |
| `SeamsT1.lean` | review | 9.6 s | `review-lean-SeamsT1` |

**Incident to disclose.** The orchestrator's first `lake build` went through the CLAUDE.md symlink
`.lake/packages → /home/devops/CambridgePQ/recursion.fast/contract/.lake/packages`. That shared
package tree is meant to be read-only, and its build directories were partly empty. The build wrote
635 Mathlib oleans and 4 Aesop oleans into it (`logs/build-main.log`: 5 min 48.8 s wall, 83 min
user). The writes were additive and at the same pinned version, and they were left in place.
Future builds should use a private copy of the package tree, not the symlink.

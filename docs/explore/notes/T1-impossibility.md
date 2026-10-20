# T1. What the relativized-SNARG impossibility rules out for the competition's recursion relation

Theorist's note, exploration `explore/relativized-nark`, 2026-10-20. Sources: `docs/explore/BRIEF.md`;
Barbara–Chiesa–Guan, "Relativized Succinct Arguments in the ROM Do Not Exist", ePrint 2024/728
(2025-09-23), cited as [BCG] with its section numbers (`SP/paper/paper.txt`);
`RecursionFast/Contract/{Oracle,Relation,Security}.lean` at `05fde28`; DESIGN-v3 §4–§5 (rules
worktree); issues #6, #7; `V3-S2b-RESULT.md` (spartan-chain). Evidence tags: **kernel**, **paper**,
**measured**, **estimate**. Every numbered result is marked proved / sketched / conjectured.
Sibling notes (P1, W2, …) are cited by name where I checked them; I did not read them in full.

## Summary

1. **The brief's premise is wrong where it matters.** Knowledge soundness for the relativized node
   relation does not "ensure the verifier is amenable to recursion". `KS` for `RelL` (Def. 1.3) is
   satisfied, with the *same* `ε` and `qV`, by any knowledge-sound argument for the oracle-free flat
   relation "`c` is the tree over these chain starts" whose proofs carry the starts in the clear
   (Theorem 4.1, the lift; sketched, kernel-checkable in abstract form). Chain starts are 32 bytes a
   leaf, so carrying them is free. That argument never recurses, its extractor emits witness-sending
   children, and its root verifier is as succinct as the flat SNARK's. The relativized requirement
   therefore neither forces nor rewards recursion: under D1 it is dead weight and only the oracle
   charge acts; under D2 it prices recursion at exactly what v3 already pays implicitly (§0).
2. **For recursive designs it forces full deferral.** If the extractor returns the child proofs
   committed in the node proof (a *decoding* extractor, the only kind a bounded node circuit admits,
   issue #7), then the parent verifier re-asks every answer-sensitive query of each child's
   verification, except with probability `(Q + qV)·ε` per query (Theorem 2.2, sketched; its
   deterministic core is kernel-checkable). A depth-`d` root verifier asks at least the union of all
   inner verifiers' live queries (≥ 1.3·10^6 at `r = 8` with spartan-chain leaves) and its proof carries
   their inputs (≈ 0.7 GB, estimate). The proof is [BCG] §4.3's flip aimed at *child-proof validity*
   instead of membership; [BCG]'s theorems themselves do not apply, because `RelO`'s language is
   oracle-free (Prop. 1.4) and its witnesses are short.
3. Spot-checking robust children saves nothing at a fixed error target (Prop. 2.4, sketched). The only
   real escapes are oracle-free child proofs (item 1) and leaving the oracle model (§6).
4. Consequences (§3): relativized 1→1 IVC over hash chains has verifier queries ≥ the number of steps,
   and verification-work compression at most `k / qV_step`. 2→1 deferral recursion is dominated by
   concatenating leaf SNARKs in root oracle work, proof size and prover work; it beats witness-sending's
   native root work iff `n > qV_leaf` (≈ 3× at `n = 2^14`, ≈ 200× at `chainCap`; estimate). "Compressing
   but not succinct" is exactly `n > qV`.
5. Composition (§5): the orchestrator's claim is right. With `RelL`, `final` re-applies to the
   extracted children on the same log, so one `KState` extracts the whole tree with the single bound
   `(Q + qV_root)·ε`. Hidden conditions: an explicit unfolding depth (BLAKE2s cycles cannot be excluded
   by counting), `nodeStmt`/`leafStmt` collisions (some witness is extracted, not necessarily the honest
   decomposition), and `qV_root` already counts the deferred queries. `Rel Vb` cannot compose because
   `Vb c₁ π₁ = true` says nothing about `runLog L`.
6. D4 and D3 (§6): the impossibility technique breaks at "simulate the honest prover under the flipped
   oracle": a flipped list cannot be certified or signed, and one flipped point moves `attest` at
   exponentially many inputs, so [BCG] §2.3's small-distance indistinguishability fails, as in the SROM
   where relativized SNARKs exist. D4 is sound given the counting-form KS of the SNARKs, collision
   resistance of concrete BLAKE2s for the list hash, and an honest service with a secret key; its
   knowledge statement *is* `RelL` with the service guaranteeing log coverage. Flaws: `attest` is not a
   uniform query (the `step` law does not model it), the root check is online and stateful, and the CR
   assumption is standard-model. D4's gain over D2 is proof size and root time, not prover work.
7. O-25: the relation does not close it (the backdoor is still certified for `RelL`); the *deployment*
   with a secret oracle does, and then the ROM theorem is the deployment theorem modulo PRF security.
8. Lean (§7): keep P1's `RelL`/`compose`/`paper_tree` and the backdoor; restate the vacuity target as
   the abstract lift theorem; the "trusting verifier has no `KState`" target is unprovable as stated
   (it needs an injective statement encoding or per-digest hypotheses); add the deterministic deferral
   core (log coverage + locality of `runLog`).

## 0. Where the brief is wrong or imprecise

- **"force it to be knowledge sound in NP^H … to ensure the verifier is amenable to recursion."** Not
  achieved by the definition. The lift (Theorem 4.1) is a `V` with `KS` for `RelL` that does no
  recursion; a succinct instance exists as soon as any ROM SNARK for the flat chain relation exists
  (it does: Micali/BCS, and spartan-chain is a certified leaf instance). So D1's relativized clause is
  satisfiable at zero cost by any leaf SNARK plus a 32-byte-per-leaf header, and the only operative
  part of D1 is the charge `c_RO · t_hash`, which v3 could adopt with no relativization.
- **D2's charge prices what v3 already prices.** Under deferral the root re-asks every inner query
  (Theorem 2.2), so the charge is `(Σ inner queries) · t_hash`. In v3's public-hash recursion every
  inner query is hashed in-circuit exactly once, by its parent, at about the same `t_hash`. The two
  score the same work; D2 merely charges it instead of running it (§3.2, estimate). D2's real
  differences are elsewhere: a root proof of concatenation size, an online root check of ≥ 1.3·10^6
  service calls, O-25 closed, and composition provable.
- **"its verifier would need Ω(n) oracle queries and no argument could compress it"** (leaf over the
  oracle, brief §3). Right for verifier queries ([BCG] Theorem 1's technique, §4.4 below); wrong if
  "compress" means proof size: the witness is 32 bytes, and [BCG] Theorem 2 lower-bounds proof size
  by the *witness length* `t`, which is tiny here. All proof-size lower bounds in this note come from
  query inputs the root must know (Cor. 2.3), never from witness length.
- **"if the node relation is relativized, nobody arithmetises the oracle, so the oracle can be external
  and secret."** True, but only because the design has given up in-circuit oracle evaluation, and the
  price is deferral (D2) or a harness capability (D4). The sentence reads as if the price were zero.
- **"Composition across the whole tree provable from one log"** (D4 claims). Right, and it is a
  property of `RelL`, not of attestation (§5): D2 has it too.

## 1. Definitions: the paper's and the competition's, and where knowledge bites

### 1.1 The paper's objects

A relativized NARG (P, V) for a relativized relation `R^O` ([BCG] §3.4): completeness Def. 3.12 is over
a random `f ← O_λ` (adversary chooses `(x, w) ∈ R^f`, honest `π ← P^f(x, w)`, `V^f` rejects with
probability ≤ α); soundness Def. 3.13 is adaptive: a `q`-query `t`-time adversary outputs `(x, π)`,
and `Pr[x ∉ L(R^f) ∧ V^f(x, π) = 1] ≤ β`. There is no extractor anywhere; the results are about
soundness. The hard objects:

- `L*` (Def. 4.3, DTIME): `(x, y) ∈ L*_f` iff `y = F_{f,n}(x)`, each bit of `y` the parity of the first
  bits of `t/(n/2)` oracle answers at `x ‖ u_j`; `t` queries decide membership and flipping any one of
  them flips membership. Theorem 4.1 / Cor. 4.2: no argument with `vq = o(t)`.
- `R*` (Def. 5.3, NTIME): `x = 0^n`, `w ∈ {0,1}^t`, `∀ i ≤ t, f(w ‖ u_i)_1 = 0`. Theorem 5.1 / Cor. 5.2:
  no argument with `as = o(t)` even at `vq = poly(t)`; Lemma 6.3: none with `vq = o(t)` either.

The technique (Lemma 4.5, §4.3): pick a random query `q(i, j)` among the `t` that decide the fixed
instance; by averaging, `V` asks it with probability < `p` on all but `vq/p` of them (Eq. 7); the
adversary `P̃` runs the honest prover answering `q` by its flipped value, so `(x, y, π̃)` is an honest
proof under `Flip(f, q)` while `(x, y) ∉ L_{Flip(f,q)}` (equality [1]); `V` cannot see the flip unless
it asks `q` (Eq. 8); the bijection `f ↔ Flip(f, q)` keeps the oracle uniform; conclusion
`(1 − α)(1 − vq/(p t))(1 − p) ≤ β`. §5.3 handles the one-to-`2^t` correspondence of `SetZero` by a
counting over the unique-witness set; §2.7 notes the adversary preserves the honest prover's query
and time complexity, so computational soundness is also ruled out.

### 1.2 The competition's objects

`OProg` (`Oracle.lean:16`): a deterministic query program; `run H` against a function, `runLog L`
against a table (`none` on an unlogged query). `KState R V E ε` (`Security.lean:86`): a potential
`μ : Log → ℝ≥0` with `empty`, `step` (fresh query raises `μ` by ≤ `ε` on average over the `2^256`
answers, within `logCap = 2^96`) and `final` (`μ L < 1 → (V c π).runLog L = some true → ∃ w, E c π L =
some w ∧ R c w`). Paper theorem (`Library/PaperTheorem.lean`, `paper`, **kernel** for lazy sampling):
an adversary with `Q` queries makes `V` accept an unextractable proof with probability ≤ `(Q + qV)·ε`.
The statement `c` is adaptive (quantified in `final`), the extractor is straight-line (input `(c, π, L)`),
`V` has no private randomness, and completeness is perfect over every function (`Complete`,
`Security.lean:110`; `CompleteWithError δ` in the rules worktree). Perfect completeness only strengthens
the lower bounds below: the flipped world is a valid world, with no `α` loss.

### 1.3 Three node relations (leaf clause identical and oracle-free in all three)

```
Rel  Vb  c (node c₁ c₂ π₁ π₂) := c = nodeStmt c₁ c₂ ∧ Vb c₁ π₁ = true ∧ Vb c₂ π₂ = true   -- v3; Vb = V run on blake2sOracle
RelO V O c (node …)           := c = nodeStmt c₁ c₂ ∧ (V c₁ π₁).run O = true ∧ (V c₂ π₂).run O = true   -- the brief
RelL V L c (node …)           := c = nodeStmt c₁ c₂ ∧ (V c₁ π₁).runLog L = some true ∧ (V c₂ π₂).runLog L = some true
```

`KS_L (V, E, ε)` := a `KState` whose relation takes the log: `final : μ L < 1 → (V c π).runLog L =
some true → ∃ w, E c π L = some w ∧ RelL V L c w` (P1's `KStateRel`). `RelL V L c w → RelO V O c w`
whenever `L` is a sub-table of `O` (a `runLog`/`run` agreement lemma, kernel-cheap), so `RelL` is the
stronger, log-local statement; it is the form that composes (§5). Note that the relation now mentions
`V`: `KS_L` is a fixed-point property of `V`, which is intended.

### 1.4 The language of `RelO` is oracle-free (proved, lattice argument)

Let `Leaf := {leafStmt (chainEnd s n) n : n ≤ chainCap}`, `F(X) := Leaf ∪ nodeStmt(X × X)`,
`T := lfp F` (the honest tree digests), `A^O := {c : ∃ π, (V c π).run O = true}`. Then
`L(RelO^O) = F(A^O)`. If `V` is complete under every `O` then `A^O ⊇ L(RelO^O) = F(A^O) ⊇ T`. If `V` is
also sound (`A^O ⊆ L(RelO^O)`) then `A^O` is a fixed point of `F`, hence `A^O ⊇ T`, with equality
unless `A^O` contains a digest outside `T`, which requires an infinite descending `nodeStmt` chain:
a cycle of concrete BLAKE2s. Cycles exist in abundance (about `2^256` pairs `(c, c₂)` with
`c = BLAKE2s(N ‖ c ‖ c₂)` for a random function) but no counting argument sees them and none is
findable; outside that caveat the language is `T` for every `O`.

Consequence: *soundness* for `RelO` is soundness for the oracle-free NP language `T`, which any ROM
SNARG for `T` provides ([Mic00], BCS). [BCG]'s theorems say nothing: `L*` and `R*` are hard because
one flipped answer flips membership, and no flipped answer changes `T`.

### 1.5 Where knowledge bites, exactly

Soundness needs only `c ∈ T`. Two further clauses of the competition's definition are where anything
can bite. (a) **Completeness for `RelO`** hands the node prover `(c₁, π₁, c₂, π₂)`, not the starts; if
accepted child proofs are *too short to reveal the starts* the node prover must genuinely combine
proofs. But starts are 32 B a leaf, so no sensible format is too short: nothing in the relation stops
a proof from carrying the flat witness, and then both prover and extractor may switch to the flat
relation (Theorem 4.1). (b) **`final` for `RelL`** demands child proofs that verify *on the log*. For a
design whose extractor returns the committed child proofs this forces the log to cover the children's
verification paths, which forces deferral (§2). So the bite is conditional on the design being
recursive, and the relation does nothing to make it so. The structural fact behind both: this
relation's witnesses are short and its verification is expensive, so the relevant [BCG] statement is
the verifier-query one (Theorem 1 / Lemma 6.3), and that needs a language that depends on the oracle,
which `T` does not.

## 2. The lower bound for `RelL`: recursive designs must defer everything

### 2.0 Setting and the decoding hypothesis

Fix a submitted `V` (one program for leaves and nodes, as in the contract), honest `P`, extractor
`E`, and `KS_L (V, E, ε)` with `V` asking ≤ `qV` queries. Perfect `Complete` for `RelO` (the contract's
form, for every oracle function). A node proof format has a parser `children : Proof → List (Digest ×
Proof)` (the child proofs the node proof commits to). **`E` is decoding** if, whenever
`E c π L = some (node c₁ c₂ π₁ π₂)`, both `(cᵢ, πᵢ) ∈ children π`. Every recursive design is decoding:
a node circuit of bounded size takes `(π₁, π₂, claimed answers)` as its witness, and the only child
proofs a straight-line extractor can recover from the log are those (issue #7 §2; P1's `dE` is the
instance). The non-decoding alternative is §2.4 (a).

### 2.1 Lemma (log coverage; proved, kernel-cheap)

If `(V c₁ π₁).runLog L = some true` then every query on that run is a key of `L`, and the run's path
is determined by `L`'s first answers. (Induction on `OProg`; P1's `Agrees`/`runLog_of_agrees` is the
monotone half.) Hence under `KS_L`, on every log `L` with `μ L < 1` on which the root accepts, the
extracted children's whole verification paths lie in `L = (adversary's queries) ++ (root verifier's
queries)`.

### 2.2 Theorem (deferral; sketched)

Let `(c₁, w₁) ∈ Rel`, `(c₂, π₂)` any accepted child, `c = nodeStmt c₁ c₂`, and `j ≥ 1`. Define the
adversary `A_j` against a random oracle `O`:

1. `π₁ ← P^O(c₁, w₁)`; run `V^O c₁ π₁` and let `q` be its `j`-th query (abort if there are fewer). All
   these queries, `q` included with its true answer `O(q)`, are now in the log.
2. Draw `a'` uniform; let `O' := O[q ↦ a']`. Re-run `π₁' ← P^{O'}(c₁, w₁)`, answering `q` by `a'`
   privately and everything else through `O`.
3. `π ← P^{O'}(c, node c₁ c₂ π₁' π₂)`, the same way. Output `(c, π)`.

`A_j` makes `Q ≤ 2·pq_leaf + pq_node + qV` queries. Let `L` be the final log (including the root
verifier's queries, as in `paper`). Let `Sens_j` be the event `(V c₁ π₁').runLog L ≠ some true`: the
flipped child proof does not verify against the *true* answer at `q` ("`q` is answer-sensitive").
Then

    Pr[ V^O(c, π) asks q ]  ≥  Pr[Sens_j] − (Q + qV)·ε .

Proof. (a) `(c, node c₁ c₂ π₁' π₂) ∈ RelO^{O'}` and `π` is honest under `O'`, so `V^{O'}(c, π) = true`
by `Complete` (a deterministic fact for every `O, a'`, no `α`). (b) `V` on `(c, π)` runs identically
under `O` and `O'` until it asks `q`; so on the event "does not ask `q`" it accepts under `O`, and
every answer it read is in `L` with `O`'s value, hence `(V c π).runLog L = some true`. (c) By
`KStateRel.paper` (P1, **kernel** for lazy sampling) applied to `A_j`'s query program followed by the
verifier's, `Pr[(V c π).runLog L = some true ∧ ¬∃ w, E c π L = some w ∧ RelL V L c w] ≤ (Q + qV)·ε`.
(d) `E` decoding and `children π = [(c₁, π₁'), (c₂, π₂)]` force the extracted witness's first child to
be `(c₁, π₁')` up to a `nodeStmt` collision (the extracted `(c₁', c₂')` must satisfy `nodeStmt c₁' c₂' =
c`; assume `(c₁', c₂') = (c₁, c₂)`, see §5.2), so `RelL` demands `(V c₁ π₁').runLog L = some true`,
which fails on `Sens_j`. Hence `Pr[¬asks q ∧ Sens_j] ≤ (Q + qV)·ε`. ∎

Status: (a), (b), (d) are deterministic and kernel-cheap given P1's definitions; (c) is `paper`; the
only sketched step is phrasing `A_j` as one `OProg` game (two honest-prover runs with a private
table), which is routine.

**Why `Sens_j` is essentially 1.** For a Fiat–Shamir/Merkle verifier, `q` is a challenge derivation
or a Merkle node of the child's transcript. `π₁'` was built for the answer `a'`; with the true answer
the path either asks an unlogged query (`none`) or fails a comparison (`some false`), unless the bits
of `O(q)` the verifier uses coincide with `a'`'s: at most `2^-b` for a `b`-bit use. A query whose
answer never affects acceptance of honest proofs can be deleted from `V` without changing its decisions
on honest proofs, so the bound counts *live* queries; for real verifiers every query is live.

### 2.3 Corollary (whole tree; sketched)

Apply 2.2 at each inner node to each live query of each child's verification and union-bound. With
probability ≥ `1 − Σ_{i,j} (Q + qV)·ε` over the honest experiment, the root verifier's query set
contains the child verifiers' query sets; by induction on depth (the child's query set contains the
grandchildren's, by the same theorem at the child), it contains the union over all `2^d` leaves and
`2^d − 1` inner nodes of their live queries. Leaf query sets are disjoint w.h.p. (they derive from
distinct commitments), so

    qV_root  ≥  2^d · qV_leaf^live  +  Σ_{inner nodes} qV_node^live   (up to the error terms).

At `r = 8` with spartan-chain leaves (`qV = 5 156` **measured**): ≥ 1.32·10^6, plus the 255 nodes'
own, which no certified node verifier exists to measure (≈ 5·10^3 each if Flock-class, so ≈ 2.6·10^6
in all; **estimate**). **Proof size.** The root verifier is deterministic in `(c, π)` and the answers
it has read; a child's Merkle-authentication queries are `(sibling ‖ sibling)` pairs whose values are
oracle outputs on the *child prover's* hashing queries, which the root can reproduce only by asking
those (more queries still) or by reading them from `π`. So `|π_root| ≳ Σ` (sibling digests over all
inner proofs), the Merkle bulk of every inner proof: ≈ 511 × 1.4 MB ≈ 0.7 GB at `r = 8` (**estimate**;
`proofCap` is 1 MiB). This is the brief's "the root proof must contain those queries' inputs", made
precise: the inputs are the siblings, and the siblings are incompressible given only the root's view.

### 2.4 Escape hatches, precisely

(a) **Non-decoding extractors.** `E` returns a child proof the adversary never wrote. By 2.1 its
verification path must lie in `L`; the adversary controls `L` outside the root's queries, so the
only child proofs `E` can *construct* are those whose verification asks nothing the root did not ask,
in particular oracle-free ones. An oracle-free accepting proof of `c₁` exists iff `V` accepts a
witness-sending format for `c₁`, and `E` can build one iff the subtree's starts are computable from
`(π, L)`. Completeness for `RelO` then needs the honest node prover to know the same starts. So this
escape is exactly "the node proof carries the flat witness and the node argument is an argument for
the flat relation": Theorem 4.1. It is not recursion, and it is the only escape inside the ROM.

(b) **Spot-checking robust children (Prop. 2.4, sketched).** Let the child verifier be `k`-fold
parallel repetition of a piece with error `1/2` (or any verifier splittable into independent pieces),
let the parent re-ask a fraction `ρ` of the pieces' queries, and let `E` return the `ρk`-piece
sub-proof (so `V` must accept sub-proofs). The extracted child then has error `2^-ρk`. To leave `λ`
bits at the root of a depth-`d` tree the leaves need `k_d = λ/ρ^d` pieces, and the root asks
`(2ρ)^d · k_d = 2^d λ`: identical to full deferral. Non-splittable verifiers (a sumcheck's rounds, one
Fiat–Shamir chain) cannot be spot-checked at all: every query is live. Hence spot-checking shifts
constants between levels and saves nothing at a fixed target error.

(c) **Others.** Shared queries across children (one challenge for both) require the children to be
produced jointly, i.e. a batched or flat argument, whereas `RelO` hands the node prover finished,
independently produced child proofs. Grinding and proof-of-work leave live queries live. Child
formats whose validity is oracle-independent are (a). Changing the oracle model is §6. Nothing else:
2.2 is per query and uses only `Complete` and `final`.

### 2.5 Relation to [BCG]

Lemma 4.5 flips one of the `t` answers that decide a *fixed instance's membership*, needs averaging
over the `t` positions (Eq. 7) because the verifier's query set is unknown, and reproduces the honest
proof under the flipped oracle. Here membership never flips (Prop. 1.4); what flips is the validity of
the child proof the extractor is obliged to return, the honest-prover simulation is the same trick,
and no averaging is needed because the adversary learns the child's `j`-th query in step 1 and attacks
each position separately. `Complete + final` replace `α, β`; `Σ_j Pr[Sens_j]` replaces `t`. [BCG]'s
proof-size theorem (Theorem 5.1, via `2^{O(as)} · vq` distinct queries over all proofs, §5.3 Eq. 9) has
no analogue: the witness of `T` is `32·2^d + 8` bytes. Proof-size bounds here come only from query
inputs (2.3). [BCG] §1.2's remark that a ROM SNARG "becomes a relativized NARK by sacrificing
succinctness" is exactly the deferral verifier (`deferState` in P1).

## 3. Consequences

### 3.1 1→1 recursion (IVC) over hash chains

Step `i` proves "step `i−1`'s proof is accepted by `V` and `k` more chain steps were taken" (chain
steps are concrete BLAKE2s in-circuit, not oracle queries). By 2.2, the step-`i` verifier re-asks all
live queries of the step-`(i−1)` verifier and adds its own; any sound Fiat–Shamir step adds ≥ 1 query
not among the earlier ones (its challenge must depend on its own commitment). So `qV_i ≥ i`, and the
step-`i` proof must carry the inputs of ≥ `i` distinct queries: **relativized IVC in the pure ROM is
never compressing in verifier queries or proof size** when each step makes ≥ 1 live query (sketched,
from 2.2). Against the trivial verifier (recompute `i·k` chain steps, 48-byte proof, no queries),
the IVC verifier does ≥ `i · qV_step` oracle evaluations plus its native work, so its
verification-work advantage is at most about `k / qV_step`, and it always loses in proof size. With
`qV_step ≈ 5·10^3` (spartan-chain-class) and `k ≤ chainCap = 2^20`, the ratio is ≤ 200, and the
prover pays a ≈ `2^28`-constraint step circuit (issue #7's estimate) for it.

### 3.2 2→1 trees: deferral, concatenation, witness-sending (ranked tree `r = 8`, `n = 2^14`)

| | root oracle queries | root proof | root native work | prover work |
|---|---|---|---|---|
| witness-sending (`ws_ksRel`) | 0 | ≈ 12–16 KB | `2^22` compressions: 0.64 s unrolled, 37–43 ms threaded (**measured**, #6) | native chains ≈ 20 ms (**measured**) |
| concatenation of leaf SNARKs (`concatState`) | 256 × 5 156 ≈ 1.32·10^6 | 256 × 1.46 MB ≈ 375 MB | 256 × 0.8 s ≈ 205 s (6.4 s on 32 cores) | 256 × 7.7 s (**measured** per leaf) |
| deferral recursion (`deferState`) | ≥ 1.32·10^6 + nodes' own ≈ 2.6·10^6 | ≈ concatenation (2.3) ≈ 0.7 GB | one SNARK verify + 2.6·10^6 hash calls ≈ 1.3 s | concatenation + 255 node proofs ≈ 255 × 10 s |
| flat lift at the root (Theorem 4.1) | ≈ one SNARK (≈ 10^4) | ≈ 1–2 MB + 8 KB starts | one SNARK verify | one SNARK over `2^22` compressions ≈ `2^36` R1CS: infeasible |

All deferral and flat-lift entries are **estimates** (node circuit ≈ 2 × (10–14k compressions) ×
`2^14` constraints ≈ `2^28.3`, prove time scaled from the leaf's `2^28` at 7.7 s). Reading: in the pure
ROM, **deferral recursion is dominated by concatenation** in root oracle work, proof size and prover
work; what it buys is only the root's non-oracle native work (one SNARK's field arithmetic instead of
256), which the online root check pays back as 2.6·10^6 service calls. Recursion never beats
concatenation in the pure ROM for this relation; the flat lift beats both at the root and is
prover-infeasible at the root but ideal at low levels, which is the level-`j` flattening of issue #6
(b) and §5.3 of DESIGN-v3: witness-sending below `j`, flat SNARKs at `j`, concatenation or deferral
above. Under D2's charge (`t_hash ≈ T_leaf/n ≈ 0.47 ms`, **estimate**), deferral's root queries cost
≈ 620–1 200 s, about what proving those hashes in-circuit costs in v3 (§0): the charge reproduces v3's
incentive, no more.

### 3.3 "Compressing but not succinct": the exact condition

Define *compressing* as root verification work below witness-sending's, and *succinct* as root work
independent of the tree size. For a decoding design, 2.3 gives root work ≥ `Σ_leaves qV_leaf` hash
evaluations (+ nodes), against witness-sending's `2^d · n` compressions: compressing iff

    n  >  qV_leaf  (+ the per-leaf share of node queries),

up to the native-work constants, and never succinct (the root work is linear in the leaf count). At
`n = 2^14`, `qV = 5 156`: ratio ≈ 3.2; at `n = chainCap = 2^20`, with `qV` growing slowly (3 533 →
4 414 → 5 156 for `n = 16, 2^10, 2^14`, **measured**), ratio ≈ 170–200 (**estimate**). The user's hoped-for
"compressing but not succinct baseline" therefore exists exactly when the benchmark's `n` exceeds the
leaf verifier's query count, it is the deferral/concatenation construction, and the benchmark at
`n = 2^14` sits near the edge where it is barely compressing. Raising `n` toward `chainCap` is the
only lever; a cheaper-querying leaf verifier is the design incentive, and it is the one D1's charge
already expresses without any relativized clause.

## 4. Relations for which a relativized argument exists

### 4.1 The flat relation, and the lift (Theorem 4.1; sketched, kernel-checkable abstractly)

`RelFlat c (starts, n)` := `c = treeRoot (leafStmt (chainEnd sᵢ n) n)ᵢ ∧ n ≤ chainCap`; oracle-free,
witness `32·2^d + 8` bytes. Any ROM SNARK for it exists (Micali/BCS; spartan-chain at `d = 0`).
**Lift.** Given `V₀, E₀` with `KState RelFlat V₀ E₀ ε` and `qV₀` queries, define `V` to accept
(W) a witness-sending proof (`WitnessSending.check`, no query) or (S) `(starts, π₀)` by running
`V₀ (c) π₀` with the starts bound as public input (hash them: `2^d` compressions, no oracle), and
`E c (S starts π₀) L := node c₁ c₂ (W-proof of the left half) (W-proof of the right half)` when
`E₀` returns the same starts, else `none`. Then `KState (RelL V) V E ε` with `V₀`'s potential: an
accepted (S) proof gives, by `final` of `V₀`, the committed starts; the W-children are accepted by `V`
on *every* log (`runLog` of a `ret` is `some`), so `RelL V L c w` holds. Completeness for `RelO`: the
honest node prover reads the starts off either child format and makes an (S) proof. `qV = qV₀`.
Verdict: **exists, succinct in root queries, no recursion**; it is the proof that the relativized
clause is vacuous as an incentive. P1's `concatState` is the non-succinct special case
(`V₀` = concatenation); the abstract lift is the stronger statement to check (§7). Prover cost is
what makes the flat relation useless at the root (`2^36` constraints) and ideal at low levels.

### 4.2 A node relation carrying the deferred oracle claims in the statement

Statement `(c, h)`, `h = BLAKE2s(enc claims)`, node clause "each child accepted by `V` answering
from its claim list, and `h` hashes the children's lists plus the node's own"; genuineness of the
claims is checked by the consumer of the top statement. The relation is oracle-free (claims are
data), so a succinct ROM SNARK for it exists; its circuit never evaluates the oracle (CGH closed with
a secret oracle, as in D4 but without `certify`). But the top consumer must evaluate every claim:
`Σ inner` queries ≈ 2.6·10^6 at `r = 8`, and the root *proof* must deliver the claims, which are the
inner proofs' query inputs: concatenation size again (2.3). Verdict: **exists; it is deferral with
the re-asking moved from the root verifier to the harness**, same root query count, same proof size,
one fewer in-circuit hash gadget per claim. Native cost of the root check ≈ 0.5–1 s (**estimate**),
which is acceptable; nothing is gained in prover work. It is D4 minus the attestation, with the list
in the proof instead of in the service.

### 4.3 Relations whose child validity is oracle-independent

v3's `Rel Vb` is one: `Vb c₁ π₁` is a total Boolean function. The relation is oracle-free, a ROM
SNARK for it exists, and recursion means arithmetising `Vb`, BLAKE2s included. Verdict: **exists,
and it is v3**: the price is the heuristic composition (§5.3) and O-25 (the circuit knows the
oracle). Every "oracle-independent child validity" is of this kind or of kind 4.1.

### 4.4 The leaf over the oracle itself, `x = O^n(w)` (hopeless; sketched from [BCG] Lemma 6.3)

`R_chain^O := {(x, w) : x = O^n(w)}` with `w` 32 bytes. Fix `w`; the instance `x` depends on the `n`
answers `O(O^{i}(w))`, and flipping any one of them changes `x` (a new chain diverges, collision
probability `≤ n·2^-256`), while a unique witness holds except with probability `≈ 2^-224`. This is
Lemma 6.3's situation (unique-witness set `UF_n`, `Flip` at a random `i ∈ [t]`, `t = n`): a verifier
with `vq` queries asks the flipped point with probability ≤ `vq/(p n)` on all but `vq/p` positions
(Eq. 11), `P̃` reproduces the honest proof under the flipped oracle, and the instance leaves the
language; so `(1 − p)(1 − vq/(p n))(1 − 2^-224 − α) ≤ β`, i.e. `vq ≥ (1 − O(β + α + p)) · p · n`:
**no verifier cheaper than recomputing the chain**, whatever the proof size (the witness is 32 bytes,
so Theorem 2 is vacuous). Knowledge soundness is irrelevant: soundness alone is impossible. The
brief's choice to keep the leaf concrete is forced.

## 5. Composition

### 5.1 The claim (proved; P1 `compose`, `paper_tree`, **kernel**)

With `RelL`, `final` for the root gives `(V cᵢ πᵢ).runLog L = some true` for the extracted children on
the *same* `L`, which is exactly `final`'s hypothesis for `(cᵢ, πᵢ)` on that `L` (same `μ L < 1`, same
`L.length ≤ logCap`). Induction on an explicit depth `D` gives: below potential `1`, every accepted
root proof is extracted on `L` to depth `D`, every extracted node satisfying the leaf clause or the
node clause with both children extracted at depth `D−1`. The probability statement is `paper` applied
once: `Pr[root accepted on L ∧ tree not extracted to depth D] ≤ (Q + qV_root)·ε`, with no per-level
factor, for *every* `D`. The orchestrator's claim is correct.

### 5.2 Hidden conditions

1. **Coverage is forced, not assumed.** The theorem's log is the adversary's plus the root's; the
   children's verification queries must be in it (2.1). An adversary who withholds one makes the root
   reject w.h.p. (2.2); the honest prover cannot withhold them, because the root re-asks them. So the
   composition theorem is unconditional *and* implies deferral: `qV_root` in the bound already counts
   `Σ inner` queries.
2. **Length guard.** `L.length ≤ logCap` is the root's; the children reuse it. Fine within
   `Q + qV_root ≤ 2^96`; nothing is claimed beyond.
3. **Termination and cycles.** "Extracted to depth `D`" is the provable statement; "the walk ends in
   leaves" needs that the extractor never returns a child digest equal to an ancestor, which is a
   BLAKE2s fixed point/cycle in `nodeStmt` and cannot be excluded by counting (P1's `compose_flat`
   has it as a hypothesis, rightly). For the benchmark, `D = r` suffices: the extracted tree to depth
   `r` is a complete witness if every path ends at a leaf by then; a path that does not is a
   `nodeStmt` cycle or a tree deeper than the honest one, both of which are reported, not assumed away.
4. **Collisions.** `final` gives *a* witness; `c = nodeStmt c₁' c₂'` may hold for `(c₁', c₂') ≠` the
   honest children, and a node digest may also have a `leafStmt` preimage. KS is unaffected (any
   witness counts); the benchmark's intended reading "the prover knew *these* 256 starts" needs
   collision resistance of concrete BLAKE2s for `nodeStmt` and `leafStmt`, exactly as v3 needs it.
5. **Depth of the proof itself.** The bound has no `D`, but the honest *prover's* queries and the
   root's re-asked queries grow with the tree, so `Q + qV_root` does; the error is linear in the
   tree's total query count, which is the right accounting and matches the deferral bound.

### 5.3 Why `Rel Vb` cannot give this

`Rel Vb` reads the child verdict with `Vb c₁ π₁ = (V c₁ π₁).run blake2sOracle`. The theorem's `L`
holds arbitrary answers (random ones in the game); `Vb c₁ π₁ = true` says nothing about
`(V c₁ π₁).runLog L`, which is `none` whenever the child's queries are absent from `L` and `some false`
whenever `L` answers them differently from BLAKE2s. So `final` cannot be re-applied, and the gap is
real: P1's `V3.v3_no_compose` exhibits a certified v3 verifier accepting a node proof on a potential-0
log whose children are not extractable. Composition under `Rel Vb` needs "`L` agrees with BLAKE2s on
the children's paths", i.e. that the random oracle is BLAKE2s: the heuristic of DESIGN-v3 §5.4. Note
the trade: `RelL` composes *because* it forces re-asking; `Rel Vb` does not re-ask and therefore does
not compose. No definition gets both.

## 6. Escaping the oracle model: D4 and D3

### 6.1 Where the [BCG] technique breaks

The proof needs (i) two oracles at small distance that no `vq`-query verifier distinguishes
(§2.3), and (ii) an adversary that simulates the honest prover under the flipped oracle with the same
query budget (§2.4, §2.7). In D4 the verifier's view includes `attest(h)`, a deterministic function
of the *whole* oracle and the service's history: flipping one point `q` changes `attest` on every `h`
committing to a list containing `q`, so the induced oracles are far apart, (i) fails; and the
flipped-list prover cannot obtain `attest(h') = 1` for a list with `(q, a')` since `certify` evaluates
`O(q)`, so (ii) fails. In D3 the same step fails against unforgeability of the signature. This is
[BCG] §2.8's diagnosis for the LDROM/AROM ("oracles far from one another"), and the SROM of [CT10],
where relativized SNARKs exist. Theorem 2.2 of this note fails at step (a) for the same reason: the
flipped `(c, π)` is not honest under `O'` because its attestation is missing.

### 6.2 D4 as a knowledge statement in the potential form (sketched)

Model: one random oracle `O`; a service with store `S` (a set of certified lists) and two extra
operations, `certify(list)` (appends `list` to `S` iff every `(q, a) ∈ list` has `a = O(q)` or is an
attested hash, and returns `h = BLAKE2s(enc list)`) and `attest(h)` (returns `1` iff some `list ∈ S`
has `BLAKE2s(enc list) = h`). Global log `L` := every `O`-query anyone made, `certify`'s evaluations
included. Node clause: `RelL V L c (node …)` as before, with `V`'s `attest` calls answered from `S`.
**Claim.** If `V_node` runs a SNARK verifier for the circuit "`V` accepts `(cᵢ, πᵢ)` answering from a
list `Lᵢ` with `BLAKE2s(enc Lᵢ) = hᵢ`" and checks `attest(hᵢ) = 1`, then `KS_L` holds with the SNARK's
`ε` plus `Adv_CR(BLAKE2s)`: `attest(hᵢ) = 1` gives a certified list `Lᵢ' ⊆ L` with the same hash,
so `Lᵢ = Lᵢ'` unless a collision, so `(V cᵢ πᵢ).runLog L = some true` by monotonicity (P1
`runLog_of_agrees`), and the SNARK's extractor supplies `(cᵢ, πᵢ, Lᵢ)`. Composition is then §5.1 on the
global `L`: one bound `(Q + qV_root + |certify evaluations|)·ε + Adv_CR`. The root verifier makes one
`attest` (recursive) or `2^{d+1} − 1` (flat) plus the SNARK's queries: succinct. W2 reaches the same
model independently and formalises the CR disjunct in `final` (its M5: the collision must be an
*output of the budgeted extractor*, else "a collision exists" is provable by pigeonhole and `final`
is vacuous): I agree, and that is the right way to keep CR inside the counting form.

### 6.3 Flaws and costs

1. `attest` is not a uniform query. `KState.step` averages over `2^256` answers of a fresh query;
   `attest`'s answer is a function of `S`. The model needs a second query constructor whose `step`
   law is "no potential rise, answer determined by the store", and `final` must be stated for logs
   consistent with a store. This is a contract change (W2 estimates +50 lines), and the `paper`
   theorem must be re-proved for the two-oracle game.
2. The security is no longer "one random oracle": it is ROM for the SNARKs **plus** CR of concrete
   BLAKE2s for the list hash (standard-model, not countable) **plus** an honest, stateful service with
   a secret PRF key (harness trust; the first runtime component whose failure is accept-all).
3. The argument is not a NARG: the root check is online and stateful (`attest` at verification time),
   so proofs are not transferable and the store's lifecycle (per run, replay across runs, `logCap`
   accounting of `certify` evaluations) is part of the trusted procedure.
4. No in-circuit saving: hashing a child's `(q, a)` list in-circuit costs ≈ 1.5 compressions per
   claim against 1 for evaluating BLAKE2s on a 64-byte Merkle node (**estimate**); D4 prover cost ≈
   v3's. The gains are proof size (hashes instead of query inputs), a succinct online root check, O-25
   closed and composition provable; not speed.
5. Recursive `certify` must check that a list's attested-hash entries are in `S`, and the circuit
   must hash `(claims ‖ child hashes)`: CR again, fine. A denial-of-service surface (`certify` of huge
   lists) and the IPC cost of every Merkle hash going through the service (W2's M3/M4, C1) are
   engineering, not soundness.
6. Issues #6 and #7 are untouched: witness-sending needs no service and node extraction still decodes.

### 6.4 D3 (signed lists) and O-25

D3 replaces `attest` by a hash-based signature verified in-circuit: self-contained proofs, no online
state, security = ROM + EUF-CMA of the signature (standard-model; its hash must be concrete, since the
circuit evaluates it, so the signature cannot be "in the ROM" without reopening O-25 for its hash) +
CR of the list hash. In-circuit cost ≈ 10^3–10^4 compressions per signature (XMSS/SPHINCS-class,
**estimate**), per child, which is comparable to the whole child verification: D3 is strictly more
expensive than D4 and needs a strictly larger assumption; its only advantage is transferability.
**O-25.** The relation does not close it: the backdoor has a `KStateRel` (P1 `Backdoor.backdoor`).
The deployment closes it: with a secret-keyed oracle, `V`'s author has no value correlated with the
oracle except through queries, so the ROM theorem `(Q + qV)·ε` *is* the deployment theorem up to the
PRF advantage; the magic branch fires with probability `2^-256` per deployment. D2 gets this closure
at the price of deferral; D4 at the price of §6.3.

## 7. Lean targets

What P1 has kernel-checked already covers four of the orchestrator's five: `RelL`/`KStateRel`
(target 1), `compose`/`paper_tree` (2), `ws_ksRel`/`concatState` (3, in the non-succinct form),
`Backdoor.backdoor` (4), and `lazy_no_kstate`/`lazy_extractor_collides` (5, corrected). What I would
check next, all cheap, in order of value:

1. **The abstract lift (Theorem 4.1).** `KState RelFlat V₀ E₀ ε → KStateRel (lift V₀) (liftE E₀) ε`
   with `queries (lift V₀) = queries V₀`, `V₀` abstract. This is the precise vacuity statement: the
   relativized clause is met by *any* flat-relation argument with no recursion and no extra queries.
   `concatState` does not show it, because concatenation is non-succinct. Cost: a few dozen lines on
   P1's `Codec` frames; the W-children are accepted on every log by `rfl`-level reasoning.
2. **Deterministic deferral core (2.1, 2.2 (b)/(d)).** (i) `runLog L = some b → every query on the path
   ∈ L.map Prod.fst`; (ii) locality: if `q` is not on `(V c π)`'s path on `L` then
   `(V c π).runLog (L.erase q) = (V c π).runLog L`; (iii) for a decoding `E` and a child whose path on
   `L` passes `q`, `final` on `L.erase q` fails. Together: on any log of potential `< 1` where a
   decoding node verifier accepts without having `q` on its own path, the child's path cannot contain
   `q`. This is the kernel half of "the parent re-asks every live child query"; the probabilistic
   half (2.2 (c)) is `KStateRel.paper` and needs only the two-run adversary written as an `OProg`,
   which is worth doing if a reviewer doubts the sketch.
3. **`Sens` for a concrete verifier.** For the leaf of `W1` (P1's one-dummy-query witness-sending) the
   flipped answer is not live, so 2.2 gives nothing: a good negative control that the bound counts
   live queries only. For a Fiat–Shamir verifier the live claim is a `2^-b` counting fact per query;
   spartan-chain's certified `V` could supply the instance, but that is a larger job (not now).
4. **Target 5 as stated is unprovable; P1's correction is the right one.** "No `KState` for any `E`"
   would need a digest with no `nodeStmt`/`leafStmt` preimage (`acceptAll_kstate_iff`,
   `kstate_of_leaf_surjective`). Either keep P1's two forms (natural extractor; any extractor emits a
   collision) or state the probe over an abstract statement type with injective constructors, where
   the full `∀ E` form is provable and shows the *logic* of trusting is unsound independently of
   BLAKE2s.
5. **Prop. 1.4** (language oracle-free; `A^O ⊇ T` from completeness, `= T` modulo cycles) is a
   two-lemma lattice fact worth a probe only if a reviewer contests §1; otherwise paper.
6. **Not worth Lean now:** D4's two-oracle `KState` (a contract design, §6.3 item 1, to be done only if
   D4 is chosen); the proof-size bound 2.3 (information-theoretic, no finite model); 3.1–3.3 (arithmetic
   on estimates).

Mis-statements to avoid in the probes: do not write the deferral theorem with `RelO` (`run O`) in
`final`, since the log form is what forces coverage; do not state the lift with the starts *outside*
the public input (then `E` cannot tie the clear starts to the committed ones); and keep the depth `D`
explicit in every composition statement.

# Circumventing CGH uninstantiability with a secret-keyed oracle: the signed (SROM) and attested (D4) variants, a guide and a reading list

**Status.** A guide, not a design (2026-10-22). The normative proposal for this direction is
[`DESIGN-relativized-recursion.md`](DESIGN-relativized-recursion.md) (D4, merged in PR #14, not in
force). This guide is the on-ramp to it: the argument in the order a reader needs it, the decisions
it leaves open, and a map of every resource an agent needs to read, check or search. Nothing here is
implemented. Where this guide and the design disagree, the design wins; report the disagreement.

**Provenance.** Compiled from a design conversation with the user on 2026-10-22 (the user's
question: can a secret-keyed, signed oracle close the CGH gap, issue #4 / O-25?), the three v3
documents in this folder, the relativized design, the exploration branch `explore/relativized-nark`
(the exploration at `043bcb3`; the branch head `1360db5` adds the D4 doc's own review and the
axiom audit), and Chiesa–Guan–Samocha–Yogev, *Security Bounds for Proof-Carrying Data from
Straightline Extractors* (CGSY24), whose PDF is in [`reference/papers/`](reference/papers/).

**Evidence tags**, as in the other documents: **kernel** (a Lean theorem on `propext`,
`Classical.choice`, `Quot.sound` only), **paper**, **measured** (a log), **estimate**. An untagged
sentence is explanation; its pointer says where the claim is argued.

| Short name | Meaning |
|---|---|
| O-25 | the open problem: a ROM certificate cannot see the deployment oracle ([O-25 doc](v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md)) |
| `PRF_k` | BLAKE2s-256 in keyed mode under a secret key `k` |
| SROM, D3 | the signed random oracle model (Chiesa–Tromer 2010); D3 is its use here: answers signed under a public key, signatures checked in-circuit |
| D4 | the attested oracle: a trusted service certifies lists of answers; a verifier asks it whether a list hash is attested |
| D4 doc | [`DESIGN-relativized-recursion.md`](DESIGN-relativized-recursion.md) |
| v3 doc | [`v3-design-…`](v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md) |
| CGSY24 | ePrint [2023/1646](https://eprint.iacr.org/2023/1646), local copy in [`reference/papers/`](reference/papers/) |

---

## 0. Summary

1. **What CGH needs.** Every CGH-style backdoor has one trigger: "accept if the prover shows it can
   compute the oracle itself". In the ROM nobody can, so the branch is dead code and the verifier
   passes its knowledge-soundness proof; deployed with public BLAKE2s, anyone can. v3 certifies such
   a verifier in the kernel (`Controls/Backdoor.lean`, O-25 doc §1.2).
2. **A secret key removes the trigger.** If the oracle is `PRF_k`, with `k` held by a harness process
   and sampled after the verifier is frozen, a certified verifier's ROM bound carries over to the
   deployment up to the PRF advantage of a distinguisher that runs the whole evaluation (paper,
   standard hybrid; D4 doc §4.9). One falsifiable assumption about one fixed function then serves
   every verifier, where the random-oracle heuristic is a separate conjecture for each scheme; the
   O-25 candidates E and T tried to get that uniformity by restricting the verifier.
3. **A secret key alone kills recursion.** A node must check its children's oracle answers inside a
   circuit, and a circuit cannot evaluate `PRF_k` without `k`. Handing `k` to the prover reopens CGH;
   carrying the answers up to the root makes the root re-ask the whole tree (D4 doc §3.2); and in the
   pure ROM, Barbara–Chiesa–Guan (ePrint 2024/728) rule out relativized succinct arguments for hard
   oracle relations, an obstacle that returns for our relation once knowledge is required (D4 doc §2).
4. **Make the answers checkable without the key.** Two ways. **Signatures** (SROM, D3): the oracle
   signs what it answered; the circuit checks a signature under a public key. **Attestation** (D4):
   the harness is trusted and online, so the oracle simply remembers what it certified and a verifier
   asks it; the parent circuit only hashes the list. D4 needs no signature scheme; D3 buys offline,
   third-party verification during an evaluation.
5. **The relation stops instantiating the oracle.** v3's node clause `Vb c₁ π₁ = true` (V run on
   public BLAKE2s) becomes "V accepts `c₁, π₁` reading answers the oracle vouched for". The
   submitter's theorem keeps its shape: one-level knowledge soundness in the ROM, with a straightline,
   step-bounded extractor (§4, §5).
6. **The tree follows from a published theorem.** CGSY24 Thm 5.1: a straightline extractor run on one
   log extracts the whole proof-carrying-data tree with no factor per node (the error still grows with
   the number of queries the whole tree makes); kernel for every attested
   knowledge state in the exploration's probes, paper for a succinct node (D4 doc §4.6, RO-1).
7. **The price.** A trusted keyed-oracle service whose bug would be accept-all; every oracle call
   over inter-process communication; part of the prover's time spent in contract code; PRF security
   of keyed BLAKE2s and constructive collision resistance of BLAKE2s as assumptions; either a
   designated-verifier window until key release (D4) or in-circuit signature checks (D3); and leaving
   v3's decision V3-5 (the random-oracle model only) for a trusted harness capability, which the user
   has not decided (RU-1).

The rest of this guide follows that order: §1 CGH, §2 the key, §3 why recursion breaks it, §4 the
signed variant, §5 the attested variant, §6 what an evaluation checks, §7 incentives and costs, §8
the O-25 criteria, §9 open questions, §10 the reading list, §11 where to find everything.

---

## 1. What CGH needs, and our instance of it

**The mechanism** (Canetti–Goldreich–Halevi, STOC 1998, JACM 2004). A scheme proved secure with a
random oracle is given a branch that fires when the prover exhibits a short program agreeing with
the oracle on the points the verifier checks. A random function has no such program, so the branch
fires with negligible probability and the security proof holds. Any concrete hash function *is*
such a program, so after instantiation the attacker supplies it and the branch fires. The argument
needs the instantiation to be public: the seed of the function family must be known to the
adversary (CGH §4; D4 doc §4.9).

**Our instance.** v3's knowledge-soundness definition is a counting statement over all oracle
functions; a verifier that computes BLAKE2s, compares it with an oracle answer and on a match
accepts a fixed "magic" proof errs on a `2^-256` fraction of oracle functions, which the definition
cannot see. The kernel certifies it (`RecursionFast/Controls/Backdoor.lean` on branch `v3/contract-archive`;
O-25 doc §1.2), it passes every check of the benchmark run (O-25 doc §1.3), and no salt helps because the
proof can carry the salt (O-25 doc §1.4). The disguises (O-25 doc §2) and the post-hoc challenge
verification attack (O-25 doc §6.1: after a challenge, the prover sends BLAKE2s wires over the
transcript prefix and low-degree checks show the challenge equals their output) defeat every
rule-and-review fix examined. Candidate E (a parametric verifier) was broken. The user rejected MG1,
the middle ground of Candidate T (a contract-owned template): "this severely restricts the design
space for autoresearch agents, while still adding a huge gap for reviewing proposals, and requiring
manual intervention"; that T is excluded too is the authors' inference (O-25 doc §4–§8).

**The deployed-protocol version.** The same failure reaches natural protocols once the proved
statement can evaluate the hash: Khovratovich–Rothblum–Soukhanov (ePrint 2025/118) attack GKR with
Fiat–Shamir, and Fenzi (ePrint 2026/1838) extends the attack to program-generated R1CS (Spartan and
Aurora variants) and proves the fix of binding the statement into every seed (O-25 doc §9.2;
constraint C15). A recursive SNARK is exactly a protocol whose proved statement evaluates the hash:
the node circuit runs the child's verifier.

---

## 2. Step 1: a secret key

**The deployment.** The oracle is `PRF_k(q)`: BLAKE2s-256 in its keyed mode (RFC 7693 §2.5 and
§3.3: the key length in the parameter block, the padded key as the first message block), not
`BLAKE2s(k ‖ q)`, so that keyed and public BLAKE2s are different computations on every input and no
length-extension reasoning is needed (D4 doc §4.8). `k` is 32 bytes from `os.urandom`, fresh for
every timed run, held by a separate process the prover's sandbox cannot read, and never logged. At
reset it is destroyed, or, under W4's key release (§5), sealed until the record is frozen; the D4
doc says both (§9).

**The hybrid** (paper; D4 doc §4.9; the exploration's [L1] §11). Let *bad* be the event "the root
is accepted and `treeExtract` returns neither the leaf starts nor a collision". It is decided by an
efficient tester with oracle access: the extractor is step-bounded (about `2^58` steps and at most
about `2^28` queries at the ranked size, D4 doc §4.9 fine print (1)), and checking the relation costs
a bounded number of hashes. So

```
Pr_deploy[bad] ≤ Pr_random function[bad] + Adv^PRF(D),
```

where `D` runs the whole evaluation and the extractor. For a certified `V` frozen before `k` is
sampled, both terms are small: the first is the certificate's bound, the second one assumption about
one fixed function, the same for every `V`. A verifier that recognises the oracle would be a
distinguisher between `PRF_k` and a random function; no value about `PRF_k` exists before `k` is
sampled.

**Conditions.** `k` is sampled after `V` is frozen; neither `V`, the Lean prover `P`, the native
prover, nor `V`'s author ever holds `k`; the key is fresh per run (a reused key is a published
oracle); the service implements its specification (tested, not proved; D4 doc §4.9 fine print
(3)); the steps from the lazily sampled oracle of the Lean theorem to a random function are on paper,
as in v3.

**A side benefit.** Nobody can evaluate the oracle except through the service, so the service's log
is the complete query log. The straightline extractor's view in the theorem is then a file the
harness actually holds: liveness reads the service's authentic log (D4 doc §4.8).

---

## 3. Step 2: why a secret key alone kills recursion

A node proof says "I know child proofs `π₁`, `π₂` that `V` accepts". `V` needs oracle answers to run.
Inside a circuit there is no oracle, so the prover supplies the child's query–answer pairs as part of
the witness. Unless something ties those pairs to the real oracle, the prover can invent them, for
example by choosing Fiat–Shamir challenges that a fake child proof happens to pass, and the node
statement holds with no valid child. The candidate ties:

| Tie the answers to the oracle by | Outcome | Where it is argued |
|---|---|---|
| evaluating `PRF_k` in the circuit | the prover must hold `k`; the oracle is public to the attacker again and CGH is back | O-25 doc §1.4 (a backdoor that takes the key from the proof and checks two oracle points is certifiable by counting); D4 doc §4.8, "Isolation" |
| a MAC on each answer | verifying a MAC in-circuit needs the key that creates it: the problem of the row above, unless the key holder verifies online, which is D4 (last row) | (standard) |
| carrying the answers out of the circuit for the verifier to re-ask | sound, but each parent carries its children's answers and the root re-asks the whole tree: not succinct (the "re-ask law") | CGSY24 §2.3 and Constr. 6.8; D4 doc §3.2: re-asking is sound (kernel `deferState`, `queries_defer`), a parent that does not re-ask is not (kernel `lazy_no_kstate`), the root's cost is [T1] Thm 2.2 (paper) and [C1] (estimate) |
| a signature under a public key (SROM, D3) | works: checkable without `k`, unforgeable without the signing key | §4; CT10; CGSY24 §2.2, §6.2 |
| online attestation by the trusted service (D4) | works: the service's memory replaces the signature | §5; D4 doc §4 |

**The pure ROM cannot do better.** Barbara–Chiesa–Guan (ePrint 2024/728, TCC 2025) prove that
relativized succinct arguments in the ROM do not exist. Their separations are for specific hard
relations and do not apply verbatim to our relation, but once knowledge is required the obstacle
comes back by their flipping technique: a verifier that does not ask a query a child's validity
depends on cannot see that answer flipped (D4 doc §2; the exploration's [T1]). The relativized
SNARKs in the literature live in oracle models with an extra capability: the SROM, the low-degree ROM
(CCS22), the arithmetized ROM (CCGOS23), the open-and-sign ROM (MMZ25) and signed answers from
trusted hardware (CGY26); §10 A.

---

## 4. Step 3a: the signed random oracle (SROM; D3)

**The model** (Chiesa–Tromer, ICS 2010; CGSY24 §2.2 and §6.2). On a new input `x` the oracle samples
a random answer `y`, signs `(x, y)` under a secret signing key embedded in it and returns `(y, σ)`;
repeated inputs get the same answer. Anyone holding the public key `vk` can check that the oracle
answered `x` with `y` without asking it. CGSY24 §2.2: any SNARK in the ROM with a straightline
extractor becomes a relativized SNARK in the SROM, with straightline extraction, up to an error
depending on the signature scheme: to prove an oracle computation, replace every oracle call by a
sub-computation that verifies a signature.

**Our instantiation.** `y = PRF_k(x)` instead of a sampled table (a table for the ranked tree does not
fit in memory, D4 doc §4.8); the service signs the digest of a whole list of answers (hash-then-sign),
not each answer, so a child costs one signature check plus hashing its list; the signer refuses an
over-cap trace, as D4's `certify` does. The signing key pair is fresh per timed run, like `k` (D4
resets `k` and `S` per run so that repeat 2 cannot reuse repeat 1's certified state, D4 doc §4.8
"Lifecycle"; a per-evaluation `vk` would let repeat-1 child proofs verify in repeat 2), every node of
one tree uses the same `vk`, and every run's `vk` is published with the record. A verifiable random
function service (RFC 9381; Ghosal et al., ePrint 2026/2114) bundles a PRF and a proof of correct
evaluation, but the standard ECVRF is elliptic-curve based with a random-oracle-model analysis (it
brings back a group, against V3-5, and a heuristic), and against a trusted, deterministic service its
uniqueness adds nothing ([L1] §6).

**The relation** (a sketch in v3's notation, written for this guide and checked only by its own
review; the contract would fix names):

```lean
abbrev Trace := List (ByteArray × Digest)                -- query–answer pairs
-- The agent's verifier stays an uninstantiated query program (v3's `OProg Bool`, given the key):
--   V : VK → Digest → Proof → OProg Bool
def runWith (tr : Trace) : OProg Bool → Bool             -- answer from tr; a miss rejects
/-- D4's prefix-free item code per pair, `0x00 ‖ enc64 |q| ‖ q ‖ a` (D4 doc §4.3). -/
def encodeTrace (tr : Trace) : ByteArray
def traceDigest (tr : Trace) : Digest := blake2s256 (tagTrace ++ encodeTrace tr)   -- public, tagged
/-- D4's caps (RR-4): without them two distinct traces share an encoding (kernel `encList_not_inj`). -/
def TraceOK (tr : Trace) : Prop :=
  tr.length ≤ listItemCap ∧ (encodeTrace tr).size ≤ listByteCap ∧ ∀ p ∈ tr, p.1.size ≤ queryCap
def SigOk (vk : VK) (m : Digest) (σ : Sig) : Bool        -- contract-fixed scheme
/-- A child accepted against a signed, capped trace, within the proof-size cap. -/
def accS (V : VK → Digest → Proof → OProg Bool) (vk : VK)
    (c : Digest) (π : Proof) (tr : Trace) (σ : Sig) : Prop :=
  π.size ≤ proofCap ∧ TraceOK tr ∧ runWith tr (V vk c π) = true ∧ SigOk vk (traceDigest tr) σ = true

inductive Wit
  | leaf (s : Digest) (n : ℕ)
  | node (c₁ c₂ : Digest) (π₁ π₂ : Proof) (tr₁ tr₂ : Trace) (σ₁ σ₂ : Sig)

def Rel (V : VK → Digest → Proof → OProg Bool) (vk : VK) : Digest → Wit → Prop
  | c, .leaf s n => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ π₁ π₂ tr₁ tr₂ σ₁ σ₂ =>
      c = nodeStmt c₁ c₂ ∧ accS V vk c₁ π₁ tr₁ σ₁ ∧ accS V vk c₂ π₂ tr₂ σ₂
```

Every BLAKE2s in `Rel` is the public application hash (chains, statement digests, the trace digest,
the signature scheme); none is the oracle. The submitter proves, for every `vk`, v3's one-level
knowledge soundness for this `Rel` against a random oracle, with the extractor reading the log of
every query by the adversary and by `V`.

**The step to the tree, owned by the contract and independent of the entry** (paper; this guide's
argument, checked only by its own review). It departs from the exploration's [W1] §4, which puts the
signing oracle into the knowledge state and calls that the "Hardest formalisation of the set": here
the submitter's theorem stays signature-free and the signer is handled by a reduction.

1. The deployed prover can also ask for signatures, which the theorem does not mention. The theorem
   still covers it, because the potential-form statement quantifies over every query algorithm,
   including one holding the signing key: such a reduction plays the signer using only oracle
   queries, so `t` grows by the signer's checks. This is why the signer checks every pair by querying
   the oracle: those queries land in the log the extractor reads. Fiore–Nitulescu (ePrint 2016/112)
   show that SNARK extraction can fail against adversaries with an exogenous signing oracle; this
   guide's reading is that it does not bite here, since the extractor only reads the query log and
   never runs the adversary non-black-box.
2. If signatures cannot be forged and BLAKE2s is collision-resistant, with `encodeTrace` injective on
   capped traces (as D4's `encList_inj`), every trace in an extracted node witness was signed by the
   service. Its answers are then the oracle's, so `runWith trᵢ (V vk cᵢ πᵢ) = true` implies that
   `V^H vk cᵢ πᵢ` accepts: the child is a genuinely accepting proof.
3. Apply the theorem to each child with the same global log: CGSY24 Thm 5.1, no factor per node. The
   forger built from the whole evaluation runs every extraction, so its size is CGSY24's
   `s′ = s + O(N·t_ARG)`.
4. Error: `κ(t′) + Adv_sig + Adv_PRF` plus BLAKE2s collisions (trace digests, and `nodeStmt` and
   `leafStmt` as in D4's `.coll` output), `t′` counting the signer's queries.
5. Not addressed here: completeness with honest provers obtaining signatures inside the game, the
   analogue of D4's `failCtx` over honest contexts (D4 doc §4.5).

**Controls.** Positive: honest children with service-signed traces satisfy the node clause.
Negative: with `SigOk` removed, a made-up trace that answers `V`'s challenges in the prover's favour
also satisfies it, which is the vacuity the signature closes; and two distinct over-cap traces with
one encoding (D4's `hashList_not_coll`), which `TraceOK` excludes.

**Costs** (estimates from the exploration): +145 (XMSS, leanSig parameters) to +1,059 (WOTS+ worst
case) 64-byte compressions per child, 0.5–12% of a node (D4 doc §3.4, §7.3; [C1] §4.2). An
XMSS-class verification is about 160 hash invocations ([L1], from Flock §1.1). If the signature and
the trace digest are BLAKE2s-based, the whole tax runs on the agent's own BLAKE2s gadget, which the
leaves need anyway. The trusted-line estimate of 150–300 lines (D4 doc §3.4, [W1] §4) is for the
exploration's route, with the signing oracle in the knowledge state; the route above needs a trusted
`SigOk` specification plus unforgeability as a paper assumption, and is unsized.

**The signature's own proof model.** The scheme is fixed by the contract, so an agent cannot design a
backdoor around it, but if its security proof itself models a hash as a random oracle, that is a
heuristic the trust statement must list. Check the proof model of the exact variant chosen before
claiming "no random oracle anywhere". RFC 8391 defines SHA-2 and SHAKE parameter sets only, so a
BLAKE2s XMSS is a non-standard instantiation, and RFC 8391's XMSS and the original paper's differ in
their hash calls.

**When D3 is the right choice.** When proofs must be verifiable offline, by third parties, during an
evaluation. Otherwise D4 dominates it (D4 doc §3.4, RU-2). Offline checking also needs the root's
own trace: the root's Fiat–Shamir and Merkle answers are `PRF_k` values a third party cannot compute,
so `root.bin` must carry `(π, tr, σ)` for the root verifier's run, and the checker evaluates `accS`.

---

## 5. Step 3b: the attested oracle (D4), or why a trusted harness needs no signatures

**The point.** The checks that make an evaluation happen on a trusted machine that is online for the
whole run. Anything the harness checks itself (the root check, the sample checks, the extractor run)
needs no signature: it asks the service. A signature is needed only for a check the harness never
sees, a parent circuit's check of its child's answers. D4 replaces that signature by a membership
query: the parent circuit only proves "the child is accepted reading list `xs`, and `xs` hashes to
`h`", the node proof carries `h` in the clear, and the parent's verifier asks the service whether `h`
is attested. In the exploration's words, D4 is the SROM with an online MAC: query accumulation with
the organiser as the decider ([L1] summary item 4).

**The service** (D4 doc §4.8; per timed run: `k`, and `S`, a set of attested digests, initially
empty):

| Call | The service does | Returns |
|---|---|---|
| `query(q)` | `PRF_k(q)` | the answer |
| `certify(xs)` | for each `ans q a`, check `a = PRF_k(q)`; for each `att h`, check `h ∈ S`; enforce the caps; if all pass, add `listHash xs` to `S` (atomic) | a bit |
| `attest(h)` | `h ∈ S` | a bit |

Caps per run: queries of at most `queryCap = 2^20` bytes, at most `2^20` `certify` calls, `attest`
counted in the verifier's `qV`. A refused call aborts the verification as a reject, never returning a
value `V` can branch on (RR-8).

**Recursion without re-asking.** A child's verifier makes `attest` calls on its own children's list
hashes, so the child's list holds `att h` items, which the service checks when the parent certifies
it. Certification is recursive, so inside the tree no verifier talks to the service; only the runs
of `V` the harness makes (the root, sample, canary, column R and DoS checks) do, with two `attest`
calls per node proof checked, or one when the node prover certifies `[att h₁, att h₂]` (RR-3). A flat
variant, attesting everything at the root, costs 511 calls and 16,352 B at `r = 8` (D4 doc §4.8).
The service never verifies a proof; if it did, the organiser would become the prover of record.

**The relation** (D4 doc §4.1; the exploration's probes define it without the `proofCap` conjunct,
P1's `RelL` and P2's `RelA`):

```lean
def accL (V : Digest → Proof → OProg Bool) (L : Log) (c : Digest) (π : Proof) : Bool :=
  π.size ≤ proofCap && ((V c π).runLog L == some true)
def Submission.RelL (S : Submission) (L : Log) : Digest → Wit → Prop := Rel (accL S.V L)
```

A node's children must be accepted by `V` **reading the same log as the knowledge game**, so `final`
applied to the root gives children to which `final` applies again, and the relation never evaluates
the oracle. `Rel`, `Wit` and the concrete leaf chain are v3's. The relation alone does not close
O-25: the backdoor is relativized knowledge-sound too (kernel, `Backdoor.backdoor` in the
exploration's `Relativized/Backdoor.lean`); the deployment's secret key closes it (§2).

**Composition** (D4 doc §4.6). One extractor walk over the harness's tree on one log returns the
leaf starts or a BLAKE2s collision pair, with error about `Q·ε`, `Q` counting every fresh query of
the evaluation: about `2^-100` at `ε = 2^-128` for the ranked tree (estimate), with no factor per
level. Kernel for every attested knowledge state (`compose_all`, `Paper.paper_tree`); paper for the
succinct node's own `final`, which must decode the children and lists from its committed witness
(RO-1).

**What D4 costs that D3 does not.** The root check is online and stateful, so until the key is
released the competition is designated-verifier. W4 (D4 doc §4.10) publishes the per-evaluation log
of certified list hashes and releases `k` after the record is frozen, so anyone can re-run the root
check offline; proofs made after release are never evidence.

---

## 6. What an evaluation checks and measures (D4 on v3's benchmark)

The benchmark is v3's (v3 doc §8; D4 doc §7.1): one native prover process proves the whole tree,
ranked by wall time (board T); the root step is reported (column R). What D4 adds is the service, a
fresh state per timed repeat, and the rule that every check of a repeat runs against that repeat's
state before the reset.

| # | Step | Checked or measured | Service use |
|---|---|---|---|
| 0 | fresh `k` and `S` for the repeat; fresh chain starts per evaluation (per repeat under D4+ if RU-6 adopts A3's recommendation) | `k` is sampled after setup, so nothing oracle-dependent is precomputed | started |
| 1 | setup: build the native prover | untimed | none |
| 2 | **tree run**: 256 leaves, 255 nodes (`r = 8`, `n = 2^14`) | **timed: board T, ranked** | every Merkle, Fiat–Shamir and grinding hash; one `certify` per child list |
| 3 | root check: `V` on the runner's root digest and `root.bin` | must accept; succinctness cap `T_V` (a CPU-time rule without D4+, a liveness cap with it) | the verifier's queries and its one or two `attest` calls |
| 4 | sample checks: 16 inner proofs | must accept | as step 3 |
| 5 | root step: a fresh prover on two level-7 children | timed: column R, reported | as step 2 |
| 6 | canaries: altered proofs | must reject | as step 3 |
| 7 | extractor liveness at `r = 1`, `n = 16` | `E`, on the service's authentic log, returns a witness or a collision pair within its proved bound; the harness checks either | its log |
| 8 | DoS column: worst `V` time over random proofs | published | as step 3 |

The timed steps repeat three times; medians are reported. The service is reset between repeats.

**What makes up the measured time.** Hashing the leaf chains (public BLAKE2s, the agent's code); the
SNARK's field work (the agent's code); oracle calls (the contract's service, running on the prover's
own cores, §7); in each node circuit, hashing each child's list instead of recomputing its oracle
calls (the agent's circuit). Security is not measured: it comes from the certificate and the
contract's composition and deployment arguments; the run measures time and catches gross failures.

---

## 7. Incentives, design space and proving time

**Hashing moves into contract code.** With the key hidden, every oracle call the prover makes,
Merkle hashes included, goes through the service. Outside the prover's resources the service would be
a free co-processor of `2^33`–`2^35` compressions per tree (estimate), so its workers run on the
prover's cpuset and CPU cgroup (RR-8; D4 doc §4.8). Agents can no longer win by writing a faster
oracle hash; they win by hashing less and by batching well. The contract must ship a fast service (a
double-buffered ring per prover thread, flushes of at least `2^10` calls, a SIMD multi-buffer
BLAKE2s), because its speed is now part of every score.

**Inter-process cost** (**measured** on the 32-vCPU VM with 65-byte calls, [C1] §5.2, logs
[svc.log][m-svc] and [svc-multi.log][m-svcmulti]): a futex round trip per call (37 µs) costs 82× an
in-process call, a spinning one 2.3×, 256 calls per spinning round trip 1.22×; 10–12.5 M calls
per second machine-wide. **Traffic** (estimate from measured): 262,614 calls and 278 MB per
spartan-chain leaf, 6.7·10^7–2.7·10^8 calls per tree; +0.3–1.2% of leaf time for spartan-chain,
+30–110% for a Flock-class prover with a naive service (D4 doc §7.3).

**The node circuit.** D4: about 1.09× a real public-hash recursion step for a spartan-chain child
(28.3k against 25.9k compressions, estimate, [C1] §4.1). D3: +0.5–12% per child for the signature.
W5, the optional channel split (D4 doc §5), hashes Merkle trees with public BLAKE2s and attests only
the roughly 500 Fiat–Shamir answers per proof: about a thousandth of the traffic and exact in-circuit
costs, for one unfalsifiable extractability heuristic that the user must accept (RU-1).

**Design space.** The submitter keeps the verifier, the proof system, the field, the code, the query
strategy, grinding, and recursion or accumulation; there is no menu. In the authors' reading, the
design-space part of the user's objection to MG1 therefore does not apply; whether the review and
manual-intervention parts do has not been put to the user (O-25 doc §13; §8). What is lost: in-circuit tricks that exploit the oracle's internals for the
verifier's own queries (W5 restores them under its heuristic), and approaches that need a
non-black-box view of the oracle (low-degree or arithmetized random oracles, unservable at
digest-sized domains, D4 doc §3.4). The list hash is fixed by the contract as BLAKE2s ("no menu", D4
doc §4.3), which keeps v3's field neutrality (V3-1); an algebraic list hash would make nodes cheaper
but favour its field.

**Incentives** (D4 doc §8, selected rows):

| Strategy | What stops it |
|---|---|
| the backdoor and every disguise of O-25 doc §2; the liveness mirror | no value about `PRF_k` exists to compare with: fires with probability at most `Adv_PRF + 2^-256` per comparison |
| carrying `k` out of the service | a separate process the sandbox cannot read: own uid, no ptrace, seccomp, shared memory only for the rings |
| replay across repeats, evaluations or submitters | fresh `k`, `S` and starts; checks before the reset; per-evaluation logs |
| the service as a free co-processor | it runs in the prover's CPU cgroup |
| witness-sending at the root (#6(a)) | the CPU-time `T_V` rule, or the certified caps under the optional D4+ (D4 doc §6) |
| flattening below a level (#6(b)) | not stopped by any theorem studied; the benchmark shape (RU-4, D4 doc §7.2) |
| grinding | allowed: completeness error `δ` per honest prover run; costs prover time |

---

## 8. Against the O-25 criteria

The O-25 doc §11 lists ten criteria a solution must meet. The D4 doc has no assessment against them;
the column below is this guide's reading of the D4 doc, **not put to the user**. The O-25 doc (§0,
§10.2, §13) and the v3 doc (§17.1) record that the user has not been asked whether D4 avoids
narrowing the design space, a review surface and manual intervention, the three parts of the
objection to MG1.

| # | Criterion | D4, in this guide's reading |
|---|---|---|
| 1 | no narrowing of the design space | met in the authors' reading: the rule restricts how the oracle is deployed, not which proof system a submitter may use; no menu. The user has not been asked (O-25 doc §13) |
| 2 | no large human review surface | met in the authors' reading: the v3 §6.7 recognition rule and the intake review of `V` are deleted (RR-7); what remains to read is the service (300–400 lines) and about 53 contract lines, once. The user has not been asked |
| 3 | no manual intervention | the path from pull request to verdict is the harness; what a reader could count as manual is the designated-verifier window and W4's key release after the record is frozen (RU-2). The user has not been asked |
| 4 | survives the kernel attacks and the post-hoc one, with the backdoor written for it | the backdoor is written and relativized knowledge-sound (kernel, `Backdoor.backdoor`); it is stopped at the deployment by the PRF hybrid (paper); the post-hoc attack needs BLAKE2s wires for `PRF_k`, which nobody outside the service can produce (paper) |
| 5 | a kernel certificate within the trusted budget | one-level certificate unchanged in kind; about +53 trusted lines, to about 345 of 500, plus a few lines each for `WF` and `Honest`, and a trusted runtime service of 300–400 lines (estimates, D4 doc §4.7, §10) |
| 6 | states its guarantee and adversary | D4 doc §10: PRF security of keyed BLAKE2s, constructive collision resistance of BLAKE2s, a correct service; it leaves V3-5 (RU-1); "ROM-secure ⇒ BLAKE2s-secure" is not claimed, and a public-hash deployment of a winner still rests on the usual heuristic (RU-5) |
| 7 | covers the liveness mirror | closed by the same reduction (paper); liveness reads the service's authentic log |
| 8 | honest recursion expressible | yes: a node verifies children against attested lists, one or two `attest` calls per node; kernel only with children in the clear (`attState`), the succinct node is paper (RO-1) |
| 9 | statement binding of every transcript seed (Fenzi26, C15) | not mandated by D4; D4 doc §4.9 argues Fenzi's attack does not apply under a secret key; C15 asks for the rule regardless |
| 10 | built against a real entry first | **not yet**: stages R1 and R2 (D4 doc §11) with spartan-chain are the test |

---

## 9. Open questions and the user's decisions

**Decisions for the user** (none taken yet; D4 doc §12.2): RU-1, a trusted service and the PRF
assumption, leaving V3-5 (W5 adds a heuristic); RU-2, the designated-verifier window or D3; RU-3, "a witness or a collision computed by
the extractor" as the clause; RU-4, the benchmark shape or an explicit flattening policy; RU-5,
records certify the attested deployment; RU-6, whether to run R3 (D4+) and R4 (W5).

**Open items** (D4 doc §12.1): RO-1, the succinct node's `final`, decoding the children and lists
from the committed witness (paper only); RO-3, from node completeness to completeness over honest
contexts (one node kernel-checked); RO-5, `logCap` against the extraction domain; RO-8, measuring
leanVM's recursion verifier and a SIMD service before `T_V` is fixed.

**Raised by this guide** (unreviewed):

- **The deployment argument is paper.** The PRF hybrid, the signature step (D3) and the passage from
  the Lean theorem's lazily sampled oracle to a random function are not in Lean. They do not depend on
  the entry, so the contract could formalise them once; nobody has scoped that.
- **D3's signature proof model** (§4): pick the exact scheme and check whether its proof uses a random
  oracle before claiming that no heuristic remains.
- **Pricing the service.** Per-call and per-compression charges were examined for D1 and rejected
  as gameable or as certificate quantities (D4 doc §3.1; [A1] M3–M7). RR-8 charges the service's CPU
  to the prover by placement. Whether a fixed price per byte, used together with placement, would make
  scores less dependent on the service's implementation is not examined; it would be a cost model,
  which v3 rejected (v3 §8.1).
- **The empty query.** The service caches the state after the key block, so a non-empty call costs
  what an unkeyed one does; the exploration measured with that cache ([C1] §5.2–§5.3; D4 doc §4.8).
  For the empty message RFC 7693 §3.3 makes the key block the final block, so the cached fast path
  does not apply. The v3 backdoor control's trigger query `q0` is the empty string, so this case is
  the first one an attacker exercises: the service needs a test vector for it.
- **Disagreements with the D4 doc**, reported as its status line asks. (a) D4 doc §2 places
  `Controls/Backdoor.lean` "on `main`"; since PR #13 it is on `v3/contract-archive`
  (`RecursionFast/Controls/Backdoor.lean`). (b) Its header calls `docs/DESIGN-v3.md` authoritative;
  `main` no longer has that file (it is on `v3/contract-archive`, and the v3 doc here replaces it).
  (c) D4 doc §4.8 has the key "never written, destroyed at reset", while §4.10 and RR-9 release it
  after the record is frozen; under W4 each run's key must be sealed at reset and kept until release.

---

## 10. Reading list

Ordered by how much each item matters to this direction. **Checked** marks an ePrint identifier
whose page title was fetched and matched on 2026-10-22; the others come from the user's literature
list or from the exploration's [L1] and were not re-fetched. The exploration's [L1] has reading notes
(what was read, section by section, and what each result implies here) for most of A, B and E, and
for CGH, KRS25 and Fenzi in C; the O-25 doc §9 covers C and D.

**A. The core of this direction: recursion in oracle models**

| Item | Why read it | Link |
|---|---|---|
| Chiesa, Guan, Samocha, Yogev, *Security Bounds for Proof-Carrying Data from Straightline Extractors*, TCC 2024 (CGSY24) | Thm 1 / Thm 5.1: PCD from a straightline-extractable relativized argument loses no factor per node; §2.2 and §6.2 the SROM; §2.3 and Constr. 6.8 the non-succinct "trace in the proof" construction; §2.3 the idealisation of recursive STARKs | [ePrint 2023/1646](https://eprint.iacr.org/2023/1646) (checked; CC BY 4.0); local PDF [`reference/papers/`](reference/papers/) |
| Chiesa, Tromer, *Proof-Carrying Data and Hearsay Arguments from Signature Cards*, ICS 2010 (CT10) | the original SROM: a trusted signing token makes the verifier's oracle calls checkable without the oracle; straightline extraction from the token's transcript | [PCD project page](https://projects.csail.mit.edu/pcd); Chiesa's thesis [DSpace 1721.1/61151](https://dspace.mit.edu/handle/1721.1/61151) (rate-limited, not re-fetched); the [ICS 2010 page](https://conference.iiis.tsinghua.edu.cn/ICS2010/content/papers/25.html) may redirect to a login |
| Fiore, Nitulescu, *On the (In)security of SNARKs in the Presence of Oracles*, TCC 2016-B | the caution for D3's signing step: extraction against adversaries with an exogenous signing oracle (CGSY24 footnote 6) | [ePrint 2016/112](https://eprint.iacr.org/2016/112) (checked) |
| Barbara, Chiesa, Guan, *Relativized Succinct Arguments in the ROM Do Not Exist*, TCC 2025 (BCG24) | why the pure ROM cannot recurse; the flipping technique the D4 doc §2 transposes to knowledge | [ePrint 2024/728](https://eprint.iacr.org/2024/728) (checked) |
| Chen, Chiesa, Spooner, *On Succinct Non-Interactive Arguments in Relativized Worlds*, EUROCRYPT 2022 (CCS22) | the low-degree random oracle model; rewinding extraction only | [ePrint 2022/383](https://eprint.iacr.org/2022/383) (checked) |
| Chen, Chiesa, Gur, O'Connor, Spooner, *Proof-Carrying Data from Arithmetized Random Oracles*, EUROCRYPT 2023 (CCGOS23) | the arithmetized ROM: a non-black-box view of the oracle; why a harness cannot serve it at our domain sizes (D4 doc §3.4) | [ePrint 2023/587](https://eprint.iacr.org/2023/587) (checked) |
| Hall-Andersen, Nielsen, *On Valiant's Conjecture: Impossibility of IVC from Random Oracles*, EUROCRYPT 2023 | IVC lower bound in the ROM; what it needs (zero knowledge or freshness) | [ePrint 2022/542](https://eprint.iacr.org/2022/542) (checked) |
| Maller, Mohnblatt, Zapico, *IVC in the Open-and-sign Random Oracle Model*, ASIACRYPT 2025 | a 2025 SROM descendant; notes that the hash instantiation of its oracle is "clearly broken", O-25 in another model | [ePrint 2025/1663](https://eprint.iacr.org/2025/1663) (checked) |
| Chiesa, Guan, Yıldız, *Can AI Oversight Be Zero Knowledge?*, 2026 (CGY26) | `f̂(q) = (f(q), Sign(sk, (q, f(q))))`: signed answers from trusted hardware for oracle-aided computations | [arXiv 2610.01995](https://arxiv.org/abs/2610.01995) |
| Chen, Kalai, Xi, *How to Avoid Debate: Scalable AI Safety via Doubly-Efficient Interactive Proofs*, ICML 2026 | cited by CGY26 as bypassing BCG24 for "robust" computations; not read ([L1] §12) | [arXiv 2607.03561](https://arxiv.org/abs/2607.03561) |

**B. Secret or external oracles for Fiat–Shamir**

| Item | Why read it | Link |
|---|---|---|
| Ghosal, Kate, Mukherjee, Sarkar, Sinha, *How to Instantiate Fiat–Shamir Provably and Practically?*, 2026 | challenges from an external VRF service whose key the prover never sees; notes that a secret oracle alone kills recursion (§2.4); measured remote-call costs | [ePrint 2026/2114](https://eprint.iacr.org/2026/2114) (checked) |
| Arnon, Yogev, *Towards a White-Box Secure Fiat–Shamir Transformation* (XFS), CRYPTO 2025 | a relativized ROM in which diagonalisation attacks have analogues; does not help when the submitter writes `V` ([L1] §7) | [ePrint 2025/329](https://eprint.iacr.org/2025/329) (checked) |
| Bünz, Chen, Guan, *It Takes Two: Proofs of Work for Fiat–Shamir*, 2026 | limits of proof-of-work fixes | [ePrint 2026/2326](https://eprint.iacr.org/2026/2326) (checked) |
| Jain, Lin, Luo, Wichs, *The Pseudorandom Oracle Model and Ideal Obfuscation* (PROM), CRYPTO 2023 | another oracle service with handles | [ePrint 2022/1204](https://eprint.iacr.org/2022/1204) |

**C. CGH and Fiat–Shamir counterexamples** (most from the user's list; O-25 doc §9.2)

| Item | Link |
|---|---|
| Canetti, Goldreich, Halevi, *The Random Oracle Methodology, Revisited*, STOC 1998, JACM 2004 | [ePrint 1998/011](https://eprint.iacr.org/1998/011) (checked), [arXiv cs/0010019](https://arxiv.org/abs/cs/0010019) |
| Canetti, Goldreich, Halevi, *On the Random-Oracle Methodology as Applied to Length-Restricted Signature Schemes*, TCC 2004 | [ePrint 2003/150](https://eprint.iacr.org/2003/150) |
| Goldwasser, Kalai, *On the (In)security of the Fiat–Shamir Paradigm*, FOCS 2003 | [ePrint 2003/034](https://eprint.iacr.org/2003/034) (checked) |
| Barak, FOCS 2001, an early counterexample cited by Fenzi beside Goldwasser–Kalai and CGH | no ePrint version found (the user's list) |
| Bitansky, Dachman-Soled, Garg, Jain, Kalai, López-Alt, Wichs, *Why "Fiat–Shamir for Proofs" Lacks a Proof*, TCC 2013 | [ePrint 2012/705](https://eprint.iacr.org/2012/705) |
| Dachman-Soled, Jain, Kalai, López-Alt, *On the (In)security of the Fiat–Shamir Paradigm, Revisited* | [ePrint 2012/706](https://eprint.iacr.org/2012/706) |
| Ananth, Bhaskar, Goyal, Rao, *On the (In)security of Fischlin's Paradigm*, TCC 2013 | [ePrint 2012/721](https://eprint.iacr.org/2012/721) |
| Bartusek, Bronfman, Holmgren, Ma, Rothblum, *On the (In)security of Kilian-Based SNARGs*, TCC 2019 | [ePrint 2019/997](https://eprint.iacr.org/2019/997) (checked) |
| Khovratovich, Rothblum, Soukhanov, *How to Prove False Statements: Practical Attacks on Fiat–Shamir*, CRYPTO 2025 | [ePrint 2025/118](https://eprint.iacr.org/2025/118) (checked) |
| Brzuska, Hubáček, Kalsta, *Simple Attacks against (Extended) Fiat–Shamir*, PKC 2026 | [Springer](https://link.springer.com/chapter/10.1007/978-3-032-26731-3_17) |
| Fenzi, *How to Prove More False Statements: Fiat–Shamir Limitations on (Generated) R1CS*, 2026 | [ePrint 2026/1838](https://eprint.iacr.org/2026/1838) (checked) |
| Dao et al., weak Fiat–Shamir implementation bugs (O-25 doc §9.2) | [ePrint 2023/691](https://eprint.iacr.org/2023/691) |

**D. Provably sound Fiat–Shamir in the standard model** (correlation intractability; the user's
list; O-25 doc §9.4). Not a route for recursion.fast today, since the leaderboard's verifiers are
hash-based and agent-written, but the place to look if the oracle is ever to disappear: Kalai,
Rothblum, Rothblum 2017 ([2016/303](https://eprint.iacr.org/2016/303)); Canetti, Chen, Reyzin,
Rothblum 2018 ([2018/131](https://eprint.iacr.org/2018/131)); Canetti, Chen, Holmgren, Lombardi,
Rothblum, Rothblum 2019 ([2018/1004](https://eprint.iacr.org/2018/1004)); Peikert, Shiehian 2019
([2019/158](https://eprint.iacr.org/2019/158)); Chen, Lombardi, Ma, Quach 2021
([2020/915](https://eprint.iacr.org/2020/915)); Holmgren, Lombardi, Rothblum 2021
([2021/286](https://eprint.iacr.org/2021/286)); Jawale, Kalai, Khurana, Zhang 2021
([2020/980](https://eprint.iacr.org/2020/980)); Choudhuri, Jain, Jin 2021
([2021/808](https://eprint.iacr.org/2021/808)); Guan, Yogev 2025, Micali's SNARG in the standard
model ([2025/2328](https://eprint.iacr.org/2025/2328)).

**E. The workloads a node would verify** (hash-based arguments and accumulation; [L1] §8–§9)

Ben-Sasson, Chiesa, Spooner, *Interactive Oracle Proofs*, TCC 2016 (BCS16, the compiler behind
hash-based SNARKs; [ePrint 2016/116](https://eprint.iacr.org/2016/116), checked); Bünz, Chiesa, Lin,
Mishra, Spooner, *Proof-Carrying Data without Succinct Arguments*, CRYPTO 2021
([ePrint 2020/1618](https://eprint.iacr.org/2020/1618)); Bünz, Mishra, Nguyen, Wang, *Accumulation
without Homomorphism*, ITCS 2025 ([ePrint 2024/474](https://eprint.iacr.org/2024/474)) and *Arc:
Accumulation for Reed–Solomon Codes*, CRYPTO 2025 ([ePrint 2024/1731](https://eprint.iacr.org/2024/1731));
Bünz, Chiesa, Fenzi, Wang, *Linear-Time Accumulation Schemes* (WARP), TCC 2025
([ePrint 2025/753](https://eprint.iacr.org/2025/753)); Bünz, Rothblum, Wang, *Flock: Fast Proving for
Batch Boolean Computations* ([ePrint 2026/1329](https://eprint.iacr.org/2026/1329)). Arc, WARP and
BMNW argue PCD only heuristically ([L1] §8); D4 with CGSY24 would give their recursion a theorem
([L1] §8, estimate).

**F. Primitives and specifications**

| Item | Use here | Link |
|---|---|---|
| RFC 7693, BLAKE2 | keyed mode: key length in the parameter block (§2.5), padded key as the first block (§3.3) | [rfc7693](https://www.rfc-editor.org/rfc/rfc7693) |
| RFC 8391, XMSS | a candidate signature scheme for D3; the RFC defines SHA-2 and SHAKE parameter sets only, so a BLAKE2s instantiation is non-standard | [rfc8391](https://www.rfc-editor.org/rfc/rfc8391) |
| RFC 9381, verifiable random functions | a PRF and a proof of correct evaluation in one primitive; ECVRF is elliptic-curve based and analysed in the ROM (§4) | [rfc9381](https://www.rfc-editor.org/rfc/rfc9381) |
| Goldreich, Goldwasser, Micali, *How to Construct Random Functions*, JACM 1986 | the PRF definition the hybrid uses | (JACM 33(4)) |

---

## 11. Where to find things: a map for agents

**In this repository** (`main`):

| What | Where |
|---|---|
| the normative proposal for D4, its decisions RR-1…RR-13, costs, incentives, trust statement, build order R1–R4 | [`DESIGN-relativized-recursion.md`](DESIGN-relativized-recursion.md) §1, §4, §7–§12 |
| the O-25 record: backdoor, disguises, candidates E and T, MG1, the user's decisions, criteria | [O-25 doc](v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md) §1–§8, §11; the exploration summarised in §13 |
| v3's decisions V3-n, relation, submission, security definitions, scoring, constraints C1–C15 and design space | [v3 doc](v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md) §3.1, §4–§6, §8, §15–§17 |
| the paper behind the tree theorem | [`reference/papers/`](reference/papers/) |

**On branch `explore/relativized-nark`** (not merged; the exploration's report is at `043bcb3`, and
the branch head `1360db5` adds the D4 doc's own review and the axiom audit). Read without checking
out: `git fetch origin explore/relativized-nark && git show origin/explore/relativized-nark:<path>`.

- the brief, report and their reviews: `docs/explore/BRIEF.md`, [REPORT], `docs/explore/00-prompt-review.md`,
  [REVIEW] (the report's review), [DREVIEW] (the D4 doc's review);
- the notes: the literature [L1], the impossibility analysis [T1], the workarounds including D3 [W1],
  the attested-oracle design [W2], the cost study with measured service logs [C1], the attack notes
  [A1] [A2] [A3], and the Lean-probe notes P1–P4 (`docs/explore/notes/P*-*.md`);
- 21 untrusted Lean probe modules under `RecursionFast/Explore/`, and the 69-declaration axiom audit
  (`docs/explore/probes/audit/Audit.lean`, `audit-orchestrator.log`). To build, use a `git worktree`
  of the branch with the prebuilt package tree, then `timeout 900 lake build RecursionFastExplore`;
  the D4 doc §13.1 lists every theorem and its scope.

**On branch `v3/contract-archive`** (head `f4de3b8`): the v3 contract, `RecursionFast/Controls/Backdoor.lean`
(the kernel-certified backdoor), and `evidence/` with the O-25 probes and their logs
(`evidence/README.md` is the index).

**In the submissions repository**, https://github.com/scaraven/recursion.fast-submissions, the F2
memo `docs/snark-baseline/notes/F2-o25-uninstantiability.md` and its reviews
`docs/reviews/F2-o25-review.md`, `docs/reviews/F2-o25-review-r2.md` are **not on the remote** as of
2026-10-22: they are local commits `05aaddb`, `3facbf9`, `3723b1b`, `2a3d790` in the development VM's
checkout `/home/devops/Verified-zkEVM/recursion.fast-submissions`, whose `main` is 17 commits ahead
of `origin/main`. The O-25 doc condenses them.

**Searching.**

- ePrint full text: `https://eprint.iacr.org/search?q=<terms>`. ePrint sometimes serves a bot
  challenge to scripts; the exploration fetched PDFs through the Wayback Machine
  (`https://web.archive.org/web/2026/https://eprint.iacr.org/<year>/<num>.pdf`).
- Forward citations of the anchor papers (CGSY24, BCG24, CT10, CCGOS23, Ghosal et al.) on Semantic
  Scholar or Google Scholar are the fastest way to find newer work in this line.
- Terms that find this literature: "signed random oracle model", "relativized SNARK", "relativized
  succinct argument", "proof-carrying data" with "straightline extraction", "arithmetized random
  oracle", "low-degree random oracle", "open-and-sign random oracle", "Fiat–Shamir" with "VRF" or
  "external randomness", "correlation intractability", "random oracle uninstantiability",
  "trusted signing token" or "signature card".
- In this repository: `git grep -n -E "O-25|SROM|attest|D3|D4|CGSY24"`; the decision and finding
  identifiers (RR-n, RU-n, RO-n, O25-Mn, and the constraints C1–C15 of v3 §16, not the cost note
  [C1]) are cross-referenced across the documents.

[REPORT]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/REPORT.md
[REVIEW]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/reviews/EXPLORE-report-review.md
[DREVIEW]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/reviews/DESIGN-relativized-recursion-review.md
[L1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/L1-literature.md
[T1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/T1-impossibility.md
[W1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/W1-workarounds.md
[W2]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/W2-attested-oracle.md
[C1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/C1-cost.md
[A1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/A1-attacks-D1-D2.md
[A2]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/A2-attacks-W5.md
[A3]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/A3-attacks-D4plus.md
[m-svc]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/probes/c1-cost/svc.log
[m-svcmulti]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/probes/c1-cost/svc-multi.log

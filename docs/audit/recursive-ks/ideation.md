# Ideation: candidate cheats against the v4 certificate under recursion

Attack theorist's note for `BRIEF.md`. Read: the brief; `Contract/{Relation,Security,Certificate,
Extractor,Oracle}.lean`; design §0, §2.1–§2.4, §3.6, §4.3; `Controls/Backdoor.lean` (header).
Tags as in the brief; everything here is **estimate** or **paper** unless a kernel name is given.
The literature map, the per-link audit of §2.4 and the comb proof belong to the other agents.

## 1. Verdict on the orchestrator's reading

**T1: confirmed, with one correction and one quantitative caveat.** The reading is right that the
classic depth failures do not apply: the node clause of `Rel` is the exact, decidable predicate
`acc` on data, so there is no relaxed relation and no soundness/knowledge slack; the extractor is
the one Lean function `E` on the one final log, applied member by member, so there is no rewinding
tree and no depth-dependent extractor; its cost is a theorem (`Computes`), not a loss. Depth
enters only as the member count `N`. An escape at any member is, by `KS.select`/`Escape.wins`
(kernel), a win of the one-level game by a normalised adversary, and the certificate is for every
`vk` and every query-bounded adversary however it computes, so holding `sk`, knowing the design,
or grinding gives no advantage inside the model. The residual is exactly the paper list:
`N·(Q+qV)·ε`, PRF, EUF-CMA, trace-digest collisions, the comb walk, lazy sampling, averaging.
- *Correction.* The residual's PRF term is not "one assumption about one fixed function, the same
  for every `V`" (§2.3): the distinguisher `D` runs the walk, which runs `acc` on every member of
  the extraction tree, and the contract does not bound `V`'s running time. `D` is efficient only
  by an argument the design does not make (candidate 4 below gives it). No attack follows; the
  proof has a hole, the system does not.
- *Caveat.* The textbook accounting (V4-A10) is linear in `N`. At the brief's target it holds with
  margin `2^1.8`–`2^8.4` (candidate 5), but a design honestly at the cap is certified-secure for
  the season's depth, not for an application's depth: the cap was sized to `M`.

**T2: confirmed, and sharpened.** The certificate is blind to T2 by construction: `Rel (acc vk)`
never evaluates the oracle, so the KRS25/relativization precondition is absent from every
theorem, and the kernel already holds a certified entry that fails T2 with probability 1
(`Controls.Backdoor.backdoor`, candidate 2). The open question is incentive, and here the answer is
*yes, natural and score-rewarded*: the class the design itself names as the leader (GF(2^128)
sumcheck provers with univariate skip, FB-9, §3.6's Flock-class) is the class whose node circuit
evaluates the Fiat–Shamir hash as a gadget on prover-controlled data, the shape of the KRS25
attacks (candidate 1). Whether the attack survives a *fixed* node circuit with a committed witness
is the one decisive unknown; candidate 1's probe settles it. Note also that the T2 port is *the
same design*: in T1 the node circuit already hashes the child's whole trace (to check the
signature, §4.2), so dropping the signature and recomputing `H(q)` in-circuit changes the cost
profile little and the Fiat–Shamir inputs not at all. Nothing is re-engineered at the port, so a
T2 weakness of the T1 winner is a weakness of the T1 winner's exact transcript structure.

## 2. Ranked candidates

### C1 (T2, rank 1). Sumcheck/GKR node circuits with the FS hash as a gadget on witness data

*Mechanism.* In T2 the node circuit computes `H` on the child's transcript (queries and claimed
answers), which is witness the prover chooses freely, and the node's own challenges are `H` of
the node transcript. KRS25 shows that FS-GKR is practically insecure for circuits that evaluate
`H` on prover-influenced data: the prover places the sumcheck lie in a layer whose wires are a
function of the challenge, so the lie vanishes at the challenge. GKR-class provers commit to no
intermediate wires (only the input layer), which is why the lie is free. The binary field makes
the final step linear algebra (C3). *Link broken:* T2 property (ROM ⇒ public-hash FS for a
relation that evaluates `H`); no link of the T1 chain. *Certifiable:* yes, it is the standard
ROM proof of round-by-round sound sumcheck plus FS; `errorCap` was lowered to admit it (FB-9).
*Score:* strongly rewarded: linear-time prover, no witness commitment beyond the states, the
fastest known class for BLAKE2s compression circuits, proof size and `V` time near the knee.
*Attack probability:* ≈ 1 at polynomial cost if the KRS condition holds for a fixed circuit with
a committed input layer; if KRS needs the attacker to choose the circuit, the natural design is
safe and C1 collapses into C2 (a planted sub-circuit). *Decisive unknown:* exactly that regime.
*Probe (Python, then one-paragraph write-up).* Build the smallest FS-GKR toy: a layered circuit
over GF(2^16) (or GF(2^31−1) for contrast) of depth 3, whose input layer is (i) public, (ii)
Merkle-committed before the first challenge; the circuit's last layer evaluates a toy hash `h`
(a 2-round sponge over the field) on an input slot, and the FS challenges are `h(transcript)`.
Run the KRS construction (literature agent supplies the exact recipe) against a false output
claim in both regimes; success = acceptance rate ≥ 1/2 over 100 random trials in regime (ii)
with the circuit fixed in advance and only the input chosen by the attacker. Report (ii)'s
acceptance rate as the finding; (i) is the calibration that the implementation is right.
A second, cheaper check: list, for a concrete node circuit (the design's §4.2 shape), which
layers are functions of which FS inputs; if every `H`-gadget input is fixed by the commitment
before the first challenge it depends on, write down why KRS's lie has no layer to live in.

### C2 (T2, rank 2). The planted O-25 backdoor, ported with the design

*Mechanism.* `V` asks one fixed query and, when the answer equals the public unkeyed BLAKE2s of
that query, accepts a magic proof of every statement; otherwise it is the honest design. In T1 the
trigger is the keyed answer equalling the public one, `2^-256` per key; in T2 `H` *is* the public
function, the trigger always fires, and the node circuit (which recomputes the child's `H`) accepts
magic children, so a depth-96 chain of false statements costs zero work. *Link broken:* T2
property only. *Certifiable:* **kernel**, `Controls.Backdoor.certified`, `backdoor` (at `ε =
errorCap`, under every key). *Score:* neutral: one comparison of 32 bytes on the trace, no proof
bytes, no prover work; the branch can be folded into any leader design. *Attack probability:* 1.
*Why it matters although known:* v4 explicitly declined to forbid the recognition site (ADV-M5,
§2.2), relying on deployment; so the certificate *cannot* distinguish a winner from a winner with
a trapdoor for its own public-hash port, and nothing in the rules asks a reviewer to look.
*Probe (Lean toy, ~20 lines, `RecursionFast/Explore/BackdoorT2.lean`).* Define the T2 reading
of a verifier, `runPub (V vk c π) := (V vk c π).runSeq (its own queries answered by
blake2sDigest)`, or more simply the functional log `[(q0, blake2sDigest [])]`, and prove
`∀ vk c, Backdoor.S.acc vk c ⟨magic c, [(q0, trigger)], σ⟩ = true` is already `backdoor`; add
`∀ vk c, (Backdoor.V vk c (magic c)).runLog [(q0, blake2sDigest q0.toList)] = some true` and a
node lemma: the node clause of `Rel (S.acc vk)` holds for `nodeStmt c₁ c₂` with two magic children
on that trace. Success = both theorems with the standard axioms. This settles that a kernel
certificate and a kernel T2 break coexist, which moves the T2 question from theory to policy.

### C3 (T2, rank 3). Binary-field amplifier: witness bits make the final step GF(2)-linear

*Mechanism.* Over GF(2^128) with bit-valued witness slots (hash states), "choose the slots so the
multilinear extension at the challenge `r` equals a target `v`" is `Σ y_i·eq(r,i) = v` with `y_i ∈
{0,1}`, i.e. 128 GF(2)-linear equations in `#slots` unknowns: 256 slots give a solution with
probability ≈ 1 by Gaussian elimination. Over a prime field the same step is a 256-element
modular subset sum. So any T2 attack that makes a challenge predictable (C1) finishes in
microseconds in the binary-field class and needs lattice work in the prime-field class. In the
ROM the certificate's *adaptive* game (the adversary chooses `c` after its queries) shows why this
is harmless there: an unpredictable `r` leaves nothing to solve for; a weak-FS design (challenges
not binding `c`) would be caught by that game, since the adversary would pick `y` after `r` and
output `c = leafStmt y n` with no extractable start. *Certifiable:* the field choice is admitted
(FB-9). *Score:* rewarded (the leader class is binary). *Probability:* an amplifier, not an
attack. *Probe (calculation, 30 lines of Python).* For `k = 128`, slots `n ∈ {128, 160, 256}`,
random `r`, random target: solve over GF(2); report the solvability rate (expect `1 − 2^-(n−k)`).
Cite it beside C1's result so the report can say what the port's break costs end to end.

### C4 (T1, rank 4; expected negative). Unbounded verifier branches and the PRF hybrid

*Mechanism.* The contract bounds `E`'s steps, not `V`'s. A certified `V` may carry a branch that
is infeasible to run (for instance: accept a magic leaf when the proof names a key `k` consistent
with two trace entries; a union bound over the `2^256` keys gives `2^-256` over the two uniform
answers, so it is certifiable in the kernel without any BLAKE2s regularity fact, and it compiles
as a bounded search). Then the hybrid's `D` (§2.3), which runs `acc` on every member of the
extraction tree, is not efficient and `Adv^PRF(D)` is unbounded by the assumption. *Link
broken:* link 3's PRF step, as written. *Certifiable:* yes. *Score:* neutral. *Attack
probability in T1:* 0, by this argument, which the design should adopt: every member of the
extraction tree other than the root is a child the node prover proved `acc` for in-circuit, so any
`V`-branch the prover can trigger in a child is one the prover itself executed (a circuit may
under-approximate `acc`, never over-approximate it, or the node is uncertifiable); the root is run
by the harness within its cap. Hence `D`'s cost ≤ prover's cost + harness's cost + `E`'s budget,
about `2^58` steps as §2.4 estimates, independent of `V`'s worst case. *Probe (calculation /
text).* Verify the under-approximation claim against `Library/Compose.lean`'s walk: the walk runs
`acc` on the *extracted* children (`E`'s output), which are exactly the children the node proof
committed to, so their `acc` computation is the one the circuit encoded. If the walk ever runs
`acc` on a member that no prover proved (it should not), the argument fails and C4 becomes a
documentation finding with teeth. Outcome either way: a one-paragraph patch to §2.3.

### C5 (T1, rank 5; a number, not an exploit). Linear-in-`N` accounting at the cap

*Mechanism.* A design honestly at the cap (`ε = 2^-120`, e.g. a univariate-skip round at
`126/2^128 ≈ 2^-121`) is certified, score-rewarded (the cheapest field and round count), and its
composed error is the union bound, which is tight when member escapes are distinct events.
*Calculation (estimate; re-prove in Lean as a `Real` inequality if quoted).* At `Q = 2^64`, `qV =
2^16`: final output, `N = 2M+1 = 193 = 2^7.6`: `2^-48.4`; every output, `N = M²+2M = 9,408 =
2^13.2`: `2^-42.8`; with the signer's re-evaluation doubling `Q`: `2^-47.4` and `2^-41.8`. All
under `2^-40`: **no cheat at the brief's target.** But at the same budget, an IVC application of
`2^20` steps has every-output error `2^20·2^64·2^-120 = 2^-36`, above the target, and `2^-28` with
the lossy factor of a `2^28`-member tree. The potential route (`KState.ks`, library) is lossless
(`(Q+qV)·ε` for the whole tree) but is not what the certificate states (V4-A10). *Link broken:*
none; the chain is sound, its constant is sized to the season. *Probe (Lean, 15 lines,
`Explore/UnionMargin.lean`).* Prove `(9408 : ℝ) * (2^65 + 2^16) * (2:ℝ)⁻¹^120 ≤ (2:ℝ)⁻¹^40` and
`¬ ((2^20 : ℝ) * 2^64 * (2:ℝ)⁻¹^120 ≤ (2:ℝ)⁻¹^40)` by `norm_num`; quote both as **kernel**.
Recommendation for the report: state the target's depth in the record, or make a potential-based
(lossless) certificate an optional stronger claim that a record may carry.

### C6 (T1; rejected on analysis, recorded so no one re-derives it)

Weak Fiat–Shamir (challenges not binding `c`): uncertifiable, the game is adaptive (C3). A node
circuit that skips the child's signature or trace exactness: uncertifiable, `Rel` demands `acc`
and the unbounded adversary supplies the missing conjunct. Committing the witness by one `1 MiB`
query to avoid decoding: `V` must form the query from `π`, so the bytes are in `π` and priced.
Replaying one signed child in many nodes, cross-step trace reuse, degenerate `vk`: all inside the
model, all covered by `∀ vk` and single-output `KS` with `KS.select`. Grinding to `δ = 2^-40`:
completeness only. Signature-count exhaustion, index reuse, service bugs: runtime, out of scope.

## 3. The strongest argument that no T1 cheat exists

Let `A` be the whole run (the entrant's prover, the signer, the harness) with final log `L` and an
accepted output at depth 96. By the walk, "extraction fails" ⊆ "some member escapes" ∪ "forgery" ∪
"collision" (kernel for balanced trees; comb in progress). A member escape means `acc vk c p` with
`p`'s trace genuine, hence `(V vk c π).runLog L = some true` (`runLog_of_runSeq`, kernel), while
`E c π L` yields no witness of `Rel (acc vk)`. Because `Rel`'s node clause is `acc` itself,
"witness" is a decidable fact about data, so the escape is literally the event of `KS`'s game for
the adversary `A` followed by selecting that member (`KS.select`, `Escape.wins`, kernel): no
relaxation, no rewinding, no extractor that grows with depth, no dependence on which member or on
how `A` computed. The certificate bounds it by `(Q+qV)·ε` for *every* query-bounded adversary and
*every* `vk`, so the attacker's freedoms (its own `V`, `P`, `sk`, unbounded computation) are already
quantified over. Depth contributes the factor `N` and nothing else; at `M = 96`, `Q = 2^65`, the
total is below `2^-41.8` (C5). Forgery and collision are reductions to public BLAKE2s at `2^128+`
work, not oracle queries; the PRF step costs one advantage against an efficient `D` (C4's argument
makes `D` efficient). Hence no certified, score-rewarded design is T1-insecure at the target.

*Weakest assumption, named:* **keyed BLAKE2s is a PRF against the non-uniform distinguisher the
entrant designs**, i.e. `D` is built from the entrant's own `V`, `P` and `E`, chosen with full
knowledge of BLAKE2s, and the assumption must hold for that correlated family, not for a generic
one. It is still an ordinary PRF assumption (against `≈ 2^58`-step non-uniform adversaries), but
it is the one place where the attacker's design choice and the hardness assumption meet; the
backdoor control shows the model cannot see a `V` that embeds any advice about the function. Second
weakest: the comb walk (paper until the Lean agent closes it); third: that the service's `SIGN`
re-evaluation makes every signed trace a sub-log of `L` with the oracle's answers (runtime).

## 4. For the orchestrator

- Order of execution: C2's Lean toy (cheap, decisive, kernel) and C5's inequalities first; C1's
  Python toy is the one probe whose outcome changes the report's headline; C3 is a 30-line
  appendix to C1; C4 is a text patch to §2.3 once the walk's `acc` sites are checked.
- If C1 comes out positive, the report's T2 statement should be: the score selects the one design
  class with a known practical public-hash recursion attack, and the certificate cannot see it; if
  negative, T2 fragility needs a planted sub-circuit (C2), which the rules do not ask anyone to
  look for.

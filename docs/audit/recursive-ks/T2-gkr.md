# T2: is an honest GKR/sumcheck entry exposed to KRS-style attacks under public-hash recursion?

Auditor: T2 (ideation C1, C3). Sources: KRS25 (`krs.txt`, CRYPTO 2025), Fenzi26 (`krs-r1cs.txt`),
`literature.md` §§3–4, `ideation.md` C1–C3, `Contract/Relation.lean`. Script and log:
`logs/audit/T2-gkr-c3.py`, `logs/audit/T2-gkr-c3.log`.

## Verdict

**Not exposed to any known attack, provided the circuit is honest; the T2 risk that remains is a
planted circuit.** Confidence: high that the published mechanisms (KRS Thms 1, 2, 9, 10;
Fenzi26 Thm 2) do not apply to an honest v4-shaped node; moderate that the class is secure, which
is open, as KRS §5 says of every protocol it does not break. KRS needs a circuit wire that equals
an outer challenge *by construction*. In a certified design the outer Fiat–Shamir prefix binds the
node's input commitment `comm(w)` and its statement `c` (T2-2). An honest node evaluates `H` only on
its children's transcripts and on statement encodings. So a wire equals an outer challenge only if
(i) a child's statement equals the parent's, `c₁ = nodeStmt c₁ c₂`, which is a BLAKE2s fixed point,
and (ii) the input layer contains its own commitment, a second fixed point. Barrier (ii) has a soft
spot (T2-4a); barrier (i) holds on its own. Without a fixed point, only the chance event
"challenge = wire value" is left. It costs `2^k` per hit for `k`-bit challenges, gets no birthday
speed-up, and the ROM bound `Q·ε` already counts it. KRS Thm 2 shows the planted variant is
certifiable and cheap: `C*` is functionally equivalent to `C` and adds `O(d_h log ℓ)` depth. That
is ideation C2 in GKR form. Because the certificate cannot tell it apart (BCG; `literature.md`
§3), T2 safety rests on **reviewing the circuit, not on the certificate**. **Weakest step:** the
honesty assumption itself, i.e. that every in-circuit `H` input is a child prefix in the child's
own slots, or a domain-separated `nodeStmt`, `leafStmt` or chain input. Nothing in v4 checks this,
and T2-5 lists the circuit patterns that would break it.

## T2-1. KRS25: the mechanism and the role of circuit choice (**paper**)

- *Protocol.* `FS_h(Π_comm,d)`: GKR plus a multilinear PCS. `x` and `y` are sent in the clear,
  only `w` is committed, and the first challenge is `r = h(⟨C⟩, comm(w), x, y)` (§1.1.1).
- *Where the lie sits.* It sits in the output-layer claim, or in Thm 2 in the claim about an
  intermediate layer `u`. The circuit makes that layer a function of a wire `γ` that equals the
  challenge used to reduce it. Thm 1: `C*(w) = (γ, γ−1)` with `γ = h(ψ, y*, comm(w))` and
  `ψ = w = ⟨C*⟩`, so `ŷ(r) = γ − r = 0 = ŷ*(r)`. The doomed claim becomes true at `r`, and the rest
  of the proof is the honest prover's. Thm 2 (Prop. 7): `û_real(r′) − û_fake(r′)` factors through
  `γ − r′₁`. Here `g` recomputes in-circuit the GKR transcript of the `IF-THEN-ELSE` sub-circuit,
  which is how it learns the later challenge `r′`.
- *Why uncommitted layers make it free.* `γ` and `u` are intermediate wires. They are never
  committed, so their values are not fixed before `r` is drawn (§5, the "key property"). The
  circular dependency, where changing the circuit changes `r`, is broken in two places. The digest
  arrives as witness (`ψ = w`). The circuit **computes `comm(w)` itself** from a tiny witness. Both
  are needed for `γ = r`.
- *Circuit choice.* Thm 1 and Thm 2 break *adaptive* soundness: the attacker outputs `C*` knowing
  `h` and `comm` (Def. 6). Thm 2 shows the circuit's *implementation* matters, not its function.
  Thm 9 removes the choice of circuit by using a fixed universal-TM circuit whose witness is a quine
  computing the circuit's own first challenge. Thm 10 does the same with a universal GKR circuit
  whose commitment splits additively, or into batched Merkle roots, so `comm(w_C)` can sit inside
  `w_in`. In every theorem the circuit, chosen or universal, runs attacker-supplied code that
  computes `comm` and `h` of its own input. Expander was attacked through this circuit-choice
  attack. Polyhedra then mitigated "along the lines of §5" (fn. 4); we did not read PR #184.
- *Public input.* `x` is hashed into `r`, so it adds nothing to Thm 1. It is not needed there and is
  set to `x*` in Thm 2. Remark 3: canonical simple circuits, such as grand products and lookups,
  seem immune.
- *Fenzi26* needs "generated" statements, where FS hashes the program that generates the R1CS
  rather than the R1CS itself. In v4, `vk` and the circuit are fixed and `c` is hashed, so there is
  no delayed choice of statement. Prop. 5.5 is the standard binding. Not applicable to an honest
  entry.

## T2-2. Model of the recursion node, and what certification forces (**estimate**, from C3)

- *Input layer:* `w ⊇ (π₁, π₂, child traces)`, committed as `comm(w)`. The public statement is
  `c = nodeStmt c₁ c₂ = BLAKE2s(tagNode ‖ c₁ ‖ c₂)` (`Relation.lean` l. 95, 133). The outer
  challenges are `r_j = H(P_j)`, where `P_j` is the transcript prefix.
- *In-circuit `H` calls (honest):* the child prefixes `s = (⟨C⟩, comm_{cᵢ}, cᵢ, …)` and their
  extensions by the child's round messages; `nodeStmt` and `leafStmt` inputs; and the chain's
  32-byte compressions in leaves.
- *Certification forces binding.* If `P_j` omits `comm(w)`, the ROM adversary picks `w` after `r`.
  The final claim `ŵ(z) = v` is then one linear equation, which C3 solves with probability ≈ 1
  (T2-6). If `P_j` omits the output `y` or `c`, the adversary picks `y* ≠ y` with
  `ŷ*(r) = ŷ(r)`: the same linear system over the 257 output bits. Either is a win of the adaptive
  KS game with no extractable witness, so no certificate exists (ideation C3). So in a certified
  entry every outer challenge binds `comm(w)` and `c`. This leans on the certificate meaning ROM
  knowledge soundness, up to the documented gaps (`lucky_ks` and others).
- *Generic vs structural.* Suppose the circuit evaluates `H(s)` with `s ≠ P_j`. Then
  `trunc_k H(s) = r_j` is a chance event of probability `2^-k` per trial. Trials are coupled: `s`
  and `P_j` come from the same `w`, so there is no birthday. Cheap grinding of later round messages
  hits any of `T` in-circuit values with probability `T·2^-k` per hash. This is exactly the
  round-by-round bad event that the ROM bound `Q·ε` prices (`k ≥ 120` at `errorCap`). So a
  KRS-type break needs `s = P_j`.

## T2-3. Route (a): child-transcript bytes = outer prefix

- To get `s = P_j`, the child's statement slot must hold `c`. That slot holds the child's statement
  `c₁`, so `c₁ = nodeStmt c₁ c₂`, or symmetrically `c₂ = c`: a **BLAKE2s fixed point**, generic cost
  `2^256`, or `2^k` on the challenge bits (T2-2).
- The same holds for leaves (`c₁ = leafStmt …`) and for any descendant, because `c` hashes every
  statement below it.
- Independently, the commitment slot must hold `comm(w)` while `w ⊇ π₁ ∋ comm_{c₁}`. That is a
  **fixed point of `comm`**, which for a Merkle commitment is again a BLAKE2s fixed point.
- **Blocked by two independent fixed points.** **estimate**.

## T2-4. Route (b): the commitment covers only part of the input

- *Unbound part.* If part of the input is neither committed nor hashed, it is chosen after `r`.
  This is a ROM break by C3, and the design cannot be certified.
- *Batched roots,* `P = (⟨C⟩, root_A, root_B, c, y)` (KRS Thm 10's lever). Part B may contain
  `root_A`. The child slot then still needs `root_B`, the root over the part that holds it, and `c`.
  **Blocked** by the same fixed points.
- *(4a) Soft spot in barrier (ii).* An honest node *does* compute Merkle roots: it recomputes the
  child's root from opened leaves and siblings. Suppose a design wires the recomputed root into the
  child-prefix `H`, rather than the stored `comm_{c₁}` it compares the root with. A single path, or
  a batched multiproof, can then recompute `comm(w)` with no fixed point, if every sibling value is
  stored in a later off-path subtree or in the opened leaf, which is an acyclic arrangement.
  Independent paths that diverge force a cycle. But the arrangement depends on the query positions,
  and those are derived from challenges that bind `comm(w)`. So the attacker must guess positions
  carrying `≥ λ` bits of entropy, **estimate** `≥ 2^λ` trials. Barrier (i) holds regardless.
  **Blocked for v4's `Rel`.** For a relation in which a parent may restate a child's statement,
  this sub-case is the open one.

## T2-5. Routes (c), (d), (e)

- **(c) Weak FS,** where the challenges omit `comm(w)`, `c` or `y`: ROM-broken by one Gaussian
  elimination (T2-2, T2-6), so not certifiable. Exposure would require the certificate itself to be
  wrong. **Blocked by certification.**
- **(d) Public-input layers.** `x` is chosen after `comm(w)`, so `x` *may* contain `comm(w)` with no
  fixed point. But `P` binds `x` too, and the child slot reads the child's public input `x₁`.
  `x₁ = x` forces `c₁ = c`, the barrier (i) fixed point, or `x ⊋ x₁ = x` if child proofs are public.
  Cross-type coincidences fail the same way. `nodeStmt` on `(comm(w), c)` needs
  `c = nodeStmt(comm(w), c)`, a fixed point. A 32-byte chain input differs from any FS prefix of 64
  bytes or more through BLAKE2s's length counter and final flag, unless the design's transcript
  state is itself 32 bytes and fed to a leaf chain: then `h ∈ w → c → P → h`, a fixed point.
  **Blocked**, given BLAKE2s domain separation by length and tag. **estimate**.
- **(e) Composition and reuse of child challenges.** The child challenges the node computes are
  bound to child data inside `w`. If the outer protocol reuses them, or derives outer challenges
  from child digests without `comm(w)` and `c`, they are known before the rest of `w` is chosen,
  which is case (c). Two-phase commitments (`w₂` committed after `r₁`, as in lookup multiplicities)
  let `w₂` contain `r₁`. But claims about layers that depend on `w₂` are reduced with challenges
  binding `comm(w₂)`, so knowing `r₁` gains nothing. Reducing them with `r₁` is again a ROM break.
  KRS's lie below the output (Thm 2) needs the circuit to know later challenges. Those bind the
  outer round messages, which are not in `w`, so this is again route (a). **Blocked.**
- **Circuit patterns that would void the verdict:**
  - `H` gadgets whose input slots are filled from the parent's own statement or public input, i.e.
    the circuit computes its own FS prefix;
  - recomputed roots wired into `H`, together with a relation that allows `c₁ = c` (4a);
  - universal or VM circuits that run witness-supplied code (Thms 9 and 10);
  - transcript formats that are not domain-separated from `nodeStmt`, `leafStmt` and chain inputs;
  - any sub-circuit functionally redundant with `C` (Thm 2's `IF-THEN-ELSE` on a computed `γ`).

  Each is a reviewable property of the circuit. None is a property the certificate can see.

## T2-6. C3: binary-field amplifier (**measured**; exact rate is a calculation, **estimate** until re-proved)

The system `Σᵢ yᵢ·eq(r, i) = v` over GF(2^128), with the GHASH modulus, a random known challenge `r`
in `m = ⌈log₂ n⌉` variables, a random target `v`, and `n` free bits (the other hypercube points are
fixed to 0). It is 128 GF(2)-linear equations in `n` unknowns. Every solution was checked against
the multilinear extension. Seed 1, 1,000 trials per `n`:

| n   | measured solvable | exact (random 128×n GF(2) matrix) | Python time per instance |
|-----|-------------------|-----------------------------------|--------------------------|
| 128 | 0.616             | 0.6103                            | 9.1 ms                   |
| 160 | 1.000             | 1 − 1.16·10⁻¹⁰ (≈ 1 − 2⁻³³)       | 18.0 ms                  |
| 256 | 1.000             | 1 − 2⁻¹²⁹ (prints 1.0)            | 19.2 ms                  |

Words packed into GF(2^32) subfields are GF(2)-subspaces, so the system stays linear. Over a prime
field with bit-constrained slots, the same step is a modular subset sum (**estimate**). **Reading:**
in the GF(2^128) class, any route that makes a challenge predictable before the input claim is
fixed finishes in one elimination. That is why the weak-FS variants (b), (c) and (e) are
ROM-broken, and so not certifiable. For a certified honest entry the amplifier has nothing to
amplify, because no route of T2-3 to T2-5 yields a predictable challenge without a fixed point.

## T2-7. Not done, and what is open

- *The Python toy (C1 probe).* Not built: the analysis decides the question. In the committed
  regime the toy would only re-measure the `2^-k` chance event, and the uncommitted regime is the
  KRS theorem itself.
- *Open:*
  - non-diagonalisation Fiat–Shamir attacks on GKR plus BLAKE2s (KRS §5; CGSY §2.3's excluded
    class);
  - relations other than v4's `Rel` that allow `c₁ = c`, where barrier (i) is absent (T2-4a);
  - concrete BLAKE2s fixed points or collisions (T3).
- *For the orchestrator:*
  - T2 for honest entries reduces to auditing the circuit against the list in T2-5;
  - the planted `C*` (Thm 2) and ideation C2 are the realistic T2 threat: certifiable, cheap in the
    score, and invisible to functional tests.

# Adversarial review of SYNTHESIS.md (cryptographic reasoning and conclusions)

Scope: the reasoning behind C-1…C-5 and whether they answer the user's question (a certified,
well-scoring entry that is insecure "if we deploy these tricks in real life"). Lean fidelity is the
other reviewer's. Sources read: BRIEF, SYNTHESIS, all evidence files, `Explore/StreamBound.lean`,
`Explore/T2Backdoor.lean`, `Contract/*`, `Controls/Backdoor.lean`, `Library/Compose.lean` (defs),
design §2.3, §2.4, §2.7, §2.8, §3.6, §4.3, `service/PROTOCOL.md`, `service/src/main.rs` 120–200.

## Major

**1. C-1's quantitative target is wrong for the deployment and contradicts C-3(c).** C-1 says the
brief's target "2^-40 at 2^64 queries, depth 96" is "met with margin (2^-55)". That is the ROM term
only. The ROM→deployment step runs `E` (through `ext`) on every comb member, and `Computes` binds
`ext` only on tapes of ≤ 2^64 words, about 2^61 entries (or 2^47 maximal queries). At `Q = 2^64` the
tape is outside the domain, `E` is unconstrained there, and seams-T1 Finding 1's `E_bad` (honest
inside the domain, "`none` if the log is keyed-BLAKE2s-consistent under some key" outside) is
certified yet fails on every deployed log with probability 1. The PRF, EUF-CMA and collision
reductions cannot run either, since they run `E`. So at the brief's literal target the deployment
bound is not `2^-55`; it is unproved, with a certified counterexample. The synthesis demoted this
from "major" (seams-T1) to a "design document correction" (C-3c). **Fix:** state C-1's bound within
the domain: "for runs whose log stays within the extractor domain (≤ 2^61 entries, ≤ 2^47 maximal
queries; T1 is at 2^28–2^30, estimate), the deployed failure probability is at most
`(Q+qV)·ε + Adv^PRF + Adv^EUF-CMA + Adv^coll ≤ 2^-58 + …`; at `Q = 2^64` only the ROM term `2^-55`
holds and the knowledge claim degrades to soundness against extractors blind to the key." Keep the
sentence that the domain is physically unreachable in a 1,920 s run, tagged estimate.

**2. "Inert in T1" and C-5's diagnosis miss the nearest real-world failure: an SROM deployment
whose key outlives the freezing of the verifier.** The whole PRF hybrid (§2.3) needs `V`, `P`, `E`
fixed before `k` is drawn, and `k` fresh per lifetime. v4 enforces this (fresh service per stream,
entry frozen at submission). Every realistic analogue the user would "deploy in real life" (a TEE
or signing service with a long-lived key, several applications or verifiers registered over time,
a key shared across runs) does not. Against such a service the certified O-25 backdoor needs no
port: the attacker asks one `QUERY` for `q0`, sets `trigger := PRF_k(q0)` (the observed constant),
and submits; the certificate is the same proof (`2^-256` over random oracles), and under that key
the magic branch fires on every statement at every depth. The reduction cannot even be stated,
since `D` would depend on the challenge. An extractor-side variant exists too: honest `V` and `P`,
and an `E` that returns `none` when the log contains the observed pair, is certified and voids the
knowledge claim of an otherwise honest entry under that key. Nothing in the audit says this; the
condition appears only as a §2.3 bullet. **Fix:** C-4's "inert in T1" must read "inert under v4's
key discipline: `k` drawn after `V` is frozen, fresh per lifetime, never serving a verifier chosen
after any query to it". C-5 must list a third deployment, T1′ = SROM with key reuse or late
verifier registration, and rule: the same certified entries are broken there at zero cost; the
record (RU-5) should state the condition as part of what it certifies. This is the cheapest and
most realistic "cheat that passes the certificate and is insecure in real life", and it is
reachable without leaving the SROM.

## Minor

**3. "Independent of depth and of the number of members" holds for the oracle term only.** The
V-free distinguisher `D` and the forger `B` run the E-only walk on every output: `M²+2M = 9,408`
`E` calls, each within `B(t)` on the whole log, about `2^48`–`2^49` steps per call with short
queries (`2^62` in total) and up to about `2^63` per call with `2^20`-byte queries (`2^76`). The
advantage terms are therefore for distinguishers of that size; harmless against keyed BLAKE2s
(generic `T/2^256`) but not depth-free. **Fix:** "the oracle term is depth-free; the reductions'
running time is linear in the number of members and stays far below any bound the PRF or EUF-CMA
assumption cares about (estimate)".

**4. The deployment's "extraction fails" is not defined, and the only step joining kernel to
deployment is unwritten.** `stream_bad_prob` bounds a V-free event; the deployment needs
"E-only comb walk returns neither starts nor an explicit collision nor a forgery ⊆ that event ∪
forgery ∪ collision". stream-bound.md says this in prose ("paper, mechanical; not in Lean"). Note
also that the kernel `combWalk` (with `Rel (S.acc vk)`) can report an *escape* where the E-only
walk returns starts (children structurally fine but `acc`-rejected, opening to good leaves), so the
two walks differ and the deployment must use the E-only one. And `D`'s root check is the harness's
capped compiled `acc`, which implies the mathematical `acc` (trust item 5), the right direction.
**Fix:** define extraction in C-1 as the E-only comb walk, name the containment as the single paper
step that carries the kernel bound into the deployment, and say which direction the harness's
timeout cuts.

**5. Knowledge in the deployment is existential.** The service keeps no table (V4-A5), the harness
keeps no query log (removed with V4-A9), and `ext` is never run. After a run nobody holds `L`, so
nobody can run `E`; the record guarantees "a witness exists, and an efficient-in-principle extractor
would find it from a log that was not kept". For the user's purpose (no false statements) this is
enough; C-1 should say "soundness with a certified extractor" rather than imply extractability by
the organiser or a third party.

**6. "Proves a false chain statement" is covered but the evidence should be named correctly.** The
harness never poses a false statement (every leaf is drawn from its start), so no benchmark column
tests this criterion; the canaries are mutations, not false statements. What covers it is
`escape_any_le`'s quantification over every `c`: an accepted proof of a `leafStmt h n` without a
chain preimage would be an escape. Say so in C-1; do not cite the canaries.

**7. C-2 stands.** One addition: the depth-freeness also depends on `E` being one fixed function of
the log for every member (no per-member extractor, no auxiliary input), which is what lets CGSY's
first-failing-vertex selector be a single `KS.select`.

**8. C-4's honest-GKR verdict is defensible but overstated as "not exposed".** (a) The class has no
proof and can have none in the ROM (BCG25): T2 safety is CGSY §2.3's heuristic, so the right
phrase is "no published mechanism applies; open, as KRS §5 says". (b) The premise, that every
in-circuit `H` input is a child prefix or a tagged statement encoding, is checked by nothing in the
rules. (c) A port-time hazard the T1 analysis hides: the T2 oracle is untagged (`Hpub q =
BLAKE2s(q)`), so `Hpub (tagLeaf ‖ h ‖ enc64 n) = leafStmt h n` and likewise for `nodeStmt` and
`chainStep`; in T1 the keyed oracle separated the Fiat–Shamir domain from the relation's seven
tagged domains for free, in T2 the port must add its own separation. T2-5(d)'s "blocked, given
domain separation" assumes the port does. **Fix:** reword the bullet and add (c) to the list of
port-time obligations.

**9. The incentive reading needs sharpening, not reversal.** Agreed that optimisation does not
produce the backdoor: it moves no scored quantity, and no test rewards it (keyed answers are fresh
each run, so a hard-coded constant passes nothing). Agreed that the work-sharing route (child
transcript hash vs. the node's own Fiat–Shamir) gives no KRS lever: the node's own challenges are
never in-circuit, and transcript continuation across levels still needs a fixed point. But the
operative fact for autoresearch is "free and invisible": no scored quantity, no certificate clause,
no functional test and no reviewer sees it, and the repository ships a certified template
(`Controls/Backdoor.lean`). And the score favours the GF(2^128) class in which, should any route
make a challenge predictable, the finish is one Gaussian elimination (T2-6), so it selects the
class with the least T2 margin. **Fix:** replace "neither rewards nor penalises" with "costs
nothing and is detected by nothing; the favoured class has no T2 margin if any route opens".

**10. Service modelling is right; two residuals to state.** `SIGN` re-evaluation, query counting,
per-lifetime keys and the forgery/collision split are modelled correctly (seams L7, L8, L15, L16).
Residuals: the ROM bound's `Q` is "for every oracle function", which the deployment meets only
through the time cap and measured throughput (estimate); and the service computes on the prover's
CPUs (PROTOCOL §1), so the model's perfectly hidden `k` is, in deployment, a constant-time
assumption on BLAKE2s (out of the brief's scope, but it belongs in the deployment conditions of
finding 2).

**11. C-3 stands;** promote (c) into C-1 per finding 1. In (b), add that the harness's root check
is the one place `V` still runs inside `D`, under the harness's own cap.

## Verdict

- **C-1: stands with changes.** The T1 ruling is right for v4 as deployed and within the extractor
  domain; the target sentence at `Q = 2^64` must go (finding 1), with findings 3–6 as wording.
- **C-2: stands** (finding 7 optional).
- **C-3: stands;** fold (c) into C-1.
- **C-4: stands with changes.** The backdoor and GKR findings hold; "inert in T1" needs the key
  discipline spelled out (finding 2), the GKR bullet needs "open, heuristic, port-time domain
  separation" (finding 8), and the incentive sentence needs finding 9.
- **C-5: stands with changes.** The ruling "stay with the rules for what they certify" is right,
  but the diagnosis must name T1′ (SROM with key reuse or late verifier registration) as a gap
  nearer than T2, closable by a stated deployment condition rather than by any certificate
  (finding 2). The answer to the user is then: in v4 as run, no; in any real-life SROM that drops
  the key discipline, yes at zero cost; in public-hash recursion, yes by a planted circuit.

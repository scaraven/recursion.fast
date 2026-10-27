# recursion.fast v4: the signed-random-oracle (SROM) rules

**Status.** The normative design of v4 (2026-10-22, updated 2026-10-23 after stages A and B, their
reviews RA, RB, GA, GB and the contract fix pass, 2026-10-26 by the trim V4-A9, and 2026-10-27 by
V4-A10, textbook knowledge soundness), implemented on the branch `v4/srom-rules`: the Lean contract
under `RecursionFast/Contract/` (stage A) and the oracle service, runner and CI workflows (stage B).
It is a proposal: the user was away while it was built, and every decision taken without them is
listed in §6, each reversible; V4-A9 and V4-A10 are the user's own. It supersedes the working brief
[`v4/BRIEF.md`](v4/BRIEF.md) (decisions V4-1 … V4-16, amendments V4-A1 … A10) where the two differ,
and answers the adversarial review [`v4/reviews/C-design-attack.md`](v4/reviews/C-design-attack.md)
(findings C-M1 … M4, C-m1 … m13). Where this document and the Lean text differ, the Lean text is the
rule and the difference is a bug here.

**Inherits from** the v3 record and the proposals that followed it: the v3 design [V3], the O-25
record [O25], the CGH guide [CGH], the attested-oracle proposal D4 [RD] and the cost model [CM]
(§7 has the links). Their ids (V3-n, O-n, RR-n, RU-n, CM-n, C1–C15) are kept.

**Evidence tags.** **kernel**: a Lean theorem on `propext`, `Classical.choice`, `Quot.sound` only,
named. **paper**: an argument, here or cited. **measured**: a number with its log under `logs/`.
**estimate**: arithmetic from measured or published inputs. An untagged sentence is explanation.

**Reading paths.** Everyone: §0. Cryptographers: §1, §2. zkVM engineers: §1.3, §3, §4.
Formal-verification readers: §1, §2.4, §5. The user: §0 and §6, and the checks against
the record (C1–C15, the O-25 criteria, the earlier proposals' decisions) in
[`v4/CHECKS.md`](v4/CHECKS.md).

---

## 0. Summary

**The competition.** As in v3, agents submit a hash-based non-interactive argument for one relation
over 32-byte digests (a leaf commits to a BLAKE2s chain from a secret start, a node to two accepted
children): Lean query programs `V` and `P`, an extractor program, and a kernel-checked certificate
of knowledge soundness (the textbook single-output notion, V4-A10) and completeness in the
random-oracle model. An x86-64 assembly prover is
timed on GitHub-hosted runners, proving a tree of chains and extending a running proof chain by
chain: `S = T_tree + K·t_link`.

**The SROM.** Per timed run, a service draws a secret PRF key `k` and an independent signing key
pair `(sk, vk)`. It answers each query with `PRF_k(q)` (keyed BLAKE2s-256) and, on request, signs the
digest of a sequence of query–answer pairs (a *trace*) with a contract-fixed hash-based signature.
A proof travels as a **signed proof** `(π, tr, σ)`, accepted for `c` when `V vk c π`, reading its
answers in order from `tr`, accepts and `σ` signs `tr` under `vk`. That predicate, `acc`, never
evaluates the oracle: it is the relation's node clause, the harness's check of every proof, and
anyone's check later with the published `vk`. A node circuit checks its children by hashing their
traces and checking one signature each, never with the key (CT10's signed random oracle, as
CGSY24 §2.2 reads it).

**Why it closes O-25.** v3's certified backdoor computes the public oracle and accepts a magic
proof when an answer matches. Under a key drawn after `V` is frozen, no value about the deployed
oracle exists for `V` to compare with: recognising `PRF_k` would distinguish it from a random
function, so the certificate's bound carries over to the deployment up to one PRF advantage
(**paper**, §2.3). The backdoor stays certified in the model (**kernel**, `Backdoor.backdoor`) and
never fires.

**No certified verifier can trust a signature.** The certificate holds for every `vk` against an
unbounded adversary, who can sign anything, so a `V` that accepts a false statement because of a
signature is not knowledge-sound below `errorCap`: the adversary holding `sk` wins with
probability `1` (**paper**, §2.2; **kernel** controls `sigTrust_ks_extracts`,
`sigTrust_no_certificate`). Only the contract's `acc` trusts signatures, and unforgeability is used
once, outside every certificate, to compose the tree. Nothing is left for a reviewer to forbid.

**The tree.** On the run's one query log, signed traces are genuine unless a signature was forged,
so the one-level extractor applies member after member down to the leaves (CGSY24 Thm 5.1). Each
member's extraction fails with probability at most `(Q + qV)·ε` by the certificate itself, and a
union bound over the `N` members of the extraction tree gives `N·(Q + qV)·ε`: the walk and the
union bound are kernel (`Compose.walk`, `Compose.compose_prob`); the PRF hybrid and the
forgery/collision split are paper (§2.4). Error `N·(Q + qV)·ε + Adv_PRF + Adv_EUF-CMA + Adv_coll`,
the first term about `2^-81` for the stream's final output (`N = 513`), `2^-83` for the tree's
root (127), and about `2^-74` for every stream output at once (`257²` members).

**Textbook knowledge soundness (V4-A10, the user's decision of 2026-10-27).** The certificate
states the standard single-output notion a cryptographer reads, for adversaries that ask the
verifier's queries themselves: every adversary asking `Q` queries and outputting a statement and a
proof makes the verifier accept while the extractor, reading the final query log (the verifier's
answers included), returns no witness with probability at most `(Q + qV)·ε` (§1.4). Textbook
soundness implies it with the error at most doubled (**kernel**, `KSTextbook.ks`); every prover of
the deployment is of that kind, since the verifier reads only the signed trace. v3's potential
(`KState`) is an untrusted library tool, one route to a proof (`KState.ks`), and any correct proof
technique is accepted. Its cost: the tree composes by a union bound over the extracted proofs,
about `2^-81` where the potential's one event gave `2^-90`.

**What it costs.** A trusted runtime (the service, whose bug can be accept-all; the attested CI
workflow). One idealised assumption, keyed BLAKE2s is a PRF, beside collision resistance and
one-wayness, from which the signature's EUF-CMA follows (§2.5). Every oracle call goes to the
service on the prover's own cores. Per child, a node circuit checks one signature and hashes the
child's trace (§4.2). Trusted code: 350 Lean lines (v3: 292; budget 500) and 3,700 runtime lines
(§5; 3,800 before V4-A9, 3,670 after it). Two walls of v3 stand: node extraction is decoding (#7), and no honest
recursive entry is sized against the caps (C5); the certified baseline's measured frontier (§3.6)
shows how far the season shape is.

**The trim (V4-A9, the user's decisions of 2026-10-26).** Every rule is kept only if it serves
valid verifiers or honest, fast proving with priced recursion (§4.4 says what each is for). So:
one run of the tree and one of the stream, no medians; two parallel benchmark jobs; every GitHub
job within 30 minutes, with the caps nested inside it, so a slow entry is REJECTed with the reason,
never killed; only the tree's root is read; per entry only the statement canaries, on 2 proofs per
kind, and a DoS column of 100 inputs that fails on time and crashes only; no per-entry liveness;
the organiser's own checks (the canaries that never reach `V`, the extractor interpreter) in the
core CI only; one Lean build per certificate; stream `M = 256`; `errorCap = 2^-120` (admits
GF(2^128) designs, FB-9) and `completenessCap = 2^-40`.

| Status | |
|---|---|
| ran on the development VM | build and axiom audit; service, sandbox and harness tests; the witness-sending entry and the certified baseline `spartan-srom` ACCEPTed end to end at the smoke shape. After V4-A9: the build, the audit, every test of `ci.yml` and the end-to-end smoke, 16 checks in 4 min 21 s after the fix pass (`docs/v4/stages/D-trim-RESULT.md`, `logs/trim-fix/smoke-e2e.log`). After V4-A10: the same, the smoke 16 checks in 4 min 26 s, the witness-sending entry certified under the textbook `KS` (`docs/v4/stages/E-ks-RESULT.md`, `logs/ks/final-smoke-e2e.log`) |
| ran on a GitHub runner | before V4-A9: CI run 39966237935, all green (AMD EPYC 9V45 and 9V74, image ubuntu24 20261012.334.1): Lean job 7 min 29 s; service and sandbox tests; the end-to-end smoke in 9 min 18 s, 16 checks: the witness-sending entry certified with the Lean kernel and ACCEPTed with the compiled `accF` badge and a toy assembly prover, PROVISIONAL and REJECT paths, the job plan's missing part ⇒ ERROR, liveness, canaries, the DoS column, and five broken provers rejected for their stated reasons. Earlier runs: chain checker 1.78 s (`T_V` ≈ 178 ms); signatures equal to the Lean signer's |
| never ran | the evaluation workflow and its attestations; the trimmed harness (V4-A9) and the V4-A10 contract on a runner; any entry at the season-1 shape (C-m10), so nothing is ranked |

| | v3 | v4 |
|---|---|---|
| deployed oracle | public `BLAKE2s(0x52 ‖ q)` | `PRF_k(q)`, secret key fresh per run, behind a service |
| node clause | `Vb c₁ π₁`: `V` on public BLAKE2s | `acc vk c₁ (π₁, tr₁, σ₁)`: `V` on a signed trace |
| certificate | `KS`, `CompleteWithError`, `Computes`, caps | the same, **for every `vk`** |
| knowledge soundness | a knowledge state (a potential on logs) in the contract | the textbook single-output statement (V4-A10); the potential is a library route (`KState.ks`) |
| machine | a reference machine that never existed | GitHub-hosted runners, attested results |
| score | whole-tree wall time | `S = T_tree + K·t_link` |

## 1. The model and the relation

The submitter's side is v3's: a verifier `V` and an honest prover `P` as query programs over one
random oracle `ByteArray → Digest`, an extractor specification `E` computed by a step-counted
program `ext`, and a certificate. What changes is how a child proof is judged inside the relation.

### 1.1 Signed proofs and acceptance (trusted)

From `Contract/Relation.lean` (docstrings shortened to comments):

```lean
abbrev Digest := Vector UInt8 32
abbrev Proof  := ByteArray
abbrev Trace  := List (ByteArray × Digest)   -- oracle queries with their answers, in the order asked

structure Sig where
  idx  : ℕ             -- the one-time key's index (below 2^16 for a valid signature)
  ots  : List Digest   -- the WOTS chain values, one per digit (133 for a valid signature)
  path : List Digest   -- the Merkle siblings, leaf level first (16 for a valid signature)

structure Signed where
  π  : Proof           -- the proof
  tr : Trace           -- the oracle answers the verifier reads, in the order it asks
  σ  : Sig             -- the service's signature on the digest of tr

inductive Wit where
  | leaf (s : Digest) (n : ℕ)
  | node (c₁ c₂ : Digest) (p₁ p₂ : Signed)

def Rel (acc : Digest → Signed → Bool) : Digest → Wit → Prop
  | c, .leaf s n => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ p₁ p₂ => c = nodeStmt c₁ c₂ ∧ acc c₁ p₁ = true ∧ acc c₂ p₂ = true
```

From `Contract/Oracle.lean`, the one new way of running a program:

```lean
/-- The result of the program on the trace `tr`: its queries answered in order by the entries of
`tr`, each of which must be for the query asked; `none` on a mismatch, if the trace runs out, or if
entries are left over. -/
def runSeq : Trace → OProg α → Option α
  | [], ret a => some a
  | _ :: _, ret _ => none
  | (q', a) :: tr, query q k => if q' = q then runSeq tr (k a) else none
  | [], query _ _ => none
```

From `Contract/Certificate.lean`:

```lean
structure Submission where
  V : Digest → Digest → Proof → OProg Bool     -- vk, statement, proof
  P : Digest → Digest → Wit → OProg Proof      -- vk, statement, witness
  E : Digest → Proof → Log → Option Wit        -- no vk (V4-6)
  ext : XProg
  ε : ℝ≥0
  δ : ℝ≥0
  qV : ℕ
  fuel : ℕ → ℕ

def Submission.acc (S : Submission) (vk c : Digest) (p : Signed) : Bool :=
  decide (p.π.size ≤ proofCap) && decide (p.tr.length ≤ S.qV) &&
    decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) && SigOk vk (traceDigest p.tr) p.σ &&
    decide ((S.V vk c p.π).runSeq p.tr = some true)

structure Certificate (S : Submission) : Prop where
  secure   : ∀ vk, KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV
  complete : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ
  computes : Computes S.ext S.E S.fuel
  cap      : S.ε ≤ errorCap ∧ S.δ ≤ completenessCap ∧ S.qV ≤ 2 ^ 16 ∧
             (∀ t, S.fuel t ≤ extractorBudget t) ∧ S.ext.body.size ≤ progCap
```

Both caps, `proofCap` and `queryCap`, are `2^20` (`Relation.lean`).

**In words.** A signed proof is accepted for `c` under `vk` when the proof is at most 1 MiB, the
trace has at most `qV` entries and every query in it is at most 1 MiB, the signature on the trace's
digest verifies under `vk`, and
the submitted verifier accepts the proof with its oracle queries answered one by one from the trace
(each entry must be for the query asked, and the trace must be used up exactly). A node witness is
two child digests and two signed proofs accepted in that sense. The certificate is v3's, required
for every `vk`; `Declared` and `CertificateR` bind the declared numbers as in v3 §5.2.

### 1.2 Each choice, and why

| Choice | Reason | Id |
|---|---|---|
| A child is accepted against a signed trace, not by running `V` on the oracle | The relation then evaluates no oracle; a node circuit checks a signature instead of evaluating `PRF_k`, which it cannot do without `k`. The relation is an ordinary relation once `vk` is fixed. | P2, V4-3 |
| Every hash in the relation is public BLAKE2s-256 under one of seven tags `C L N T W K M` | No contract hash input is an oracle input or another domain's input. v3's oracle tag `R` is gone: keyed BLAKE2s differs from the unkeyed hash on every input (its first block is the key). | V4-16 |
| Sequential trace semantics (`runSeq`), not first-match lookup | Linear for the harness; a node circuit walks the child's trace in order with no lookup or permutation argument. | V4-4 |
| The trace is used up exactly | The signed trace is then exactly `V`'s query sequence on that trace's answers. A suffix-tolerant trace gave the relation witnesses with traces of every length, so a fixed-size node prover could not be complete (C-M3). | V4-A3 |
| `\|tr\| ≤ qV` in `acc` | Bounds every accepted trace by a fact of the relation, so the witness space is bounded and node circuits are sized from `qV`. `KS`'s query bound does not do it: it ranges over oracle functions, and a non-functional trace (two answers to one query, possible only with a forged signature or a known `sk`) follows no function's path (RA-M2; a functional trace meets it anyway, `runSeq_length_le`). | RA-M2 |
| `queryCap = 2^20` bytes per query in `acc` | Makes `enc64 \|q\|` exact, so the trace encoding is injective on every accepted trace by a fact inside the relation, and a trace-digest collision is a genuine BLAKE2s collision; equals the service's cap. Consequence: a √-size commitment must split its columns (§3.7, Q15). | V4-A3 |
| Conjunct order: size, trace length, query cap, `SigOk`, `runSeq` | Cheapest rejection first: a bogus proof costs a signature check (about 300 compressions), not a verifier run. | V4-A3, C-m5 |
| `proofCap` on `π` only | A trace is bounded by the verifier's queries and a signature is an index and 149 digests. | V4-13 |
| `V` and `P` take `vk`; `E` does not | A node circuit checks its children's signatures, so `vk` is a public input of the node's statement and `V` needs it. A node extractor decodes the children from the node proof's committed witness and never needs `vk`; a design whose encoding depends on `vk` writes `vk` into `π`, so the rule restricts nothing. | V4-6, C-m6 |
| `KS` and completeness for every `vk` | The signer is not in the model, and the theorem's adversary may hold `sk`; a verifier that trusts a signature is then uncertifiable (§2.2). | V4-1 |
| One predicate `acc` for the node clause, the harness and third parties | One trusted definition, compiled once: what the harness accepts is what the relation means. | V4-7 |

### 1.3 The signature scheme

The scheme is fixed by the contract (`Contract/Signature.lean`), so no entry can design around it.
It is a stateful hash-based signature: Winternitz one-time keys with base-4 digits (`w = 4`, chains
of three steps), 133 chains per key, under a Merkle tree of `2^16` one-time keys whose root is
`vk`. The service signs the trace digest (hash-then-sign). The check, from the contract:

```lean
def traceDigest (tr : Trace) : Digest := blake2sDigest (tagTrace :: traceBytes tr)
  -- traceBytes: each entry as enc64 |q| ‖ q ‖ a, in order

def wotsDigits (m : Digest) : List ℕ :=      -- 128 message digits, then 5 checksum digits
  let d := msgDigits m
  let C := (d.map (3 - ·)).sum
  d ++ (List.range 5).map fun t => C / 4 ^ t % 4

def SigOk (vk m : Digest) (σ : Sig) : Bool :=
  decide (σ.idx < 2 ^ sigHeight) && decide (σ.ots.length = wotsLen) &&
    decide (σ.path.length = sigHeight) &&
    decide (sigRoot σ.idx (wotsLeaf σ.idx (wotsEnds σ.idx m σ.ots)) σ.path = vk)
```

**Byte layouts** (normative; the service, the contract and the runner hash the same bytes):

| Hash | Input | Bytes | Compressions |
|---|---|---:|---:|
| trace digest | `0x54 ‖ item₀ ‖ item₁ ‖ …`, `itemᵢ = enc64 \|qᵢ\| ‖ qᵢ ‖ aᵢ` | `1 + Σ (40 + \|qᵢ\|)` | about 1.6 per 64-byte query |
| digits of `m` | byte `i` gives digits `4i + t = (m[i] >> 2t) & 3`, `t = 0…3`; checksum `C = Σ (3 − dᵢ) ≤ 384` gives digits `128 + t = (C >> 2t) & 3`, `t = 0…4` | — | — |
| chain step `F(j, i, s, x)` | `0x57 ‖ enc64 j ‖ byte i ‖ byte s ‖ x`: chain `i` of key `j`, position `s → s + 1` | 43 | 1 |
| key leaf | `0x4B ‖ enc64 j ‖ end₀ ‖ … ‖ end₁₃₂` | 4,265 | 67 |
| tree node | `0x4D ‖ left ‖ right`; at level `t` the current value is the left child iff bit `t` of `j` is 0 | 65 | 2 |
| chain start (service only) | BLAKE2s-256 **keyed by the signing seed** of `0x53 ‖ enc64 j ‖ byte i` | 10 | 1 |

A signature of `m` with key `j` reveals chain `i` at position `dᵢ`; the verifier walks it to
position 3 and hashes the ends into the key's leaf, then up the Merkle path to `vk`. Raising a
message digit lowers the checksum, so a signature cannot be walked forward to sign another message.

**Why `w = 4`** (C-M4 item 5, **estimate**): `w = 2` (265 chains) costs about the same in-circuit,
`w = 16` (67 chains, 15 steps each) more; a height of 11–12 instead of 16 saves about 3%. The cost
of one check is in §4.2.

**Why a stateful scheme with no public seed.** No group (V3-5), one hash gadget for agents
(BLAKE2s already proves the chains), the smallest in-circuit check of the hash-based options sized.
It is none of the published schemes (WOTS+, XMSS/RFC 8391, WOTS-TW): it has no public seed and no
bitmasks, so its security is argued directly (§2.5). A per-run public seed in every hash would make
it a WOTS-TW instance at one trusted line and one field of `Sig`, with no in-circuit cost; it is
not adopted (V4-A4), and is the fallback if a reviewer insists on a published scheme.

### 1.4 What v3 contributes, and the textbook knowledge soundness (V4-A10)

`Machine.lean` and `Tree.lean` are v3's, word for word (V4-1, V4-16). `Contract/Security.lean`
keeps v3's completeness and its caps' roles, with their values changed by V4-A9
(`errorCap = 2^-120`, `completenessCap = 2^-40`; v3 §6 and §7.1 explain them), and since V4-A10
(the user's decision of 2026-10-27) states knowledge soundness in its textbook single-output form,
where v3 required a knowledge state. In `KS` below, `runLog L` answers each query from the first
matching entry of the log `L` (`none` on a miss), where `runSeq tr` answers from the next entry of
the trace, and `prob B p L` is the probability that the program `p`, started with the table `L`,
ends with an output `x` and a final table `L'` with `B x L'` against a lazily sampled random oracle
(a fresh query answered uniformly over the `2^256` digests and recorded, a repeated one from the
table):

```lean
def KS (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  (∀ H c π, ((V c π).queries H).length ≤ qV) ∧
  ∀ (A : OProg (Digest × Proof)) (Q : ℕ), (∀ H, (A.queries H).length ≤ Q) → Q + qV ≤ logCap →
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧ ¬ ∃ w, E x.1 x.2 L = some w ∧ R x.1 w)
      (A.bind fun x => (V x.1 x.2).bind fun _ => .ret x) [] ≤ (Q + qV) * ε
```

- **Knowledge soundness** (`KS`): `V` asks at most `qV` queries on every input and oracle function;
  and every adversary, a query program asking at most `Q` queries on every oracle function and
  outputting a statement and a proof, run and then followed by `V` on its output against one
  random oracle, makes `V` accept on the final query log while `E`, given the statement, the proof
  and that log, returns no witness, with probability at most `(Q + qV)·ε`, `ε ≤ errorCap`, for
  `Q + qV ≤ logCap = 2^96`. The adversary is computationally unbounded, query-bounded and
  deterministic; randomised adversaries follow by averaging over their coins, since `E` does not
  depend on the adversary (**paper**). It chooses the statement after its queries. The verifier's
  queries are charged because an adversary may leave its luck to them (**kernel**,
  `Controls/Security.lean`, `queryThenAccept_ks_ge_one`); `logCap` because a linear bound cannot
  hold for every `Q` against a birthday-type event (the header of `Security.lean`); and `KS` is
  vacuous above it, which the certificate's `qV ≤ 2^16` excludes (no conjunct, by decision, review
  E-ks m-1). Acceptance read from the final log is the verifier's verdict in the game (**kernel**,
  `Library/KS.lean`, `prob_accept_eq_verdict`).
- **The extractor reads the final log, the verifier's own answers included** (review E-ks M-1;
  option B, the user's choice of 2026-10-27). The textbook definition (Chiesa–Yogev; CGSY24) gives
  it the adversary's log only. So `KS` is the textbook notion for *normalised* adversaries, those
  that ask the verifier's queries themselves, and the two coincide on them. **Textbook ⇒ `KS`**,
  with the same extractor and the error at most doubled: the adversary followed by `V` is a
  textbook adversary of `Q + qV` queries, bound `(Q + 2qV)·ε ≤ 2(Q + qV)·ε` (**kernel**,
  `Library/KS.lean`, `KSTextbook.ks`, for the textbook notion up to `logCap + qV` queries). **`KS` ⇏
  textbook**: a verifier that accepts when its own fresh answer, masked, is the statement's witness
  is certified at error 0 with an extractor that reads that answer (**kernel**,
  `Controls/Security.lean`, `lucky_ks`), while the textbook error of the same pair is at least
  `2^-112` (**kernel**, `lucky_not_textbook`) and so is every efficient extractor's (**paper**,
  preimage hardness). **Why the deployment needs no more**: every prover in it is normalised, since
  the verifier reads only the signed trace and the prover asked the service for every answer in
  it; and in the composition an extracted member's verifier asks nothing fresh (`KS.select`, §2.4).
  Option A, an extractor that reads only the adversary's log, was rejected: it breaks the
  potential's bridge and every potential-based proof, and is stronger than the deployment needs
  (BRIEF §5c).
- **The potential is a library route** (V4-A10). v3's knowledge state (`Library/Security.lean`,
  `KState`: a potential `μ` on query logs that starts at 0, rises by at most `ε` on average per
  fresh answer within `logCap`, and below 1 makes every proof `V` accepts on the log extractable
  by `E`) is untrusted; the bridge **`KState.ks`** (`Library/PaperTheorem.lean`, **kernel**) turns
  it into `KS` by Markov's inequality on the stopped potential, generalised from v3's syntactic
  depth to the functional query bounds. Any other correct proof of `KS` is accepted.
- **Completeness** (`CompleteWithError`): on every statement and witness of the relation, the honest
  prover's proof, produced and verified against one lazily sampled random oracle, is rejected with
  probability at most `δ ≤ 2^-40` (V4-A9: a failure costs only its entrant a run; grinding to
  difficulty `2^g` needs about `28 · 2^g` attempts, `89 · 2^g` at v3's `2^-128`).
- **The extractor** (`Computes`): `ext` is a program of the contract's word machine (no
  function-typed field, every step charged), and computes `E` within `fuel t ≤ B t = 2^48 + 2^16·t`
  steps on a tape of `t` words, on every proof up to `proofCap` and every log whose tape the machine
  can address (about `2^61` entries).

### 1.5 The extractor's output for signed children

`Contract/Extractor.lean` keeps v3's input tape and changes only the output, which must now denote
a node witness with two signed children: tag 1, two digests, and for each child the proof
(length-prefixed), the trace (laid out as a log on the input tape) and the signature (the index,
133 chain values, 16 path digests). The decoder reads **strictly**: a field that runs past the end
denotes nothing, where v3 read missing words as 0. Everything decoded is then bounded by the
output's length and decoding is linear (C9). With `outCap = 2^24` words and both proofs at
`proofCap`, `2^24 − 263,351` words remain for the two traces, for example `2^16` queries of up to
960 bytes per child. A node whose children's traces exceed `outCap` cannot be extracted and is
therefore not certifiable, which is the right outcome (C-m11).

---

## 2. Security

### 2.1 One level: what a certificate says

For every public key `vk`, the submitter proves the textbook single-output knowledge soundness,
for adversaries that ask the verifier's queries themselves (§1.4, V4-A10), of `V vk` for
`Rel (S.acc vk)` with the named extractor and completeness of `P vk`,
both over a random oracle. A node extractor recovers
the node's witness, the two children's signed proofs, from the node proof and the log (for a
succinct node, by decoding a word committed in the log, v3 #7; for the witness-sending entry, by
reading the proof) and outputs it; it does not check them, and the certificate does not ask
whether their signatures are genuine. That is the composition's job (§2.4).

The relation is **oracle-free given `vk`**, so completeness means what it says: the game samples a
fresh oracle only for `P`'s and `V`'s own queries, and a node witness carries its children's
signatures as data (C §2 item 6). The Lean `P` needs no signer. In deployment the native prover
obtains its own proof's signature from the service; the Lean `P` exists so that completeness is a
theorem.

Completeness for every `vk` is vacuous on the node clause for a `vk` under which nothing is signed,
so its positive control signs the children with the Lean reference signer and proves `SigOk`
symbolically (C-m12; **kernel**: `Library/Signer.lean`, `sigOk_sign`, for every function of secret
chain starts, every index below `2^16` and every message; the node-clause control
`Controls/Relation.lean`, `node_of_two_leaves`, an honest node of two signed leaf children, for
every secret function, starts and lengths, and `node_of_two_leaves_ref` with the reference
derivation). Negative controls: a child signed under another key (`child_other_key`), a trace with
one answer changed (`traceDigest_changed_answer`; and `acc_changed_answer`: if one signature is
accepted on two different traces, their digests differ or their encodings collide), a
witness-sending child carrying a trace (`child_trace_nonempty`), `|ots| ≠ 133`
(`Controls/Signature.lean`, `sigOk_ots_length`), a malformed trace length in `decodeWit`
(`Controls/Extractor.lean`, `decodeWit_long_trace`).

### 2.2 No certified verifier can trust a signature

**Statement** (**paper**, C-m1). Let `B` be a branch of `V` that accepts some `(c, π)` with `c`
outside the language because of a predicate `Φ(vk, π, answers)` that an unbounded adversary with
oracle access can make true for every oracle: a valid signature under `vk` in `π`, `sk` in `π`, a
signed answer in `π` that agrees with the oracle's. Then for that `vk`, `V vk` is not
knowledge-sound at any `ε` with `(q + qV)·ε < 1`, where `q ≤ qV` is the number of oracle queries
on the branch; in particular not at `errorCap = 2^-120`, since `q + qV ≤ 2^17`.

**Proof.** The adversary asks the branch's queries itself, makes `Φ` true (it is unbounded, so it
can sign anything under `vk`) and outputs `(c, π)`. The verifier run after it asks only queries
already in the log, so on the game's final log `L`, `(V vk c π).runLog L = some true`, and `E`
returns no witness for `c`, which has none. The adversary wins with probability `1`, so `KS` needs
`1 ≤ (q + qV)·ε`. ∎ If `Φ` needs no query, the adversary asks nothing, and `KS` at `qV·ε < 1`
forces `E` to open every such proof to a witness on the empty log, which needs every digest to
have one, the shape of `acceptAll_ks_iff` (`Library/KS.lean`); then `Computes` with the budget
excludes the extractor (v3 §6.2).

The general statement is paper; the kernel controls are its `q = 0` case.

**Controls** (**kernel**, `Library/SigTrust.lean`). `Vsig vk c π` accepts, with no oracle query,
a proof carrying a signature of `c` valid under `vk`. Under every key whose signer is known
(`Signer.pk sk`, keys the certificate quantifies over), the adversary that holds `sk`
(`adversary sk c`: it asks nothing and outputs `c` with `sk`'s signature of `c`) wins with
probability `1` unless the extractor opens that signature to a witness on the empty log
(`adversary_wins`). So `sigTrust_ks_extracts`: knowledge soundness at `qV ≤ logCap`,
`qV·ε < 1` (the certificate's caps give both) makes the named extractor find witnesses from
signatures alone; `sigTrust_not_ks_none`: with an extractor that returns nothing, it fails;
`sigTrust_ks_iff`: it is knowledge-sound for some extractor exactly when every statement has a
witness, so a signature is no knowledge. The twin `sigTrust_ks_of_unsignable`: under a key for
which no signature verifies, the same verifier is knowledge-sound at error 0 for every relation
and extractor. So it is exactly the quantification over keys, some of whose secrets the adversary
holds, that excludes it; a certificate for one fixed key would not. `Controls/Certificate.lean`
states the same about `Certificate` (`sigTrust_no_certificate`, `sigTrust_certificate_opens`,
`sigTrust_ks_unsignable`). The same facts about the library's potential (`sigTrust_kstate_iff`,
`sigTrust_no_kstate_none`) are kept.

**What it means.** A node circuit does check signatures, but as part of proving the relation's own
`acc` conjunct for its children; the extractor must still return those children. What `V` cannot
do is let a signature stand in for a witness. The `∀ vk` quantifier and the unbounded adversary
(V4-1) are what make this so: the certificate never rests on unforgeability, and only `acc`, which
never sees the oracle, trusts a signature. This is the answer to the recognition rule of the
2026-10-19 design ("`V`'s local computation must not evaluate the oracle's instantiation", O-25 §2):
the rule could not be stated so that review could check it (ADV-M5), and under the SROM there is
nothing left for it to forbid. A verifier that compares answers with signed values is either
harmless or uncertifiable; one that compares answers with a value it computes about the
instantiation has nothing to compute (§2.3).

### 2.3 The deployment argument: why O-25 closes

**The hybrid** (**paper**; [CGH] §2, [RD] §4.9). Let *bad* be the event "the root's signed proof is
accepted and the composition walk (§2.4) returns neither leaf witnesses nor a collision nor a forged
trace". A tester decides it by running the evaluation (whose prover and checks the harness bounds
by its time caps) and the walk (`E` within its proved budget, public hashes, and `V` where the walk
runs it; the contract does not bound `V`'s running time, the measured `T_V` does in practice, as
in [RD] §4.9's fine print). So

```
Pr_deployment[bad]  ≤  Pr_random function[bad]  +  Adv^PRF(D),
```

where `D` runs the whole evaluation: the prover, the signer (`D` draws the signing seed itself), the
harness's checks and the walk, with the PRF challenge as the oracle; at the season shape about
`2^58` steps and `2^28–2^30` queries (**estimate**, §2.4). For a certified `V` frozen
before `k` is drawn, the first term is the certificate's bound and the second is one assumption
about one fixed function, the same for every `V`.

**Conditions**, each enforced by the deployment (§3): `k` is drawn after `V` is frozen; neither
`V`, its author, the Lean `P` nor the native prover ever holds `k`; `k` and the signing seed are
**independent** draws (if the seed were derived from `k`, `D` would not be a PRF distinguisher, and
worse, see §2.5); the key is fresh per service lifetime and never reused; the service implements
its specification (tested, not proved). The steps from the Lean theorem's lazily sampled oracle to
a random function and to randomised adversaries are on paper, as in v3.

**Every channel by which a verifier could learn about the deployed oracle** (C §1, condensed):

| Channel | Carries a value about `PRF_k`? | Why the certificate or the deployment stops a `V` that uses it |
|---|---|---|
| any oracle query | yes, but only through a query | in the model the adversary asks first, the answer is in the log, `final` must extract (O-25 §2) |
| `vk` | no: a root of hashes of the signing seed, independent of `k` | a branch on `vk = vk*` fails `∀ vk` |
| a signed trace, `sk` or a WOTS secret in `π` | the trace does, through the service | §2.2: uncertifiable |
| the post-hoc challenge verification (O-25 §6.1) with BLAKE2s wires | would need keyed BLAKE2s under `k`, or the chaining state after the key block; neither leaves the service | dead branch: in the model `2^-192`, in deployment never true |
| the same with a signed trace as the "wires" | in deployment, yes | §2.2: uncertifiable |
| cross-run or cross-entry reuse | `k`, `(sk, vk)` fresh per lifetime; a record publishes `vk` and the root's answers after `k` is destroyed | nothing to reuse |
| `sign` on traces that are not a verifier's | signatures on genuine answers, available to everyone in the SROM | harmless; the signer's queries are in the log and counted in `Q` |

**The liveness mirror**, a `V` that rejects honest proofs only under the deployment, needs a
recognition site and has none; it is closed by the same reduction, and would harm only its author.
**What the argument does not give:** that a public-hash deployment of the winning design is sound.
CGH and the Fiat–Shamir counterexamples (GK03, BBHMR19, KRS25, Fenzi26) still apply to any public
instantiation; records certify the signed deployment (RU-5).

### 2.4 Composition across the tree

**The argument** (CGSY24 Thm 5.1 and §6.2; C §2; since V4-A10 by a union bound over the extracted
proofs). Treat the deployed prover together with the signer and the harness's checks as one query
algorithm `A` against the oracle; for each fixed signing seed it is deterministic, and knowledge
soundness covers every deterministic query algorithm however much it computes, so holding `sk`
costs nothing. Its log `L` contains every query anyone asked, including the signer's re-evaluation
of every trace it signs, and `Q` counts them all. Walking down from the root:

1. The root's signed proof `(π, tr, σ)` is accepted, so `SigOk vk (traceDigest tr) σ`.
2. Either every entry of `tr` is the log's answer to its query (the trace is **genuine**: the
   service computed each answer by a query, and the oracle has one answer per query), or the walk
   has found a valid signature on a trace not contained in the log: outcome **forgery**.
3. If genuine, `runSeq tr` accepting implies `runLog L` accepting (the `runSeq → runLog` lemma),
   so `V` accepts the member on the run's log; then `E` returns `w = E c π L` with
   `Rel (acc vk) c w`, or the member **escapes**. An escape is a win of the knowledge-soundness game
   for the adversary that runs `A`, keeps its log and outputs this member: it asks at most `Q`
   queries (the extractor is a Lean function and the adversary is unbounded, so it computes the
   member), and `V` run after it asks nothing fresh. By the certificate each member escapes with
   probability at most `(Q + qV)·ε`.
4. A node witness gives children `(c₁, p₁)`, `(c₂, p₂)` accepted by `acc`. Either `c₁, c₂` are the
   harness's children, or the walk has a `nodeStmt` collision: outcome **collision**. Recurse on each
   child with the same `L`.
5. At a leaf, the extracted `(s, n)` hashes to the harness's leaf digest: a witness (not necessarily
   the harness's start), or a `leafStmt`/`chainStep` collision.

So the walk returns the leaf starts, a collision or a forgery unless one of the `N` members of the
extraction tree escapes, and a union bound over them gives `N·(Q + qV)·ε` for that case. No member
costs more than one adversary's queries and the verifier's: the member's adversary runs no inner
verifier, since `E` reads the log. A knowledge state (the library's potential) composes losslessly
instead: below potential 1 on the run's log, `final` extracts every accepted member
(`compose_of_kstate`), and the one event, the potential reaching 1, has probability at most
`(Q + qV)·ε` (`PaperTheorem.prob_potential_ge_one`), for the whole tree; the textbook statement
the certificate now makes pays the factor `N`.

**What is kernel and what is paper.**

| Piece | Status |
|---|---|
| `walk L n hn r hs hr p hacc : Outcome S vk L n hs root p r`: from a log, `2^r` leaves and an accepted root signed proof, it computes the leaf starts, an explicit BLAKE2s collision, an explicit signed trace with queries within `queryCap` not contained in the log **in the root's extraction tree** (`InTree`, with the member's path), or an **escape**: a member within depth `r`, accepted, its trace in the log, that `E` does not open to a witness | **kernel**, Library (untrusted, kernel-checked): `Library/Compose.lean`, `walk`, and `compose`, its propositional form (V4-8; its first disjunct, that starts exist, is free when the harness drew them, so the content is that `walk` computes them, RA-M1); `compose_exists`, without the forgery's `InTree`, is trivially true for a known signer's key (`Controls/Compose.lean`, RA-M1) |
| an escape on a functional log is a win of `KS`'s game at that member (`Escape.wins`); an adversary that runs `A` keeping its log and outputs any function of `A`'s output and log is bounded like every other (`KS.select`), and a finite family of them by the sum (`KS.union`) | **kernel**: `Library/Compose.lean`, `Library/KS.lean` |
| **the composition bound**: for `A` asking at most `Q` queries with `Q + qV ≤ logCap`, the probability that `acc` accepts the root and `walk` on `A`'s final log ends in an escape is at most `(2^(r+1) − 1)·(Q + qV)·ε` | **kernel**: `Library/Compose.lean`, `compose_prob` (through `escape_prob_le`, the union bound over any finite set of paths of the extraction tree, and `card_paths`) |
| the meter's lossless form: with a knowledge state and one functional log within `logCap` below potential 1, no member escapes and the walk returns the first three outcomes; the potential reaches 1 with probability at most `n·ε` for a game of `n` queries | **kernel**: `compose_of_kstate`, `PaperTheorem.prob_potential_ge_one` (that a lazily sampled log is functional and within `logCap` joins them on paper) |
| the stream: its final output's extraction tree (513 members, depth 256) | the union bound **kernel** for any finite set of paths (`escape_prob_le`, with the comb's 513 paths); the walk over the stream's shape **paper** (the kernel walk is the tree's, as before V4-A10) |
| `runSeq → runLog` | **kernel**: `Library/Trace.lean`, `OProg.runLog_of_runSeq` (on a functional log, a verdict on a trace whose entries are all in the log is the verdict on the log) |
| equal trace digests are equal traces or an explicit collision | **kernel**: `Library/Trace.lean`, `traceDigest_eq` (for queries under `2^64` bytes, which `queryCap` implies) |
| one member's bound `(Q + qV)·ε` | the certificate itself (`KS`), for a lazily sampled oracle and a deterministic adversary; the member's adversary is normalised (the verifier run after it on an accepted member asks nothing fresh, `KS.select`), so `KS`'s final-log extractor reads the adversary's log, as the textbook's does (§1.4); randomisation and the random function **paper** |
| the split of "a signed trace not in the log" into an **EUF-CMA forgery** (no signed trace has that digest) or a **trace-digest collision** (the service signed another trace with the same digest; the two encodings differ and are injective by `queryCap`) | **paper** (V4-A8, C §2 item 4). A kernel form would carry the service's signed set as a Library parameter (C, unsettled 5); not done |
| the PRF hybrid | **paper** (§2.3) |

**The error.** `Pr[bad] ≤ N·(Q + qV)·ε + Adv^PRF(D) + Adv^EUF-CMA(B) + Adv^coll`, where `N` is
the number of members of the composed output's extraction tree, `N = 2^(r+1) − 1 = 127` for the
season's tree (`r = 6`) and `N = 513` for the stream's final output (`M = 256` links: 257 leaves and
256 nodes, depth 256), and `B` and `D` run the evaluation and the walk: about `2^58` steps
(**estimate**, [RD] §4.9 fine print; the walk runs `E` per node within `B t`). At the season shape
`Q ≈ 2^28–2^30` (**estimate**, C §2 item 1), inside `logCap = 2^96` and the efficient-extraction
domain of about `2^61` entries, so at `ε = errorCap = 2^-120` the first term is at most about
`513 · 2^30 · 2^-120 ≈ 2^-81` for the event that the stream's final output escapes (its
extraction tree's 513 members) and `127 · 2^30 · 2^-120 ≈ 2^-83` for the tree's root
(`qV ≤ 2^16` is negligible beside `Q`), where the potential's lossless composition gave
`2^30 · 2^-120 = 2^-90` (**estimate**). The harness checks every stream output, not only the last:
a union over the 257 outputs' extraction trees (`Σ_{i ≤ 256} (2i + 1) = 257²` members) gives about
`2^16 · 2^30 · 2^-120 ≈ 2^-74` for "some checked stream output escapes" (**estimate**). The kernel
theorem is per root and for the season's balanced tree; the stream's comb needs the paper walk
(table above). At the caps one member's bound is
`2^96 · 2^-120 = 2^-24` at `2^96` queries and `2^-56` at `2^64`; collision-type events are
chargeable at the cap from `216` bits up (`logCap · 2^-t ≤ 2^-120`; a full digest costs `2^-160`
and an honest Merkle verifier comparing `2^15` digests per query `2^-145`, both below it).

**Fiore–Nitulescu** (ePrint 2016/112) show that SNARK extraction can fail against adversaries with
an exogenous signing oracle. It does not bite here (**paper**, C §2 item 5): the extractor is
straightline, reads only the log, and the signer's queries are in the same log.

### 2.5 The signature's security (V4-A4)

**What is claimed** (**paper**). Let the signer use each index at most once and at most `2^16`
indices, with chain starts `skⱼ,ᵢ = PRF_seed(0x53 ‖ enc64 j ‖ byte i)` under a seed independent of
`k`. Then for every adversary that sees `vk` and obtains signatures on adaptively chosen 32-byte
messages, the probability of a valid signature on a message never signed is at most the sum of:

1. finding a **collision** of BLAKE2s-256 on the tagged domains `K` (key leaves), `M` (tree nodes)
   or `W` (chain steps with the same tweak);
2. inverting a **chain step** `F(j, i, s, ·)` on its honest input, multi-target over the chain
   values of one key tree, about `2^16 · 133 · 3 ≈ 2^24.6` targets, and over every tree ever
   published, since the tweak names the index but not the key;
3. distinguishing **keyed BLAKE2s** under the seed from a random function (the chain starts);

with the usual guessing loss in the reduction for item 2. Hash-then-sign adds (4): a forgery on a
*trace* is a forgery on its digest, or a collision of the tagged trace digest (`T`) between two
distinct traces, which `queryCap` makes distinct encodings.

**Why** (the classical Merkle and Winternitz argument). Walk the forgery's path up to `vk` beside the
honest tree: a first point where the values agree but the inputs differ is a `K` or `M` collision.
Otherwise the forgery's chain ends are the honest ones for key `j`. Key `j` signed at most one other
message, and the checksum guarantees a chain `i` on which the forgery reveals an *earlier* position
than any signature did. Walking both values forward to the common end, either they meet early (a
`W` collision under one tweak) or the forger knows the honest value at that earlier position, which
inverts the chain step at a revealed target.

**Precision on item 2** (this document's, refining C-M4's "one-wayness on uniformly random
inputs"). The honest input to `F(j, i, s, ·)` is uniform only at `s = 0` (a PRF output); at `s = 1, 2`
it is one or two applications of `F` to a uniform value. The assumption is one-wayness on those
distributions; WOTS+ derives it from one-wayness on uniform inputs plus undetectability (the
image of a uniform input looks uniform). With `w = 4` the chains are three steps long, so the
distinction costs little, but it is the statement to be checked.

**Model.** Every item is a property of public or keyed BLAKE2s, so the argument needs no random
oracle. Keyed BLAKE2s as a PRF is the design's **one idealised assumption about BLAKE2s**: its
analysis (Luykx–Mennink–Neves, ePrint 2016/827) is in an ideal-cipher model of the compression
function. It serves twice, for the oracle (`k`) and for the chain starts (the seed). Collision
resistance and one-wayness are the assumptions every hash-based signature makes.

**Margins** (**estimate**). Generic attacks on 256-bit BLAKE2s: a collision among `2^58`
evaluations has probability about `2^-141`; inverting one of `2^45` targets (`2^20` key trees) with
`2^80` evaluations about `2^-131`. Collision resistance (128-bit generic) is the binding term,
below `errorCap = 2^-120`.

**Operational conditions** (§3.2): the index is taken in one atomic step before the
signature is computed, and never reused; the signer refuses after `2^16`; a restart is a new key and
aborts the run (earlier proofs no longer verify under the new `vk`); `k` and the seed are
independent `getrandom` draws.

**Key separation** (C-M4 item 3). If the seed were `k`, every chain start
`PRF_k(0x53 ‖ enc64 j ‖ byte i)` would be the service's answer to that 10-byte query, and every
signature forgeable. Oracle queries carry no tag (V4-2), so the tag `0x53` does not prevent this
(V4-A4's wording, corrected): the independence of the two draws does, and a personalisation in
BLAKE2s's parameter block would be the hardening for a shared key. The Lean reference signer
(`Library/Signer.lean`) is the specification the service is tested against, derivation included.

### 2.6 Completeness, and the checks under the deployment

Completeness is over a random oracle, so it does not say that an honest proof passes `acc` under
the deployed `PRF_k` and `vk`; the harness's concrete checks do (C8): the tree's root and every
stream output are checked with the compiled `acc`. The extractor is not run per entry (V4-A9): its
correctness and its cost are the kernel-checked `Computes`, and the core CI runs the compiled
contract interpreter on the library's witness-sending entry once per harness commit
(`scripts/speed/Extract.lean`). The service therefore keeps no query log (its liveness mode is
gone); the composition argument's log is the run's query log as a mathematical object (§2.4), not
a file.

`CompleteWithError` is about `V`, not `acc`: a `V` that accepts only proofs longer than `proofCap`
is certified and fails every harness check (v3 §6.4). A verifier whose queries on one proof exceed
what one `sign` request carries (a body of at most 16 MiB) can never obtain a signed trace, and
fails the same way.

### 2.7 The trust statement

> **A ranked record means:** the certificate job's Lean kernel accepted `CertificateR` for the
> rendered challenge; the benchmark jobs, on GitHub-hosted runners, started a fresh service for
> every timed run, checked the tree's root and every stream output with the compiled `acc` under
> that run's `vk` within `T_V`, and measured `T_tree` and the stream, one run each; and the result
> JSON, binding `vk`, the CPU model, the runner image, the harness commit and the service binary's
> hash, carries a GitHub artifact attestation that verifies against the organiser's evaluation
> workflow. Its reader trusts:
>
> 1. **One kernel**: Lean v4.34.1's, the comparator that replays the proofs in it, and Lean core,
>    Mathlib and the pinned packages as hashed in the olean manifest. *v3 also had nanoda as a
>    second kernel; CI drops it (Q5).*
> 2. **The contract**: 10 files, 350 code lines, no theorem, three standard axioms. It now includes
>    the signature check `SigOk`, the trace digest and `runSeq`, and states knowledge soundness in
>    its textbook single-output form over a lazily sampled oracle (`prob`, `KS`, V4-A10), beside
>    v3's completeness and extractor machine. The potential (`KState`) is not trusted: it is one
>    library route to `KS` (`KState.ks`).
> 3. **BLAKE2s** = RFC 7693, and three properties: collision resistance on the seven tagged domains
>    (constructive: a failure is a pair someone can exhibit), multi-target one-wayness of the chain
>    step, and **keyed BLAKE2s-256 is a PRF** (LMN16's ideal-cipher analysis), for the oracle and for
>    the signer's key derivation. EUF-CMA of the contract's scheme follows from these (§2.5).
>    *Replaces v3's "BLAKE2s instantiates the random oracle".*
> 4. **Knowledge soundness of the whole tree from one log, by a union bound over its members**
>    (§2.4, V4-A10): the one-level certificate, the composition walk and the union bound
>    (`compose_prob`: the walk on the run's log escapes with probability at most
>    `(2^(r+1) − 1)·(Q + qV)·ε`) are kernel for the harness's tree; the paper steps are the passage
>    from the lazily sampled oracle to a random function and to randomised adversaries, the PRF
>    hybrid (§2.3), the reading of the walk's forgery outcome as a forgery or a trace-digest
>    collision, and the walk over the stream's shape (its union bound is kernel). `KS`'s extractor
>    reads the final log (§1.4): every member's adversary in the composition is normalised, so this
>    is the textbook notion where the bound is used. *v3's item 4
>    (O-25 open, no composition theorem) is gone.* Completeness is over a random oracle; that honest
>    proofs pass `acc` under the deployment is the harness's concrete checks.
> 5. **The badge code**: what Lean's compiler emitted for `acc` (through the word-level BLAKE2s twin
>    proved equal to the contract's, V4-A7), compiled from the one build whose exports the kernel
>    checked (V4-A9), guarded by the source rule and gate rules 3 and 6–8 (v3's rule 9 went with
>    the frontend); residual O-12. No badge runs `P` or `ext` any more (V4-A9). *(v3 item 5)*
> 6. **The harness tools**: gate, source rule, axiom audit, manifest, renderer, sandbox. *(v3 item 6)*
> 7. **Tested, not proved: the runner and the service.** The runner: Python `treeRoot`, the prover
>    interface, the caps, the measurements, the stream protocol. The service: tested against
>    `hashlib.blake2s(key=…)` (the empty message included) and against the Lean reference signer
>    (derivation, signatures, `SigOk`), and under concurrent `sign` load. Its failures that would be
>    accept-all: an answer that is not `PRF_k` signed, an index used twice, the key reachable from the
>    sandbox, a key reused across lifetimes.
> 8. **The organiser's key management**: `k` and the signing seed are independent `getrandom` draws
>    inside the service, never written, destroyed at exit; a restart aborts the run. A published `vk`
>    certifies a record **relative to this** (V4-A8, C-m9): a third party who checks `acc vk c p`
>    trusts that `vk` came from the service of the attested job and that `sk` never left it.
> 9. **The trusted machine**: a GitHub-hosted runner of the recorded image, running the organiser's
>    workflow at the recorded commit; GitHub's artifact attestations as the anchor (V4-A1); the
>    sandbox's isolation of untrusted code from the service and from the job's credentials; and
>    **the cache store** that carries the organiser's environment from the setup jobs to the jobs
>    that run the entry (V4-A9, review D-trim m-4): the GitHub Actions cache of the submissions
>    repository's default-branch scope, to which only the `setup` and `setup-tools` jobs save, whose
>    saved keys are immutable and name the resolved core commit, and from which a new commit's
>    setup starts with the latest cache under the same prefix. The olean manifest travels inside the
>    cache, so it cannot detect a poisoned one; every result records the environment it was checked
>    against (`environment`: the core commit and the manifest's and allowlist's hashes).
> 10. **The calibration**: `T_triv,best` measured in the same job (§3.5); the service's measured
>     throughput, published beside every score.
>
> Not trusted: `Library/`, `Controls/`, the entries, the assembly provers. Not claimed: §2.8.

What a reader no longer trusts, against v3: that the submitted `V` does not recognise the deployed
oracle; that BLAKE2s is a random oracle; a reference machine that did not exist. What is new:
items 7 (the service), 8 and 9. The organiser as a person holds no key: `k` and `sk` exist only
inside one job's service process, so what is trusted is published code on GitHub's machine, as
attested.

**What dropping nanoda costs** (Q5). nanoda reached 17.6 GB after 10 min 51 s on the witness-sending
entry, unfinished (**measured**, stage B, `logs/harness/nanoda-ws.log`), so CI checks with the Lean
kernel alone. A record is then not cross-checked by an independent kernel: a soundness bug in
Lean's kernel, or a proof exploiting one, is not caught, where v3 needed both kernels to fail
together. Running nanoda on a larger machine restores the check (§6.2).

### 2.8 What is not claimed

- That a **public-hash deployment** of a winning design is sound (CGH; §2.3).
- **EUF-CMA** as a theorem, or the forgery/collision split, in the kernel (§2.4, §2.5).
- A **lossless** composition from the certificate: the textbook `KS` composes by a union bound,
  `N·(Q + qV)·ε` with `N` the extracted proofs (V4-A10, §2.4); one event for the whole tree holds
  only for an entry that exhibits a knowledge state (`compose_of_kstate`), which the rules do not
  require. The **walk over the stream's shape** is paper (its union bound is kernel).
- Anything for `qV > logCap`: `KS` is vacuous there (`acceptAll_ks_above_logCap`); the
  certificate's `qV ≤ 2^16` excludes it.
- That `KS` is the textbook notion for adversaries that leave queries to the verifier: its
  extractor reads the verifier's answers too, so a verifier that decides on its own fresh answer
  can be certified (`lucky_ks`, §1.4). No such adversary exists in the deployment, where the
  verifier reads only the signed trace.
- That **honest proofs pass `acc`** under the deployment: measured by the harness, not proved.
- The **native prover's** correctness; only the signed proofs it writes are checked.
- **Efficient extraction** beyond `B t` and the domain of about `2^61` log entries; anything for
  `Q + qV > logCap` (O-21, unchanged).
- That the **succinct node's** extractor exists: kernel only for children in the clear (the
  witness-sending entry); a decoding node extractor is a paper obligation (#7, C4).
- That `T_tree` **rewards recursion** inside the tree: flattening is allowed there, and the stream
  prices recursion (§3.6).
- That any **certified entry fits the season-1 shape** (C-m10).
- Anything about a record whose `vk` and result are not bound by an attestation of the organiser's
  workflow.

**What has been exercised** (as in §0): the development VM ran the build, the tests and two
entries end to end at the smoke shape, the trimmed harness of V4-A9, and the V4-A10 contract with
the witness-sending entry end to end; a GitHub runner (CI run
39966237935) ran the core CI with the end-to-end smoke before V4-A9; the evaluation workflow and
its attestations have never run. Until they do, every end-to-end claim here is from
the development VM, and no record of the kind the trust statement describes exists.

---

## 3. The deployment

### 3.1 The trusted machine: GitHub Actions with a trust anchor (V4-A1, V4-A2)

**Why CI.** v3 had no reference machine, so every measured rule was a placeholder (C13). A
GitHub-hosted runner is a public, identical-image machine that anyone can re-run, and GitHub's
artifact attestations give a checkable statement "this result was produced by that workflow at
that commit on GitHub's runner". The costs are stated in P3 of the brief: `ubuntu-24.04`, x86-64, 4
vCPU, 16 GB RAM, 14 GB disk, 6 h per job (the rules allow 30 minutes, V4-A9), and **heterogeneous
CPU models** (AMD EPYC and Intel Xeon; carry-less multiply available; AVX-512 and GFNI not
guaranteed). Hence: the benchmark shape fits 16 GB; `T_V` self-calibrates in the same job; every
result records the CPU model; records are only ever compared in pairs within one job (v3's ABBA
rule).

**Separate jobs** (V4-A2, C-M2, V4-A9). A `plan` job resolves the core commit every later job
checks out and keys its caches on. Two **setup jobs** build the organiser's environment: `setup`
the package tree, the organiser build with its olean manifest and import allowlist, and the
objects the badge links (§3.6); `setup-tools`, beside it, the comparator and the service. Each
caches its output per core commit; neither fetches the entry, so what they save exists before any
entry code is on any machine of the run, and a cache miss costs their time, never an entry's. A
save that did not land fails its setup job with the reason; a later job that finds a cache missing
ends as an attested ERROR with the reason, never as a missing part. The **certificate job** (source rule, the entry's one `lake build`, the comparator, the
gate, the badge build) restores that cache, is deterministic and may run on any runner. It uses
the **Lean kernel only**: nanoda does not fit a 16 GB runner (§2.7, Q5) nor the 30-minute job; a
larger machine can add it, and the result states which kernels ran. The **benchmark** must run on
the GitHub-hosted runner; it is two parallel jobs (V4-A9): the tree job (calibration, the tree run,
the DoS column) and the stream job (calibration, the stream run), one run each. The plan is
defined once (`harness/aggregate.py`), and the verdict requires exactly its parts, from one harness
commit and one season: a missing, duplicated or mismatched part, or parts from different commits,
make the result `ERROR` and not comparable; a part the entry failed makes it `REJECT` (RF-M1). Each
job measures its own `T_triv,best` and service throughput, and a result whose jobs ran on different
CPU models is marked `mixed_cpu` and never used for a paired record comparison. Every job ends
within 30 minutes, the caps inside it nested (§3.4).

**The submission pipeline and the organiser's CI are separate** (V4-A9). The evaluation
(`evaluate.yml`, called from the submissions repository) runs only what is about the entry: the
source rule, its build, the comparator, the gate, the badge build, the prover's build and runs, the
root and stream checks, the statement canaries, the DoS column, the score. It also builds or
restores the environment the entry runs in, which is not a check: the package tree, with its
olean-manifest check per evaluation (it guards what the entry builds against), the comparator, the
service, `T_triv,best` (the cap needs it) and the service's throughput (informational, a few
seconds). Every check whose subject is organiser code (the contract's `acc` before the entry's `V`:
the file parser, the trace digest, the signature; the service, the sandbox, the badge template, the
compiled extractor interpreter, the harness itself) runs in the core repository's `ci.yml`, once per
harness commit, and never in an evaluation.

**Measured** (CI runs 39935079265, 39940607844, 39952420263): the core's Lean job, which builds
the contract, library and controls, takes 8 min 53 s cold, 4 min 12 s and 7 min 21 s with the
package cache. On the development VM the witness-sending entry's certificate job took 2 min 2 s with
v4's byte-identical rebuild and takes 1 min 33 s with the one build of V4-A9 (build 25 s,
comparator 34 s; `logs/trim/cert-ws-before.log`, `cert-ws-after.log`). The baseline's certificate
job on the same VM (32 vCPU): the comparator 354–372 s and 3.7 GB, of which its `Solution` build
147 s and the kernel phase about 144 s, then the rebuild V4-A9 removes 173 s, the gate 18 s, the
badge 16 s (submissions repository, branch `v4/flock-baseline`, `logs/f3/cert-lean.log` and
`docs/v4/flock-baseline/stages/F4-final-harness-RESULT.md`). The 30-minute caps (§3.6) are the
user's rule; no real entry has been run against them on a 4-vCPU runner (§6.2).

**The anchor** (V4-A1, C-M1). A result is a JSON file plus a job log; without an anchor the
leaderboard would trust the submitter, who controls a pull request's own workflow file. So:

- Evaluation runs only from an organiser-controlled workflow: the submissions repository's
  `evaluate-entry.yml` (a template, `harness/ci-template/`, installed there with the pin), from its
  default branch, triggered by `pull_request_target` with the `evaluate` label or by
  `workflow_dispatch`, calls the core's reusable `evaluate.yml` at a pinned commit. Permissions are
  minimal, no secrets are present, and the entry is fetched by SHA with plain git (never
  `actions/checkout` of the fork). Its bytes are executed **only inside the sandbox**, the Lean
  build, gate and badge build included: `lake build` runs the submission's lakefile and elaborates
  its files, which is code execution.
- A separate `attest` job, which runs no entry code, signs the result JSON (verdict, `vk`, CPU
  model, runner image, harness commit, service, badge and prover hashes) with a GitHub artifact
  attestation. A record counts only if `harness/verify-record.sh RESULT.json` passes: it runs
  `gh attestation verify --owner scaraven --signer-workflow
  scaraven/recursion.fast/.github/workflows/evaluate.yml --deny-self-hosted-runners`, which rejects
  a fork's copy of the workflow, then requires the certificate's signer digest (the commit the
  reusable workflow ran at) to equal the result's `harness_commit`, since `--signer-workflow`
  matches the path and not the ref (RF-m1), and finally the verdict ACCEPT and comparable. It is
  untested: neither the evaluation nor an attestation has run on GitHub yet (§2.8), and the
  development VM's `gh` 2.46 has no `attestation` command.
- GitHub's approval of first-time contributors' workflows is **compute admission**, not a verdict.

### 3.2 The service (V4-2, V4-3, V4-A4, V4-A5)

**What it is.** One process per timed run (the tree run, the stream run; and the calibration's),
outside the prover's sandbox, reachable from the prover only through a Unix socket whose path is in
`RF_ORACLE`.
Operations (stage B's `service/PROTOCOL.md`, normative for provers):

| Op | Request | Response |
|---|---|---|
| `QUERY` | a batch of byte strings | their answers `PRF_k(qᵢ)`, BLAKE2s-256 keyed by `k` (RFC 7693 keyed mode, 32-byte key, no tag on queries) |
| `SIGN` | a batch of byte strings `q₀ … q_{m−1}` | the answers, recomputed, and a signature on `traceDigest [(q₀, a₀), …]` with the next unused index |
| `VK` | — | `vk`, the Merkle root of the `2^16` one-time public keys (also written to `DIR/vk.hex`) |

Every request is a batch so a prover amortises the round trip; one connection per prover thread
hashes in parallel. **Caps**, each refused as an error that aborts the proof as a reject: a query of
at most `2^20` bytes (`queryCap`); a request body of at most 16 MiB; at most `2^18` items per
`QUERY` and `2^16` per `SIGN`; at most 32 connections, so that the worst case (about 1.3 GiB)
fits the service's 2 GiB cgroup; `2^16` signatures per lifetime.

**Lifecycle and key handling.** `k` and the signing seed are independent `getrandom` draws, never
written to disk, destroyed at exit; chain starts are derived under tag `0x53` (§2.5). The signature
index is taken by one atomic step before the signature is computed and never reused, even if the
request then fails. A crash or restart is a new key and aborts the run.

**No memoisation** (C-m2). The service persists across the stream's otherwise stateless
requests; a cache of answers would be a timing channel between them, so every answer is computed
when asked. The visible 16-bit signature index is the one channel left, harmless at that width.
**`SIGN` re-evaluates every query** (C-m4): one extra PRF per query of the verifier's trace, small
against the Merkle traffic.

**Placement and memory.** The service computes on the same CPUs as the prover: outside the prover's
CPU budget it would be a free co-processor of billions of compressions (RR-8). The prover's
`oom_score_adj` is raised so that under memory pressure the kernel kills the prover, never the
service, and the kill reason is recorded (C-m4). Memory is capped in two cgroups, 11 GB for the
prover's sandbox and 2 GB for the service (13 GB together, V4-13's total), so a prover cannot make
the OOM killer pick the service and the service's buffers do not count against the prover. A dead
service aborts the run as the entry's failure; it is never restarted.

**Tests** (**measured**, stage B RESULT §4): 89 checks against Python `hashlib.blake2s(key=…)` and
an independent Python WOTS on both SIMD paths, the empty message included (its only block is the
key block, so a cached-key fast path does not apply, [CGH] §9); every refused cap; 32 concurrent
connections; fresh keys per service; exactly `2^16` signatures, then `EXHAUSTED`. The service's
`vk` and signatures are **byte-identical to stage A's compiled Lean signer**, whose `SigOkF`
accepts them (`logs/service/test_lean_signer.log`), on the development VM and on a GitHub runner.

**Speed** (**measured** on the development VM, after golf GB; stage B RESULT §3, GB §1): a round
trip of about 31 µs; with batches of 4,096 queries of 64 bytes, 7.4 M calls/s on one connection and
125 M on 32 (25 M on 4 CPUs before the golf); 39 ns per 64-byte block in a batch (AVX2, 8 lanes);
key generation of the `2^16` one-time keys 0.5 s on four threads. Batching is what makes the
service cheap: one call per round trip runs at about 30 k calls/s. The runner's own figures are the
calibration column of each result.

### 3.3 The sandbox and the assembly prover (V4-9, V4-A6)

**The prover is x86-64 assembly** (P4, the user's request): one or more `prover/*.s` files in GNU `as`
syntax (AT&T or `.intel_syntax`), linked with the runner image's `gcc -static -pthread … -lm`
(static glibc, libgcc), no other build input. The **reference toolchain is part of the rule**
(`harness/PROVER.md` §1): GitHub's `ubuntu-24.04` image, GCC 13.3, binutils 2.42, glibc 2.39; CI
assembles every committed `.s` fixture with it first, and `harness/tools/asm-compat.py` (an
untrusted helper) rewrites a newer compiler's output for it. Source in any language may sit beside
it for readers,
unbuilt. Agents write in any language and submit the compiler's output. Soundness never depends on
the prover: `acc` is the only check. The Lean `P` stays, since completeness is a theorem about it
(P5).

**Built inside the sandbox** (C-m7): `as` honours `.incbin` and `.include`, so a build outside it
could embed any file the job user can read. The image version, `gcc` and `as` versions and the
binary's hash are recorded; an incumbent for a paired comparison is rebuilt from its own `.s` in the
same job.

**Running it.** `PROVER tree DIR`, `PROVER leaf DIR`, `PROVER node DIR` (v3 and [CM]), with
`DIR/vk.hex` and `RF_ORACLE`. Every output is a signed-proof file (stage B's `harness/FORMAT.md`,
normative): `|π| ‖ π ‖ m ‖ (|qᵢ| ‖ qᵢ ‖ aᵢ)ᵢ<m ‖ idx ‖ ots₀…ots₁₃₂ ‖ path₀…path₁₅`, every number a
little-endian `u64`, read strictly (a file that is not exactly one encoding is rejected).
The binary may dispatch on `cpuid`; a `SIGILL` fails the run.

**The sandbox** (stage B RESULT §5.1; 45 checks against a hostile prover pass,
`logs/harness/test_sandbox.log`). Every untrusted process, the prover, its build, the entry's Lean
build and the badge, runs under `bubblewrap`: its own user and pid namespaces, no network, no
capabilities, an empty environment, a read-only root holding only what it needs, a seccomp filter
(`ptrace`, `process_vm_*`, `bpf`, `perf_event_open`, `userfaultfd`, `io_uring`, keyrings, mounts,
namespaces), a memory cap on the whole process tree, and death with its parent. The namespaces keep
the prover out of the service's memory (the brief asked for a separate uid; stage B needs no system
user); the filter is depth. The workflow relaxes Ubuntu 24.04's AppArmor restriction on user
namespaces for the job.

### 3.4 One evaluation, step by step

| # | Step | Checked or measured | Service |
|---|---|---|---|
| 0 | setup jobs | the organiser's environment, cached per core commit (§3.1); no entry code | none |
| 1 | certificate job | source rule, the one build, comparator, gate, badge build (§3.1) | none |
| 2 | build | the assembly prover, in the sandbox, hashes recorded (each benchmark job) | none |
| 3 | calibration | `T_triv,best`; the service's calls/s and compressions/s (§3.5; each benchmark job) | a calibration instance |
| 4 | **tree** (one run) | fresh starts per evaluation; `PROVER tree DIR`; **timed**: `T_tree`; only `root.bin` is read | a fresh lifetime: every `QUERY` and `SIGN` |
| 5 | root check | compiled `acc` on (`treeRoot`, root signed proof) under that run's `vk`, within `T_V` (§3.5) | none: offline |
| 6 | **stream** (one run) | `M + 1` leaves and `M` merges, a fresh process each, ready handshake, **timed**: `t_link`; every output checked with `acc` within `T_V` | a fresh lifetime, shared by its requests |
| 7 | statement canaries | the root against its statement with one bit flipped; the first 2 leaf and 2 node outputs of the stream against that and against their sibling's statement: each must be rejected (C15) | none |
| 8 | DoS | `acc` on 100 random and mutated signed proofs of the root's statement (in turn: random bytes; random `π` with the root's trace and signature; the root's `π` with 1–8 bits flipped; the root's file with 1–8 bits flipped, cut to a random prefix in 30% of cases; none extends the file). Each input may take at most 10 × `T_V`, the column at most 180 s in all; a breach or a crash of the checker fails the run (REJECT), and the slow input is kept and named; an accepted input is recorded, not failed (V4-A9) | none |
| 9 | result | JSON with every number of §3.5, attested | — |

Steps 2–5, 7 and 8 are the tree job, steps 2, 3, 6 and 7 the stream job; they run in parallel.

**Every job within 30 minutes** (V4-A9). A job killed at its limit is a missing part and makes the
verdict ERROR, so the caps the entry controls are nested inside each job with room for its fixed
steps: an entry that is slow or hangs fails a cap and is REJECTed with the reason (a kernel over its
cap leaves the certificate unchecked, Q12, as before). The worst case of each job, with the caps of
§3.6 and the organiser's own steps as measured or estimated:

| Job | Entry-capped steps (worst case) | Organiser steps | Bound |
|---|---|---|---|
| setup (no entry code) | — | on a cold miss: an earlier commit's cache restore (about 45 s, **estimate**), `lake exe cache get` ≤ 240 s, `org-setup.sh` steps 1–4 ≤ 1,080 s (their timeouts), the save and its check (about 2 min, **estimate**): 22 min of timeouts and about 3 min of transfers. **Measured**: `cache get` 39 s warm and 139 s cold, `org-setup.sh` 237 s warm and 270 s cold (CI runs 39966237935, 39935079265, before CompPoly and `Mathlib.Tactic` joined), the `Mathlib.Tactic` objects 221 s on 4 cores of the development VM. On a hit: nothing | about 25 of 30 min |
| setup-tools (no entry code) | — | on a miss: the comparator ≤ 240 s (14 s **measured**; 540 s with nanoda), the service ≤ 120 s (12–17 s **measured**), two small saves | 6 of 30 min |
| certificate | build 600 s + kernel 600 s + gate 120 s + badge 180 s = 1,500 s (25 min) | checkout and runner setup 10 s (8 s **measured**); elan 1 s (**measured**); the two cache restores about 45 s (**estimate**: the 2.7 GB package-tree cache restores in 35 s, **measured**, and the organiser build and objects add some hundreds of MB); the Lean toolchain 29 s (**measured**, CI run 39966237935); fetch, render, source rule about 5 s; two olean-manifest checks over 7.58 GB, 15.5 s each on 4 cores with a warm page cache (**measured**, `logs/trim-fix/manifest-check-time.log`), allowed 40 s each cold; `lake env`, the upload about 10 s: about 3 min | 28 of 30 min; even at twice the restore estimate the job ends inside 30 |
| benchmark, tree | prover build 300 s + setup 300 s + tree 600 s + root check ≤ 150 s (up to three badge runs of `2 · verify_s + 30` s) + its canary ≤ 40 s + DoS 180 s = 1,570 s (26.2 min) | calibration (three chain-checker runs of 1.8 s, **measured**; the service probes about 5 s), the instance's digests (2.2 s, **measured** by the review), three service lifetimes: under 30 s | 26.7 min, inside the part's 28 min (`evaluate.py` `PART_S`), the job's fixed steps (about 30 s) and upload inside 30 |
| benchmark, stream | prover build 300 s + setup 300 s + the stream 960 s, a hard wall deadline over every request, check and canary from its first request (§3.6) = 1,560 s (26 min) | calibration, the stream's digests (about 3 s): under 30 s | 26.5 min, inside 28, inside 30 |
| plan, attest | — | data only | 10 min each |

The core CI's jobs (`ci.yml`) are bounded the same way: every step has a timeout, their sums are
22–26 min per job, and the jobs took 1.4–9.3 min on a runner (CI run 39966237935).

The runner never passes a digest to `tree` and never a start to `node`; leaf and root digests are
the runner's (`treeRoot`, the contract's specification of it).

### 3.5 What is measured, and how

- **`T_tree`**: wall time of one `PROVER tree` process proving the whole tree, one run (V4-A9; no
  repeats, no median). Anything goes inside: flattening, proof of parent, bundling near the root,
  grinding. Only the root is read and checked; inner proofs, if written, are ignored.
- **The stream** ([CM] §3.3, CM-4, CM-6): link `i` draws a fresh start of length `n_f`; a leaf
  request proves it and a merge request folds it into the running proof (`π_i` proves
  `nodeStmt c_{i−1} d_i`), or one 1→1 request does both. Every request is a fresh process whose
  start-up is untimed (ready handshake); the clock runs from the inputs to the output; one start per
  process, released one at a time. As the runner computes it (`harness/rfh/bench.py`, [CM] §3.3),
  `t_leaf` is the sum of the `M + 1` leaf times over `M`, `t_merge` the sum of the `M` merge times
  over `M`, and `t_link = t_leaf + t_merge`, from the one stream run (V4-A9). Under the SROM a link
  also pays its `SIGN` calls, on the clock.
- **`T_V`** (V4-12, C6): one `acc` check (parse plus `accF`, timed in the badge process) must take
  at most `T_triv,best / R`, `R = 10`, measured as the **wall time of the check pinned to one core**
  (an upper bound on its CPU time); the cap's calibration is measured the same way. A per-check CPU
  time would need FFI in the badge or one 140 MB process per check. Every timed batch starts with an
  untimed warm-up check; a sample above the cap is measured again, up to `checker_runs` times, and
  its best time is compared, the statistic of the cap (RB-M1). `T_triv,best` is the best of
  `checker_runs` runs, where
  it is measured **in the same job** by the organiser's compiled-Lean chain checker, interleaving
  8 chains, over the tree's chains (`2^24` compressions). It applies to the root and every
  stream output. **Measured**: 1.776–1.785 s on a GitHub runner, about 106 ns per
  compression, so `T_V` ≈ 178 ms (orchestrator's run); 3.10 s on the development VM
  (`logs/harness/chaincheck-season.log`). The trusted part of `acc` is small: the word-level twin
  takes 0.23 ms per `SigOk` and 72 ms for the trace digest of `2^16` queries of 100 bytes, and a
  whole `acc` on that trace 135–155 ms on the development VM (`logs/harness/accprobe.log`), so a
  verifier that really asks `2^16` long queries cannot meet the cap; honest roots ask about
  5,000–15,000. How `T_V` treats binary-field verifiers is open (§6.2, Q11).
- **The service calibration column** (C-m8): the service's measured calls/s and compressions/s on
  that runner, published beside every score like `T_triv,best`. Every Merkle hash of every
  commitment is a service call, about `10^8` per tree (**estimate**, [RD] §4.8), so `T_tree` and
  `t_leaf` measure the organiser's IPC and SIMD BLAKE2s as well as the entry. The organiser's
  hashing speed is part of the rules; a faster service in a later season moves every score, and not
  uniformly. The benefit: entries no longer compete on Merkle-hashing craft, only on proving.
- **Recorded with every result**: CPU model, runner image version, `gcc`/`as` versions, the prover
  binary's hash, the harness commit, the service binary's hash, `vk`, the kernels that ran.
- **Records**: paired ABBA confirmation within one job (5 pairs, median ratio ≤ 0.97, v3 §8.4),
  the incumbent rebuilt in the same job; cross-model results are never compared unpaired. This is
  what decides a record, so the score itself needs no repeats (V4-A9).

### 3.6 The score, season 1, and provisional entries

```
S = T_tree + K · t_link          (seconds; lower is better)
```

`T_tree` is the chain term (any method), `t_link` the recursion term, `K` one published number per
season, recomputed from the leading entry so that recursion is a stated minority share of the
leader's score ([CM] §3.4). The 100 ms and 200 ms per-merge targets are reference lines, not part
of `S` (CM-7).

| Parameter | Season 1 | Smoke (CI) | Source |
|---|---|---|---|
| tree depth `r`; leaves | 6; 64 leaves, 63 nodes | 2 | V4-11 |
| chain length `n` | `2^18` (`2^24` compressions per tree) | 16 | V4-11 |
| stream: links `M`, chain length `n_f` | 256, `2^16` | 4, 16 | V4-11, CM-5, V4-A9 |
| `K` | 20, provisional | 20 | V4-10, CM-2 |
| `T_V` ratio `R` | 10, enforced | 10, reported only (the trivial check takes microseconds) | V4-12, CM-8 |
| runs (tree, stream) | 1, 1; no medians | 1, 1 | V4-A9 |
| statement canaries per kind; DoS proofs | 2; 100 | 2; 64 | V4-A9 |
| certificate caps: the entry's build, the kernel, the gate, the badge build | 600 s, 600 s, 120 s, 180 s | same | V4-A9 |
| benchmark caps: prover build, prover setup, tree run, stream request, the stream, one `acc` check, DoS column | 300 s, 300 s, 600 s, 60 s, 960 s (900 s for the entry), 10 s, 180 s (10 × `T_V` per input) | 300 s, 300 s, 120 s, 60 s, 300 s, 10 s, 180 s | V4-A9, [CM] §3.5 |
| `proofCap`, `queryCap`, `qV` | 1 MiB, `2^20` B, `≤ 2^16` | same | V4-13, V4-A3 |
| signed-proof file the runner reads | ≤ 64 MiB | same | V4-13 |
| `errorCap`, `completenessCap`, `logCap` | `2^-120`, `2^-40`, `2^96` | same | V4-13, V4-A9 |
| signatures per service lifetime | `2^16` | same | V4-3 |
| memory cgroups | prover 11 GB, service 2 GB (13 GB together), badge 4 GB | same | V4-13 |
| job limit | 30 min | 30 min | V4-A9 (the runner allows 6 h, P3) |

The table is a selection of `harness/season.toml` and `harness/smoke.toml`, which also fix the
check batching and the number of calibration runs; the season benchmark runs as two parallel jobs
(§3.1), the smoke as one.

**What the badge cap pays for** (review D-trim m-1). The badge build links the object code of every
module of `Solution`'s import closure. The `setup` job precompiles those of `RecursionFast`, the
CompPoly roots and `Mathlib.Tactic` (4,716 modules, 2,825 of Mathlib's 8,530); every other module
the entry imports, its own included, is compiled inside `badge_s = 180 s`, at about 4.8 objects per
second on 4 cores (**measured** on the development VM: 1,063 objects in 221 s,
`logs/trim-fix/objects-mathlib-tactic-4cores.log`), so about 860 such modules fit (**estimate** for
a runner). Importing all of Mathlib (about 5,700 more) does not fit.

**What the stream's cap holds** (review D-trim m-5). `stream_s` is wall time from the stream's
first request: 960 s, of which 60 s allow for the organiser's overhead inside it (about 30 s
**measured**: a request's sandbox start, staging, kill and read at most 50 ms, 513 times; a badge
batch's start at most 0.2 s, about 20 times; `logs/trim-fix/stream-overhead.log`). The entry's
900 s hold its 513 requests from their process's start, its own start-up to `ready` included, and
the checks of its outputs. With every check at `T_V` ≈ 178 ms (about 530 checks, warm-ups included,
about 95 s), that leaves **about 3.1 s per link**, a leaf and a merge with their start-ups, at the
season shape; an entry slower than that is REJECTed at the cap, not scored.

**The stream's tail at `M = 256`** (CM-R2, **estimate**). The last merges of the stream can bundle
or leave chain hashing to the verifier and never pay: at most `c − 1` of them escape, where `c` is
the number of `2^16`-step chains a verifier can check natively within `T_V`. `T_V` is `T_triv,best
/ R` and `T_triv,best` checks `2^24` compressions with the same chain checker, so
`c ≈ 2^24 / (R · n_f) ≈ 25` at `R = 10`, whatever the machine. The escaped share is therefore at
most about `24 / 256 ≈ 9.4%` of the stream's merges at `M = 256` (it was about 4.7% at `M = 512`).

**Why this shape** (V4-11). The cost model's long shape (`r = 4`, `n = 2^20`) does not fit 16 GB
for a Flock-class prover (**estimate**); `r = 6`, `n = 2^18` keeps its total chain work (`2^24`
compressions) and has more leaves than cores. **Why `K = 20`**: the cost model's own illustration
(`p = 15%` for a leader at leanVM's published 0.394 s step on an M4 Max). `K` is a ratio of times,
so a uniformly slower runner leaves it unchanged; but it was computed for the long shape, whose tree
has 15 nodes against season 1's 63, so it is provisional until a leader exists on CI.

**Provisional entries** (V4-15, C-m13). An entry whose Lean builds but whose certificate does not
check (a `sorry`, a failed gate) may be benchmarked: it is published as PROVISIONAL, marked
uncomparable, and never ranked or recorded. The source rule, the gate's other rules and the sandbox
stay mandatory, and a maintainer approves the run.

**The first certified entry, and what it shows** (as reported by the baseline team, stage F; logs
in the submissions repository, branch `v4/flock-baseline`). `spartan-srom` ports v3's
`spartan-chain` (Spartan + Ligero over GF(2^64)) to v4, with an assembly prover. It is certified
(the comparator with the Lean kernel: 372 s, 3.7 GB, `logs/f3/cert-lean.log`) and ACCEPTed at the
smoke shape (`logs/f3/bench-smoke.log`), with harness workarounds for Q2 (CompPoly's modules
missing from the organiser's roots) and Q7 (the gate tree's rebuild), both since fixed (`5b2b591`):
`T_tree` 0.896 s; the root's `acc` 978.8 ms, on a bundle of the four leaf proofs (`π` 603,812 B,
14,132 trace entries); `t_leaf` 0.251 s, `t_merge` 0.037 s, `S` 6.67 s. It is not recursive: a node
bundles its leaves' proofs, so the frontier is set by the caps (`logs/f3/frontier-table.txt`):

| What stops it | Where |
|---|---|
| `proofCap` (1 MiB) on a bundle of leaf proofs | rejected at `r = 0, n = 8,192`; `r = 1, n = 2,048`; `r = 2, n = 256`; `r = 3, n = 8` |
| memory: a stream leaf of `2^16` steps | 15.1 GiB peak, above the 11 GB prover cap (F2 RESULT §4, unit as corrected by its review F2-m3) |
| `T_V` at the season shape, about 0.18–0.3 s | its compiled `acc` takes 0.20 s for one leaf proof and 0.45–0.50 s for a bundle of two (F1 RESULT, `L/run/verify-final.log`) |

At the smoke shape `T_V` is reported, not enforced: the trivial check there takes about 0.1 ms, so
any SNARK would fail it. The ranked path is therefore exercised end to end only at the smoke shape,
and the season shape needs a recursive entry with a verifier faster than this one's (§4.3).

### 3.7 Consequences that bite

Found by building entries against the rules; the submissions repository's rulebook (`AGENTS.md`)
carries the same list.

1. **The assembly must be accepted by the image's `as`.** `ubuntu-24.04` ships binutils 2.42; a
   `.s` from a newer GCC with `.base64` directives (binutils 2.43 and later) does not assemble
   there, which is how the organiser's own toy prover failed on the runner (RF-M2). Generate the
   assembly with the reference toolchain (§3.3), or pass it through `harness/tools/asm-compat.py`.
2. **A `Submission` must be computable** (Q4): gate rule 4 requires `V`, `P` and `ext` compiled
   (the badge itself runs only `V` since V4-A9), and a noncomputable `ε : ℝ≥0` literal fails the
   build; write it as a cast from `ℚ≥0`.
3. **Compiled `ByteArray.data` copies the array** (Q4): a parser reading bytes through it is
   quadratic (88 s on 539 KB for a v3-style parser); use `ByteArray.get!` or the library's twins.
4. **Every query is at most `queryCap = 2^20` bytes** (Q15, a consequence of V4-A3): v3's Ligero
   hashes a whole column as one Merkle-leaf query, above 1 MiB from `n = 2^17`; a √-size commitment
   must split its columns (a tree, or several queries). The service refuses a longer query.
5. **`acc` hashes the whole trace inside `T_V`**: `2^16` queries of 100 bytes cost 135–155 ms of
   `acc` on the development VM, close to the season cap; size the verifier's queries for it.
6. **One `SIGN` per proof, and it re-evaluates every query**; a `SIGN` of zero queries signs the
   empty trace, which every query-free child (a clear leaf) can share.
7. **A node witness must fit `outCap = 2^24` words** (C-m11): with both child proofs at `proofCap`,
   the two traces may hold, for example, `2^16` queries of up to 960 bytes each; a node beyond that
   cannot be extracted and is not certifiable.

---

## 4. Incentives and residual risks

### 4.1 The cost model's table under the SROM

The SROM changes what a record certifies, not which strategy pays. **Unchanged** from [CM] §5:
full witness-sending fails `T_V`; partial witness-sending at the root keeps up to `1/R` of the chain
work (CM-R7); concatenating or bundling leaf proofs is bounded by `T_V` and `proofCap` (the
baseline's frontier, §3.6, measures exactly this); flattening, proof of parent and bundling inside
the tree are allowed and the stream prices recursion; the stream's protocol stops folding from
memory and preparation off the clock, and bounds CM-R1–R3; grinding is on the clock. What changes:

| Strategy | Under [CM] | Under the SROM |
|---|---|---|
| the service as a free co-processor (CM-R6) | the service in the prover's cgroup | same CPUs as the prover (§3.2); its speed is published |
| state between stream requests | none: a fresh process each | the service persists across them but memoises nothing |
| the oracle backdoor and its disguises; the liveness mirror | open in v3 | closed by the deployment (paper, §2.3) |
| a verifier that accepts on a signature, on `sk`, or on a signed answer | — | uncertifiable (§2.2) |
| key in the proof, replay across runs, key reuse | — | fresh keys per lifetime, held by a process outside the prover's namespaces |
| grinding | allowed, on the clock | unchanged |
| sharing one signature between two children (C-M3 item 3) | — | possible only through dummy queries counted in `qV`: a legitimate optimisation |
| the 16-bit signature index as a channel between stream requests | — | harmless at that width (§3.2) |

### 4.2 The in-circuit cost of the SROM (for zkVM engineers)

Per child, a node circuit under v3 evaluated every oracle query of the child's verifier as public
BLAKE2s of `0x52 ‖ q`. Under the SROM it instead (**estimate**, arithmetic on §1.3's layouts):

- **hashes the child's trace**: an item `enc64 |q| ‖ q ‖ a` per query, absorbed in one streaming
  hash. For a 64-byte Merkle preimage that is 104 bytes, about 1.6 compressions, against 1 for an
  untagged public-hash Merkle step and 2 for v3's tagged 65-byte input. The answers are witness
  values, never evaluated;
- **checks one signature**: the chain walks take `Σ (3 − dᵢ)` steps, about 200 for a random digest
  (192 for the message digits, about 8 for the checksum) and at most 396; the key leaf takes 67
  compressions and the path 32. So about 300 compressions on average, at most 495, and 498 for a
  fixed circuit that always takes three steps per chain with selectors;
- **walks the trace in order** (`runSeq`), with no lookup argument.

**Per child, in total**: about 104 + 300 ≈ 400 compressions for 64 queries of 64 bytes, and about
6,660 + 300 ≈ 7,000 for 4,096. The trace a node circuit walks is at most `qV · (queryCap + 40)`
bytes and in practice `Σ (|qᵢ| + 40)`: 426 KB for 4,096 queries of 64 bytes. Two children may share
one signed trace through dummy queries, so one signature per node is possible (V4-A3); per-child
cost statements are upper bounds. For scale, the exploration's estimate for the attested variant D4
was 1.09× a public-hash recursion step for a spartan-chain child ([RD] §7.3), and D3 +0.5–12% per
child for the signature. Whether an honest recursive entry fits `proofCap` under v4 has not been
re-sized (C5, C unsettled 4).

### 4.3 Residual risks

- **The service is accept-all-critical.** One signed answer that is not `PRF_k(q)` lets a prover
  pick its challenges; an index used twice lets anyone forge. Tested against the Lean specification,
  not proved (trust item 7).
- **The service's speed is in every score** (C-m8, CM-R6): published, but a season-2 service moves
  scores non-uniformly. If traffic dominates, W5 (public Merkle hashing, attested Fiat–Shamir
  answers only) is the recorded optimisation, at the price of an extractability heuristic (V4-14).
- **Heterogeneous runners** (P3): only paired comparisons are meaningful; `T_V` self-calibrates
  but a single-core time does not remove SIMD (C6, H-m10).
- **No entry runs the season-1 shape** (C-m10): the certified baseline's frontier (§3.6) stops far
  below it on `proofCap`, memory and `T_V`. The season shape needs a recursive entry with a compiled
  verifier several times faster; until one exists, the first ranked shape should be the one the
  first certified recursive entry can run.
- **Nothing has run end to end on GitHub** (§2.8): every end-to-end claim is from the development
  VM until the evaluation workflow and its attestations run.
- **`T_V` is biased against binary-field verifiers** (Q11, §6.2): the chain checker compiles to
  fast word code, while Lean has no carry-less multiply, so a GF(2^k) verifier pays a software
  `clmul` on the same clock. This is against V3-1 ("binary fields must not be disadvantaged").
- **Crafted inputs can make `acc` slow** (C9; the baseline's review F1-M2): a 970 KB node built from
  public parts took the baseline's compiled `acc` 68–183 s against 0.43 s for its honest root, above
  the then `verify_s = 60 s`. The DoS column fails a run whose input takes more than 10 × `T_V`
  (§3.4), but it draws 100 random mutations and does not search for such inputs; a crafted-input
  column is a follow-up (FB-5, §6.3).
- **The 30-minute jobs bind entries** (V4-A9): an entry's Lean must build within 10 min and check
  within 10 min on a 4-vCPU runner, and its prover must build, set up and prove the tree within
  their caps. The baseline's build took 147 s and its kernel phase about 144 s on the 32-vCPU
  development VM (§3.1); on a runner neither has been measured. A larger runner for the
  certificate job is the alternative (§6.2).
- **One kernel on CI** (Q5, §2.7): no independent re-check of the certificate.
- **The baseline's FB-7, FB-8** (§6.3): the service tax on a recursion step and the cost of the
  assembly-only build. FB-9 (`errorCap` against GF(2^128)) is answered by `errorCap = 2^-120`
  (V4-A9).
- **CM-R1 … R8** of the cost model, unchanged.

### 4.4 What each rule is for (V4-A9)

A rule stays if it serves one of two goals: (a) entries are valid, sound verifier designs; (b)
proving is honest and fast, and recursion is priced. What served neither was cut (c), the user's
decisions of 2026-10-26.

**(a) Vital for valid verifiers.**

| Rule | What breaks without it |
|---|---|
| the relation and `acc`: exact in-order replay of the trace, `\|tr\| ≤ qV`, the 1 MiB caps | witnesses are unbounded, so no recursive design is complete (C-M3), and the trace digest is ambiguous |
| textbook single-output knowledge soundness at `errorCap = 2^-120` per query, `logCap = 2^96` (V4-A10); the potential is a library route | no soundness; the run's bound `N·(Q + qV)·ε` is about `2^-81` (§2.4) |
| the efficient straight-line extractor: `Computes` within the budget `B t` | an accept-all verifier is knowledge-sound when every statement has a witness (`acceptAll_ks_iff`), and the tree's members are not extracted from the run's log (§2.4) |
| completeness for every witness, `δ ≤ 2^-40` | reject-all verifiers, and verifiers that accept only the benchmark's shapes, are certified |
| the certificate for every `vk` | it is proved before the key exists, so no verifier can lean on a signature (§2.2) |
| proof hygiene: the kernel check, the axiom audit, the gate's rules, the source rule | the certificate is not a proof (`sorry`, an axiom, elaboration-time code, a code-changing attribute) |
| the badge bound to the checked code | the code that checks proofs is not the verifier the kernel certified; the binding is vital, how it is made is not (one build since V4-A9, §3.1) |

**(b) Vital for honest fast proving and priced recursion.**

| Rule | What breaks without it |
|---|---|
| the signed oracle, a fresh secret key per run, unreachable from the sandbox | with a public oracle v3's certified backdoor is a scoring exploit, a magic root proof with no chain work (O-25); without fresh keys proofs and signatures replay across runs |
| fresh random starts per evaluation; the runner's own root and digests | the instance is precomputed, or the prover names the statement it proves |
| `T_V` relative to the same job's chain checker | witness-sending: the verifier redoes the chain work the prover skips (CM-R7 bounds the rest) |
| `proofCap` | bundling the children's proofs in place of recursion |
| the stream: a fresh process per request, one start per process released one at a time, enough links | recursion is unpriced (the tree may be flattened); with state or preparation across links, work leaves the clock |
| the sandbox: no network, no persistent writable path, a memory cap, the service on the prover's CPUs | outside help, state across requests, a free co-processor (RR-8) |
| `S = T_tree + K·t_link` | one wall time cannot weight recursion (CM-1) |
| attested results | the leaderboard trusts the submitter (C-M1) |
| paired comparison for records, the CPU model recorded | heterogeneous runners make unpaired times incomparable (P3) |
| short, nested time limits | a slow entry kills its job, an ERROR instead of its REJECT, and holds runners for hours |

**Changed parameters.** `errorCap` from `2^-128` to `2^-120`: it admits GF(2^128) designs such as
Flock's (a degree-2 sumcheck round costs `2^-127`, a univariate-skip round `126 / 2^128 ≈ 2^-121`;
FB-9), and the run's bound stays negligible (about `2^-90` with the potential's lossless
composition, `2^-81` by the union bound since V4-A10). `completenessCap` from `2^-128` to `2^-40`: a
failure costs only its entrant, and about 640 proofs per evaluation fail a run with probability
about `2^-30.7`. `M` from 512 to 256: the stream fits its 15-minute cap; the tail's share grows to
about 9.4% (§3.6). The time limits (§3.4).

**(c) Removed as fat.**

| Removed | Why |
|---|---|
| three repeats of the tree and of the stream, and their medians | records are decided by the paired comparison anyway (§3.5) |
| the file, trace and signature canaries per entry (`file±1`, `trace-answer`, `trace-query`, `trace-extra`, `sig-ots`, `sig-idx`) | they test organiser code (the parser, `traceDigest`, `SigOk`) before the entry's `V` runs: the core CI runs them once per harness commit |
| the `pi±1` canaries, and "an accepted mutation fails" in the DoS column | non-malleability, which nothing needs and which can reject a sound entry; an accepted DoS input is recorded |
| 1,000 random DoS inputs (now 100) | random inputs never found a slow input; a crafted-input column is the real check (FB-5) |
| the tree's inner proofs and the 16 sampled checks of them | the root's certificate covers its children (§2.4), and the stream prices recursion |
| extractor liveness per entry, and the service's logging mode | `Computes` is kernel; the core CI runs the compiled interpreter on the library's entry |
| the second, byte-identical Lean build | one build serves the comparator, the gate and the badge, and the badge is compiled from the artifacts the kernel's exports were made from (§3.1) |
| `δ ≤ 2^-128` (now `2^-40`) | see the changed parameters |

Two vital rules are under-built and stay open: `T_V` is measured on compiled Lean, which
disadvantages binary fields (Q11, §6.2), and the verifier's time on crafted inputs is not searched
(FB-5).

---

## 5. The trusted base and the trusted runtime

**The contract** (`RecursionFast/Contract/`, code lines by `scripts/loc.py` on the branch):

| File | Code lines | What | Change from v3 |
|---|---:|---|---|
| `Contract.lean` | 9 | reading order | — |
| `Hash/Blake2s.lean` | 68 | RFC 7693 | unchanged |
| `Relation.lean` | 38 | digests, tags, caps, chain, statements, `Trace`, `Sig`, `Signed`, `Wit`, `Rel` | signed children; tags `T W K M` added, `R` removed; `queryCap` |
| `Signature.lean` | 31 | `traceDigest`, WOTS digits, chain, leaf, Merkle path, `SigOk` | new |
| `Oracle.lean` | 24 | `OProg`, `runLog`, `runSeq`, `queries`, `bind` | `runSeq` added, `run` moved to Library |
| `Security.lean` | 28 | `prob` (lazy sampling), `KS` (textbook single-output), `CompleteWithError` (through `prob`), caps | `KS` textbook and `KState`, `failProb` to the Library (V4-A10; 33 lines before); the caps' values (V4-A9: `2^-120`, `2^-40`) |
| `Machine.lean` | 62 | the step-counting word machine | unchanged |
| `Extractor.lean` | 50 | tape, `decodeWit` for signed children, budget, `Computes` | output format |
| `Tree.lean` | 8 | `treeRoot` | unchanged |
| `Certificate.lean` | 32 | `Submission` with `vk`, `acc` (with `\|tr\| ≤ qV`, RA-M2), `Certificate`, `Declared`, `CertificateR` | `Vb`, `blake2sOracle`, `tagRO` deleted |
| **total** | **350** | budget ≤ 500 | v3: 292; 355 before V4-A10 |

What a human must trust it for: that `Rel` and `acc` say what §1.1 says; that `SigOk` and
`traceDigest` hash exactly the bytes of §1.3 (the service and runner are tested against them); that
`KS` and `prob` say what §1.4 says (V4-A10); that v3's other definitions are unchanged but for the
two caps' values (V4-A9). `lake build` is green (1,266 jobs since V4-A10, `logs/ks/lake-build.log`;
before, 1,264, `logs/D-final-build.log`, `logs/trim/lake-build-final.log`; a cold build takes
1 min 56 s to 2 min 55 s on the development VM, `logs/A-fix-build-cold.log`), and the axiom audit
passes on every module (`propext`, `Classical.choice`, `Quot.sound`; `logs/A-fix-axiom-audit.log`,
`logs/trim/axiom-audit.log`, `logs/ks/axiom-audit.log`). The contract imports Lean core and Mathlib
only. By `loc.py`, the Library has 2,275 code lines and 291 theorems, the Controls 2,191 lines and
327 theorems after the stage E-ks fix pass (1,856 and 233, 2,082 and 309 before V4-A10).

**Controls**: every trusted definition has a positive and a negative control (the full table is
stage A RESULT §3). The ones that carry the v4 changes:

| Definition | Positive | Negative |
|---|---|---|
| `Rel`, signed node clause | `node_of_two_leaves` (reference signer, symbolic), `node_of_two_leaves_ref` | `child_other_key`, `child_trace_nonempty`, `node_needs_statement`, `first/second_child_rejected` |
| `runSeq` | `prog_runSeq`, `prog_runLog_of_runSeq` | `prog_runSeq_extra` (exact consumption), `prog_runSeq_short`, `prog_runSeq_wrong_query` |
| `acc` | `acc_leafSigned`, `acc_query_at_cap` | `acc_trace_over_qV`, `acc_two_entries_rejected`, `acc_query_over_cap`, `acc_over_cap`, `acc_changed_answer` |
| `traceDigest`, WOTS, `SigOk` | `traceDigest_kat` (hashlib), `sigOk_sign` (every `sk`), `wotsDigits_dominates` (the checksum) | `traceDigest_changed_answer`, `sigOk_other_key`, `sigOk_key_unique`, `sigOk_ots_length`, `sigOk_path_length` |
| `decodeWit` | `decodeWit_node_kat`, `decodeWit_leaf_kat` | `decodeWit_long_trace`, `decodeWit_short_sig`, `decodeWit_long_proof` |
| `Certificate` with `∀ vk` | `ws_certificate`, `Backdoor.certified`; `sigTrust_ks_unsignable` | `sigTrust_no_certificate`, `sigTrust_certificate_opens` (the adversary holding `sk` wins with probability 1), v3's negatives (`acceptAll_no_certificate` re-proved against the textbook `KS`) |
| `KS`, textbook single-output for normalised adversaries (V4-A10) | `ws_ks`, `twoLucky_ks_exact` (through its potential, at `2^-192`), `queryThenAccept_ks_one` (direct, at `ε = 1`), `Backdoor.certified`; `ws_textbook` (the textbook notion at 0, giving `KS` back through `KSTextbook.ks`) | `acceptAll_wins`, `acceptAll_not_ks` (the adversary that asks nothing wins with probability 1), `queryThenAccept_ks_ge_one` (the verifier's own query is charged), `oneQuery_not_KS` (the query bound); what it does not say: `acceptAll_ks_above_logCap`; what it does not exclude: `lucky_ks` (certified at 0) with `lucky_not_textbook` (textbook error at least `2^-112`) |
| `prob` (V4-A10) | `prob_askGood` (a fresh answer is uniform: exactly `1/2`) | `prob_askTwice` (a repeated query is the table's: probability `0`, not `1 − 2^-256`) |
| `errorCap = 2^-120`, `completenessCap = 2^-40` (V4-A9) | `twoLucky_ks`, `collision_ks` (potentials at the cap), `grind40_complete` (40 nonces: exactly `2^-40`) | `twoLucky_no_bool_kstate`, `collision_no_bool_kstate` (a log of `2^136 + 1` answers), `v24_no_bool_kstate` (`2^72 + 1` answers within the guard), `grind39_not_complete` |
| composition (Library) | `walk_one_leaf`, `walk_two_leaves`, `ws_compose_prob` (the walk escapes with probability 0) | `forgery_trivial`, `compose_exists_free`; `noExt_walk_escaped`, `noExt_escape_prob` (an extractor that returns nothing: the walk escapes, `compose_prob`'s event is certain) |

The Library theorems the badge and the decoder rest on, `Fast.accF_eq` (the badge's `accF` is `acc`)
and `Words.decodeWit_witWords` (every fitting witness can be denoted), are theorems, not controls.

**The trusted runtime** (the groups and rule of stage B RESULT §1.1; recounted by
`logs/ks-fix/loc_runtime.py`, `logs/ks-fix/loc-runtime-after.log`): **3,700 code lines** after the
stage E-ks fix pass (the certificate job records the gate's and the badge's durations and the
kernel's memory peak, +30): the service 948 Rust lines (std only), the runner 1,023, the sandbox
255, the badge main 88, the proof-side order 464, v3's ported tools 697, the calibration generator
161, CI scripts 64. After V4-A9 it was 3,670 (`logs/trim-fix/loc-runtime-after.log`), before V4-A9
3,800 (`logs/trim/loc-runtime-before.log`; stage B counted 3,559 before its final fix pass). The
measurement client `rf-bench` is trusted for nothing a record's soundness rests on (the
calibration column is published, not enforced).

| Component | Trusted for |
|---|---|
| the service (Rust: PRF, signer, wire protocol, caps) | answers are `PRF_k`; signatures only on traces it computed; index uniqueness; key isolation and freshness; no memoisation |
| the runner (Python: sandbox, assembly build, tree, stream, `acc` badge, statement canaries, `T_V` calibration, DoS, score JSON, season file) | the instances, the clock, the caps, running the compiled `acc` on every proof, the published numbers |
| the gate, source rule, axiom audit, manifest (ported from v3) | the badge executables are the kernel-checked terms |
| the CI workflows (the core's reusable evaluation workflow; the submissions repository's caller) | the anchor: untrusted code runs only in the sandbox; the result is attested |

---

## 6. Decisions taken in the user's absence, and open items

### 6.1 The decisions

Each is reversible; the reason is one line. Overrides: the amendments V4-A1 … A10 win over V4-1 …
V4-16 where they differ. V4-A9 (2026-10-26) and V4-A10 (2026-10-27) are the user's own.

| Id | Decision | Reason |
|---|---|---|
| P1 | D3, the SROM, not D4 | offline, stateless checks by the harness and by third parties; no key release, no designated-verifier window; cost one signature check per child |
| V4-1 | v3's KS, completeness, extractor machine and budget verbatim; KS and completeness for every `vk` (KS textbook single-output since V4-A10) | minimal change; `∀ vk` makes a signature-trusting verifier uncertifiable |
| V4-2 | the oracle is keyed BLAKE2s-256 behind a service, fresh key per lifetime; `blake2sOracle`, `tagRO`, `Vb` deleted | CGH needs a public seed |
| V4-3 | a contract-fixed stateful hash-based signature (WOTS `w = 4`, 133 chains, height 16), fresh keys per lifetime, hash-then-sign of the trace | no group; one hash gadget; near-minimal in-circuit cost |
| V4-4 | sequential trace semantics | linear for the harness and in-circuit |
| V4-5 | no trace cap | **withdrawn** by V4-A3 |
| V4-6 | `E` takes no `vk` | it decodes children from the node proof; a design may put `vk` in `π` |
| V4-7 | `acc` is the harness's one check; root proofs are signed proofs | one predicate for relation, harness, third parties |
| V4-8 | composition as a Library theorem returning witnesses, a collision or a forgery | kernel content for CGSY24's argument |
| V4-9 | the prover is x86-64 assembly; the Lean `P` stays | the request; completeness is about `P` |
| V4-10 | `S = T_tree + K·t_link`, `K = 20` provisional, 100/200 ms reference lines, a fresh process per stream request | the cost model as written, with its illustration |
| V4-11 | season 1: `r = 6`, `n = 2^18`; stream `M = 512` (256 since V4-A9), `n_f = 2^16`; smoke `r = 2`, `n = 16`, `M = 4`; one season file | 16 GB runners; the same chain work as the long shape |
| V4-12 | `T_V`: wall time of one `acc` check pinned to one core ≤ `T_triv,best / 10`, the cap measured the same way in the same job | C6; self-calibrating |
| V4-13 | v3's caps kept; memory 13 GB in all (as built: 11 GB prover + 2 GB service, B dev. 1); the two error caps changed by V4-A9 | minimal change |
| V4-14 | no D4+, no W5, no key release; every query, Merkle hashes included, goes to the service | no extractability heuristic |
| V4-15 | PROVISIONAL listing for entries whose certificate does not check | lets real entries be measured; never ranked |
| V4-16 | tree, leaf clause, `chainCap`, statements unchanged; tags `T`, `W`, `K`, `M` added | distinct first bytes for every contract hash |
| V4-A1 | the trust anchor: organiser workflow, sandboxed Lean build, attested results | C-M1 |
| V4-A2 | separate certificate and benchmark jobs; nanoda where it fits | C-M2 |
| V4-A3 | exact trace consumption, `queryCap = 2^20`, conjunct order | C-M3, C-m5 |
| V4-A4 | the signature's theorem stated; independent keys; tagged derivation; atomic index; restart aborts | C-M4 |
| V4-A5 | service: no memoisation, caps, `oom_score_adj`, empty-message vector, calibration column | C-m2, C-m4, C-m8 |
| V4-A6 | assembly built inside the sandbox; image and hashes recorded; seccomp; AppArmor handled | C-m7 |
| V4-A7 | controls: the impossibility, the node clause with the Lean signer, the negatives, the word-level twin | C-m1, C-m3, C-m11, C-m12 |
| V4-A8 | this document states the impossibility, the `vk` caveat, `E` without `vk`, the unrankable season shape, the paper split, the trace-hash cost | C-m6, C-m9, C-m10 |
| V4-A9 | the trim (the user's): every job within 30 min with nested caps and a cached organiser setup; one tree run and one stream run, no medians, two parallel jobs; `M = 256`; no per-entry liveness; per entry only the statement canaries, 2 per kind; the organiser's checks in the core CI only; DoS 100 inputs, failing on time and crashes only; only the root read; one Lean build; `errorCap = 2^-120`, `completenessCap = 2^-40` | keep only what serves valid verifiers or honest, fast, recursion-priced proving (§4.4) |
| V4-A10 | the contract states textbook single-output knowledge soundness in the random-oracle model (`prob`, `KS`); v3's potential (`KState`) is an untrusted library tool, an intermediate artifact of a proof (`KState.ks`); the tree composes by a union bound over the extracted proofs (`Compose.compose_prob`) (the user's, 2026-10-27); the extractor reads the final log, the verifier's answers included: textbook for adversaries that ask the verifier's queries themselves (option B, the user's choice after review E-ks M-1; option A, the adversary's log only, rejected: it breaks the potential's bridge and exceeds the deployment's need); no conjunct `qV ≤ logCap` (the cap `qV ≤ 2^16` excludes the vacuous case, m-1) | the certificate states the standard notion a cryptographer reads and accepts any correct proof technique; cost: about `2^-81` against `2^-90` per composed output (§2.4) |
| RA-M2 | `acc` checks `\|tr\| ≤ qV` (one trusted line) | `KS`'s query bound ranges over oracle functions and does not bound a non-functional trace |
| Q5 | CI checks certificates with the Lean kernel only | nanoda needs more than 16 GB (§2.7) |
| B dev. 1 | the prover isolated by namespaces, not a separate uid; two memory cgroups (11 GB + 2 GB) | no system user needed; the prover cannot make the OOM killer pick the service |
| B §5.4 | the season benchmark split into six jobs (two since V4-A9); mixed CPU models never paired | the 6 h job limit (30 min since V4-A9) |
| B dev. 2, 3 | the badge parses files at byte level; `T_V` times parse plus `accF` in process | the word-level parser costs 0.4 µs per byte; start-up excluded |

### 6.2 Open items

**Not yet done** (the three items the implementation still owes):

1. **The full evaluation on GitHub**: the evaluation workflow, its setup jobs and caches, its two
   benchmark jobs and the attestation have never run; the caller template is not yet installed in
   the submissions repository. (The end-to-end smoke of `ci.yml` ran on a runner before V4-A9: run
   39966237935.)
2. **The 30-minute caps against a real entry on a runner** (C-M2, C10, V4-A9): the entry's build
   and kernel caps (10 min each), the badge cap (3 min, which also compiles any module the entry
   imports beyond the precompiled set, §3.6) and the stream's (about 3.1 s per link) bind entries
   and are a rule; the baseline's figures are from the 32-vCPU development VM (§3.1), and the
   certificate job's fixed steps are partly estimated (§3.4). The user's alternative: a larger
   runner for the certificate job.
3. **`T_V` and binary fields** (Q11). Both sides of `T_V ≤ T_triv,best / R` are compiled Lean, but
   the chain checker's BLAKE2s compiles to fast word code while Lean has no carry-less multiply, so
   a GF(2^k) verifier pays a software `clmul`: the baseline's 2-leaf bundle takes 0.5 s of `acc` and
   one leaf 0.20 s, against a season cap of about 0.18 s on a runner. Options: a contract-fixed
   verified `clmul` primitive on the badge path (a proved-equal word-level `clmul` with an
   `extern`-free fast path is impossible in core Lean today); a per-field calibration; a larger `R`;
   or timing `V` natively against a proved-equal native twin. **`R = 10` stays provisional** until
   this is decided, with the baseline's feedback report.

**Open questions of the design:**

- **The succinct node** (#7, C4, [RD] RO-1): that a decoding node extractor satisfies `final` within
  `B t` is paper; kernel only for children in the clear.
- **Sizing an honest recursive entry under v4** (C5, C unsettled 4); WHIR-class "yes, barely" is
  v3's last estimate. **The first ranked shape** (C-m10): from the first certified recursive entry.
- **The second kernel** (C-M2, Q5): run nanoda on a larger machine, or accept the Lean kernel alone
  (§2.7). The user's decision.
- **Crafted-input DoS** (C9, F1-M2, FB-5): the bounded DoS column of 100 random inputs is the
  first step (§3.4); a crafted-input column is the follow-up.
- **Gate rule 4 still requires `P` and `ext` compiled** (V4-A9): no badge runs them any more, so
  the rule could be relaxed to `V`; relaxing it changes what entries may submit and is the user's.
- **The deployment's whole-run bound at `errorCap = 2^-120`**: about `2^-81` at `2^30` queries for
  the stream's final output, `2^-83` for the tree's root, about `2^-74` for every stream output
  at once (§2.4, V4-A10's union bound; `2^-90` before); a season whose runs ask far more queries,
  or a longer stream, moves it.
- **Keyed BLAKE2s as a named assumption** (C unsettled 1): the alternative wording calls it the
  design's one heuristic, since its only analysis is in an ideal-cipher model.
- **Runner facts** (C unsettled 2, 3): the CPU models, and whether `pclmulqdq` and AVX2 are on every
  one (each job prints `lscpu`).
- **The forgery/collision split in the kernel** (C unsettled 5); **the efficient-extraction domain
  against `logCap`** (O-21, v3); **`K` and the targets on CI**, once a leader exists.
- **The submissions repository**: its branch `v4/flock-baseline` pins `81e1ebf` and carries the v4
  rulebook and the baseline; its `main` still pins `15e4ae5` (v3) until that branch is merged.

### 6.3 Feedback from the first entry

The baseline team's report, `docs/v4/FLOCK-BASELINE-FEEDBACK.md` on the branch `v4/flock-baseline`
of `scaraven/recursion.fast-submissions`, and its dispositions here:

- **FB-1** (no non-recursive entry runs the season shape): (1) publish every entry's frontier as
  unranked columns: adopted in principle, for the next harness stage; (2) an interim partial-stream
  ranking: not adopted, since it suspends G2 and G3; (3) the first ranked shape is the first
  recursive entry's: already adopted (§4.3).
- **FB-2** (`T_V` untestable at small shapes; at node size a √-size PCS misses the season cap by
  about 10×): Q11, open (§6.2).
- **FB-3** (a signed child restates every hashed byte, so every non-recursive entry builds a
  bundle): a Library bundle with `accWith` and `AtMost`, a Library follow-up with no trusted change.
- **FB-4**: the computability rule is documented (§3.7); nanoda's absence is the user's decision Q5,
  on the measured evidence (more than 20.9 GB and 10 min on the baseline's 17.9k-line entry, more
  than 17.6 GB on the witness-sending one); package roots per declared need: a follow-up.
- **FB-5** (a crafted-input column): a follow-up; the bounded DoS column is the first step (§3.4).
- **FB-10** (accept an empty trace without a signature, `tr = [] ∨ SigOk …`; saves 4,776 B per
  query-free child; sound, since an empty trace is trivially genuine): a candidate contract change
  for the user, not applied.
- **FB-7** (the service tax, about 30–100 ms per recursion step, **estimate**) and **FB-8** (the
  assembly-only build's cost in tooling and reviewability): residual risks, argued in the report.
  **FB-9** (`errorCap = 2^-128` per query excludes Flock's GF(2^128) as published): adopted by
  V4-A9, `errorCap = 2^-120`.

---

## 7. Where things are

- **This design's implementation**: branch `v4/srom-rules`. Contract `RecursionFast/Contract/`;
  Library `RecursionFast/Library/` (the potential and its bridge to `KS`, the calculus of `prob`,
  the union bound, witness-sending entry, reference signer, composition, word-level BLAKE2s);
  Controls `RecursionFast/Controls/`; `scripts/` (line count, gate, source rule, axiom audit); the
  service `service/` (`PROTOCOL.md` normative for provers); the runner `harness/` (`FORMAT.md` the
  signed-proof file, `PROVER.md` the prover interface, `season.toml`); `tests/`;
  `.github/workflows/` (`ci.yml`, `evaluate.yml`); stage records
  `docs/v4/stages/A-contract-RESULT.md`, `B-harness-RESULT.md`, `D-trim-RESULT.md` (V4-A9) and
  `E-ks-RESULT.md` (V4-A10).
- **The brief, the reviews and the fix queue**: [`v4/BRIEF.md`](v4/BRIEF.md); the design attack
  [`v4/reviews/C-design-attack.md`](v4/reviews/C-design-attack.md), the stage reviews and golf
  passes (`RA`, `GA`, `RB`, `GB`) and the whole-branch review `R-final-review.md` in
  [`v4/reviews/`](v4/reviews/); [`v4/FIXLIST.md`](v4/FIXLIST.md); the checks against the record in
  [`v4/CHECKS.md`](v4/CHECKS.md).
- **The record it inherits**:
  [V3] [`v3-design-…`](v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md),
  [O25] [`v3-open-problem-…`](v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md),
  [CGH] [`CGH-circumvention-guide-…`](CGH-circumvention-guide-secret-keyed-signed-and-attested-random-oracles-with-reading-list.md),
  [RD] [`DESIGN-relativized-recursion.md`](DESIGN-relativized-recursion.md),
  [CM] [`DESIGN-cost-incentive-model.md`](DESIGN-cost-incentive-model.md).
- **Papers**: CGSY24, ePrint [2023/1646](https://eprint.iacr.org/2023/1646) (local copy in
  [`reference/papers/`](reference/papers/)); Chiesa–Tromer, ICS 2010 (CT10); Luykx–Mennink–Neves,
  ePrint [2016/827](https://eprint.iacr.org/2016/827); Hülsing–Kudinov, ePrint
  [2022/346](https://eprint.iacr.org/2022/346); Fiore–Nitulescu, ePrint
  [2016/112](https://eprint.iacr.org/2016/112); Barbara–Chiesa–Guan, ePrint
  [2024/728](https://eprint.iacr.org/2024/728). The rest of the reading list is [CGH] §10.

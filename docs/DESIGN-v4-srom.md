# recursion.fast v4: the signed-random-oracle (SROM) rules

**Status.** The normative design of v4 (2026-10-22, updated 2026-10-23 after stages A and B, their
reviews RA, RB, GA, GB and the contract fix pass), implemented on the branch `v4/srom-rules`: the
Lean contract under `RecursionFast/Contract/` (stage A) and the oracle service, runner and CI
workflows (stage B). It is a proposal: the user was away while it was built, and every decision
taken without them is listed in §6, each reversible. It supersedes the working brief
[`v4/BRIEF.md`](v4/BRIEF.md) (decisions V4-1 … V4-16, amendments V4-A1 … A8) where the two differ,
and answers the adversarial review [`v4/reviews/C-design-attack.md`](v4/reviews/C-design-attack.md)
(findings C-M1 … M4, C-m1 … m13). Where this document and the Lean text differ, the Lean text is the
rule and the difference is a bug here.

**Inherits from** the v3 record and the proposals that followed it: the v3 design [V3], the O-25
record [O25], the CGH guide [CGH], the attested-oracle proposal D4 [RD] and the cost model [CM]
(§7 has the links). Their ids (V3-n, O-n, RR-n, RU-n, CM-n, C1–C15) are kept.

**Evidence tags.** **kernel**: a Lean theorem on `propext`, `Classical.choice`, `Quot.sound` only,
named. **paper**: an argument, here or cited. **measured**: a number with its log under `logs/`.
**estimate**: arithmetic from measured or published inputs. An untagged sentence is explanation.
Two marked **PLACEHOLDER**s wait on the harness's final fix pass.

**Reading paths.** Everyone: §0. Cryptographers: §1, §2. zkVM engineers: §1.3, §3, §4.
Formal-verification readers: §1, §2.4, §5. The user: §0 and §6, and the checks against
the record (C1–C15, the O-25 criteria, the earlier proposals' decisions) in
[`v4/CHECKS.md`](v4/CHECKS.md).

---

## 0. Summary

**The competition.** As in v3, agents submit a hash-based non-interactive argument for one relation
over 32-byte digests (a leaf commits to a BLAKE2s chain from a secret start, a node to two accepted
children): Lean query programs `V` and `P`, an extractor program, and a kernel-checked certificate
of knowledge soundness and completeness in the random-oracle model. An x86-64 assembly prover is
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
signature has no knowledge state below `errorCap` (**paper**, §2.2; **kernel** control
`sigTrust_kstate_iff`). Only the contract's `acc` trusts signatures, and unforgeability is used
once, outside every certificate, to compose the tree. Nothing is left for a reviewer to forbid.

**The tree.** On the run's one query log, signed traces are genuine unless a signature was forged,
so the one-level extractor applies node after node down to the leaves (CGSY24 Thm 5.1, no factor
per node). The walk is kernel (`Compose.walk`); the PRF hybrid and the forgery/collision split are
paper (§2.4). Error `(Q + qV)·ε + Adv_PRF + Adv_EUF-CMA + Adv_coll`, the first term about `2^-98`.

**What it costs.** A trusted runtime (the service, whose bug can be accept-all; the attested CI
workflow). One idealised assumption, keyed BLAKE2s is a PRF, beside collision resistance and
one-wayness, from which the signature's EUF-CMA follows (§2.5). Every oracle call goes to the
service on the prover's own cores. Per child, a node circuit checks one signature and hashes the
child's trace (§4.2). Trusted code: 355 Lean lines (v3: 292; budget 500) and 3,559 runtime lines
(§5). Two walls of v3 stand: node extraction is decoding (#7), and no honest recursive entry is
sized against the caps (C5); the certified baseline's measured frontier (§3.6) shows how far the
season shape is.

| Status | |
|---|---|
| ran on the development VM | build and axiom audit; service, sandbox and harness tests; the witness-sending entry and the certified baseline `spartan-srom` ACCEPTed end to end at the smoke shape |
| ran on a GitHub runner | CI run 39952420263 (AMD EPYC 9V45): Lean job 7 min 21 s, service and sandbox tests pass; earlier runs: chain checker 1.78 s (`T_V` ≈ 178 ms), signatures equal to the Lean signer's. The end-to-end smoke has not yet run there |
| never ran | the evaluation workflow and its attestations; any entry at the season-1 shape (C-m10), so nothing is ranked |

| | v3 | v4 |
|---|---|---|
| deployed oracle | public `BLAKE2s(0x52 ‖ q)` | `PRF_k(q)`, secret key fresh per run, behind a service |
| node clause | `Vb c₁ π₁`: `V` on public BLAKE2s | `acc vk c₁ (π₁, tr₁, σ₁)`: `V` on a signed trace |
| certificate | `KS`, `CompleteWithError`, `Computes`, caps | the same, **for every `vk`** |
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

### 1.4 What v3 contributes verbatim

`Contract/Security.lean`, `Machine.lean` and `Tree.lean` are v3's, word for word (V4-1, V4-16); v3
§6 and §7.1 explain them. In `final` below, `runLog L` answers each query from the first matching
entry of the log `L` (`none` on a miss), where `runSeq tr` answers from the next entry of the trace.
In brief:

```lean
structure KState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) where
  μ : Log → ℝ≥0
  empty : μ [] = 0
  step : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256
  final : ∀ L c π, L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
    ∃ w, E c π L = some w ∧ R c w
```

- **Knowledge soundness** (`KS`): the submitter exhibits a potential `μ` on query logs that starts
  at 0, rises by at most `ε` on average per fresh answer, and below 1 makes every proof `V` accepts
  on the log extractable by `E`. The paper theorem, kernel-checked in v3 (`Library/PaperTheorem.lean`,
  `paper`, ported unchanged), turns it into `(Q + qV)·ε` by Markov's inequality on the
  stopped potential, for `Q + qV ≤ logCap = 2^96`.
- **Completeness** (`CompleteWithError`): on every statement and witness of the relation, the honest
  prover's proof, produced and verified against one lazily sampled random oracle, is rejected with
  probability at most `δ ≤ 2^-128`.
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

For every public key `vk`, the submitter proves v3's knowledge soundness of `V vk` for
`Rel (S.acc vk)` and completeness of `P vk`, both over a random oracle. A node extractor recovers
the node's witness, the two children's signed proofs, from the node proof and the log (for a
succinct node, by decoding a word committed in the log, v3 #7; for the witness-sending entry, by
reading the proof) and outputs it; it does not check them, and the certificate does not ask
whether their signatures are genuine. That is the composition's job (§2.4).

The relation is **oracle-free given `vk`**, so completeness means what it says: the game samples a
fresh oracle only for `P`'s and `V`'s own queries, and a node witness carries its children's
signatures as data (C §2 item 6). The Lean `P` needs no signer. In deployment the native prover
obtains its own proof's signature from the service; the Lean `P` exists so that completeness is a
theorem and so that the harness can produce honest logs for the liveness check.

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
signed answer in `π` that agrees with the oracle's. Then for that `vk` no knowledge state exists
with `ε < 1/q`, where `q` is the number of oracle queries on the branch; in particular none at
`errorCap = 2^-128`, since `q ≤ qV ≤ 2^16`.

**Proof.** The adversary asks the branch's queries itself, then makes `Φ` true (it is unbounded, so
it can sign anything under `vk`). On every resulting log `L`, `(V vk c π).runLog L = some true`, so
`final` needs a witness for `c`, which does not exist; hence `μ L ≥ 1` on every such log. But
`empty` and `step` make the potential, stopped at 1, a supermartingale from 0 that rises by at most
`ε` per fresh query, so it reaches 1 on every path of `q` queries only if `q·ε ≥ 1`. ∎ If `Φ` needs
no query, no knowledge state exists at all unless every digest has a witness, the shape of v3's
`acceptAll_kstate_iff`, and then `Computes` with the budget excludes the extractor (v3 §6.2).

The general statement is paper; the kernel controls are its `q = 0` case.

**Controls** (**kernel**, `Library/SigTrust.lean`). `Vsig vk c π` accepts, with no oracle query,
a proof carrying a signature of `c` valid under `vk`. Under every key whose signer is known
(`Signer.pk sk`, keys the certificate quantifies over): `sigTrust_kstate_iff`, it has a knowledge
state for some extractor exactly when every statement has a witness, so a signature is no
knowledge; `sigTrust_no_kstate_none`, with an extractor that returns nothing it has none at any
error. The twin `sigTrust_ks_of_unsignable`: under a key for which no signature verifies, the same
verifier is knowledge-sound at error 0 for every relation and extractor. So it is exactly the
quantification over keys, some of whose secrets the adversary holds, that excludes it; a
certificate for one fixed key would not. `Controls/Certificate.lean` states the same about
`Certificate` (`sigTrust_no_certificate`, `sigTrust_certificate_opens`, `sigTrust_ks_unsignable`).

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

**The argument** (**paper** in outline, CGSY24 Thm 5.1 and §6.2; C §2). Treat the deployed prover
together with the signer and the harness's checks as one query algorithm against the oracle; for
each fixed signing seed it is deterministic, and the paper theorem covers every deterministic
query algorithm however much it computes, so holding `sk` costs nothing. Its log `L` contains
every query anyone asked, including the signer's re-evaluation of every trace it signs, and `Q`
counts them all. If the potential of `L` is below 1, which fails with probability at most
`(Q + qV)·ε` by the paper theorem, then walking down from the root:

1. The root's signed proof `(π, tr, σ)` is accepted, so `SigOk vk (traceDigest tr) σ`.
2. Either every entry of `tr` is the log's answer to its query (the trace is **genuine**: the
   service computed each answer by a query, and the oracle has one answer per query), or the walk
   has found a valid signature on a trace not contained in the log: outcome **forgery**.
3. If genuine, `runSeq tr` accepting implies `runLog L` accepting (the `runSeq → runLog` lemma),
   so `final` gives `w = E c π L` with `Rel (acc vk) c w`.
4. A node witness gives children `(c₁, p₁)`, `(c₂, p₂)` accepted by `acc`. Either `c₁, c₂` are the
   harness's children, or the walk has a `nodeStmt` collision: outcome **collision**. Recurse on each
   child with **the same `L` and the same event** `μ L < 1`: no factor per node.
5. At a leaf, the extracted `(s, n)` hashes to the harness's leaf digest: a witness (not necessarily
   the harness's start), or a `leafStmt`/`chainStep` collision.

**What is kernel and what is paper.**

| Piece | Status |
|---|---|
| `walk : KState (Rel (S.acc vk)) (S.V vk) S.E ε → L.Functional → L.length ≤ logCap → μ L < 1 → … → S.acc vk root p = true → Outcome S vk L n hs root p`: from a knowledge state, a functional log within `logCap` of potential below 1, `2^r` leaves and an accepted root signed proof, it computes the leaf starts, an explicit BLAKE2s collision, or an explicit signed trace with queries within `queryCap`, not contained in the log, **in the root's extraction tree** (`InTree`) | **kernel**, Library (untrusted, kernel-checked): `Library/Compose.lean`, `walk`, and `compose`, its propositional form (V4-8); `compose_exists`, without `InTree`, is trivially true for a known signer's key (`Controls/Compose.lean`, RA-M1) |
| `runSeq → runLog` | **kernel**: `Library/Trace.lean`, `OProg.runLog_of_runSeq` (on a functional log, a verdict on a trace whose entries are all in the log is the verdict on the log) |
| equal trace digests are equal traces or an explicit collision | **kernel**: `Library/Trace.lean`, `traceDigest_eq` (for queries under `2^64` bytes, which `queryCap` implies) |
| the paper theorem `(Q + qV)·ε` | **kernel** (`Library/PaperTheorem.lean`, `paper`, v3's) for a lazily sampled oracle and a deterministic adversary; randomisation and the random function **paper** |
| the split of "a signed trace not in the log" into an **EUF-CMA forgery** (no signed trace has that digest) or a **trace-digest collision** (the service signed another trace with the same digest; the two encodings differ and are injective by `queryCap`) | **paper** (V4-A8, C §2 item 4). A kernel form would carry the service's signed set as a Library parameter (C, unsettled 5); not done |
| the PRF hybrid | **paper** (§2.3) |

**The error.** `Pr[bad] ≤ (Q + qV)·ε + Adv^PRF(D) + Adv^EUF-CMA(B) + Adv^coll`, where `B` and `D`
run the evaluation and the walk: about `2^58` steps (**estimate**, [RD] §4.9 fine print; the walk
runs `E` per node within `B t`). At the season shape `Q ≈ 2^28–2^30` (**estimate**, C §2 item 1),
inside `logCap = 2^96` and the efficient-extraction domain of about `2^61` entries, so the first term
is at most about `2^-98` at `ε = 2^-128`.

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
`2^80` evaluations about `2^-131`. Collision resistance (128-bit generic) is the binding term, at
the scale of `errorCap`.

**Operational conditions** (§3.2): the index is taken by one atomic read-modify-write before the
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
the deployed `PRF_k` and `vk`; the harness's concrete checks do (C8): every root, sampled proof and
stream output is checked with the compiled `acc`, and the extractor's liveness runs on the native
prover's proofs with the service's own log. That log is now **authentic**: nobody can evaluate the
oracle except through the service, so the service's log is the complete query log the theorem's
extractor reads (in v3 the native prover emitted its own log, #9 item 1).

`CompleteWithError` is about `V`, not `acc`: a `V` that accepts only proofs longer than `proofCap`
is certified and fails every harness check (v3 §6.4). A verifier whose queries on one proof exceed
what one `sign` request carries (a body of at most 16 MiB) can never obtain a signed trace, and
fails the same way.

### 2.7 The trust statement

> **A ranked record means:** the certificate job's Lean kernel accepted `CertificateR` for the
> rendered challenge; the benchmark job, on a
> GitHub-hosted runner, started a fresh service for every timed run, checked every signed proof it
> was given with the compiled `acc` under that run's `vk` within `T_V`, and measured `T_tree` and
> the stream; and the result JSON, binding `vk`, the CPU model, the runner image, the harness commit
> and the service binary's hash, carries a GitHub artifact attestation that verifies against the
> organiser's evaluation workflow. Its reader trusts:
>
> 1. **One kernel**: Lean v4.34.1's, the comparator that replays the proofs in it, and Lean core,
>    Mathlib and the pinned packages as hashed in the olean manifest. *v3 also had nanoda as a
>    second kernel; CI drops it (Q5).*
> 2. **The contract**: 10 files, 355 code lines, no theorem, three standard axioms. It now includes
>    the signature check `SigOk`, the trace digest and `runSeq`, beside v3's security definitions
>    and extractor machine.
> 3. **BLAKE2s** = RFC 7693, and three properties: collision resistance on the seven tagged domains
>    (constructive: a failure is a pair someone can exhibit), multi-target one-wayness of the chain
>    step, and **keyed BLAKE2s-256 is a PRF** (LMN16's ideal-cipher analysis), for the oracle and for
>    the signer's key derivation. EUF-CMA of the contract's scheme follows from these (§2.5).
>    *Replaces v3's "BLAKE2s instantiates the random oracle".*
> 4. **Knowledge soundness of the whole tree from one log** (§2.4): the one-level certificate and
>    the composition walk are kernel; the paper steps are the passage from the lazily sampled oracle
>    to a random function and to randomised adversaries, the PRF hybrid (§2.3), and the reading of
>    the walk's third outcome as a forgery or a trace-digest collision. *v3's item 4 (O-25 open, no
>    composition theorem) is gone.* Completeness is over a random oracle; that honest proofs pass
>    `acc` under the deployment is the harness's concrete checks.
> 5. **The badge code**: what Lean's compiler emitted for `acc` (through the word-level BLAKE2s twin
>    proved equal to the contract's, V4-A7), `P` and the contract interpreter on `ext`, guarded by the
>    source rule and gate rules 3 and 6–8 (v3's rule 9 went with the frontend); residual O-12.
>    *(v3 item 5)*
> 6. **The harness tools**: gate, source rule, axiom audit, manifest, renderer, sandbox. *(v3 item 6)*
> 7. **Tested, not proved: the runner and the service.** The runner: Python `treeRoot`, the prover
>    interface, the caps, the measurements, the stream protocol, liveness. The service: tested against
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
>    sandbox's isolation of untrusted code from the service and from the job's credentials.
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
entries end to end at the smoke shape; a GitHub runner (CI run 39952420263, AMD EPYC 9V45) ran the
Lean job and the service and sandbox tests, but not yet the end-to-end smoke; the evaluation
workflow and its attestations have never run. Until they do, every end-to-end claim here is from
the development VM, and no record of the kind the trust statement describes exists.

---

## 3. The deployment

### 3.1 The trusted machine: GitHub Actions with a trust anchor (V4-A1, V4-A2)

**Why CI.** v3 had no reference machine, so every measured rule was a placeholder (C13). A
GitHub-hosted runner is a public, identical-image machine that anyone can re-run, and GitHub's
artifact attestations give a checkable statement "this result was produced by that workflow at
that commit on GitHub's runner". The costs are stated in P3 of the brief: `ubuntu-24.04`, x86-64, 4
vCPU, 16 GB RAM, 14 GB disk, 6 h per job, and **heterogeneous CPU models** (AMD EPYC and Intel Xeon;
carry-less multiply available; AVX-512 and GFNI not guaranteed). Hence: the benchmark shape fits 16
GB; `T_V` self-calibrates in the same job; every result records the CPU model; records are only ever
compared in pairs within one job (v3's ABBA rule).

**Separate jobs** (V4-A2, C-M2). The **certificate job** (source rule, the entry's `lake build`, the
comparator, the gate, the axiom audit) is deterministic and may run on any runner with the cached
package tree. It uses the **Lean kernel only**: nanoda does not fit a 16 GB runner (§2.7, Q5); a
larger machine can add it, and the result states which kernels ran. The **benchmark** must run on
the GitHub-hosted runner; it is split into six jobs, each within the 6 h limit: calibration, one
tree repeat, the DoS column and liveness; two more tree repeats; three stream repeats. Each job
measures its own `T_triv,best` and service throughput, and a result whose jobs ran on different CPU
models is marked `mixed_cpu` and never used for a paired record comparison (stage B RESULT §5.4).

**Measured** (CI runs 39935079265, 39940607844, 39952420263): the core's Lean job, which builds
the contract, library and controls, takes 8 min 53 s cold, 4 min 12 s and 7 min 21 s with the
package cache. On the development VM the witness-sending entry's certificate job takes 2 min 33 s,
of which the comparator with the Lean kernel takes 68–81 s; the baseline's comparator takes 372 s
and 3.7 GB (submissions repository, `logs/f3/cert-lean.log`). The build caps are not yet set from a
runner run of a real entry (§6.2).

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
  attestation. A record counts only if `gh attestation verify result.json --owner scaraven
  --signer-workflow scaraven/recursion.fast/.github/workflows/evaluate.yml` passes, which rejects a
  fork's copy of the workflow. That check matches the workflow's path, not the ref it ran at, and
  the harness commit in the JSON is reported by the caller (RF-m1). So a reader also requires the
  attestation certificate's `job_workflow_ref` (`…/evaluate.yml@<commit>`) to name the recorded
  harness commit (the exact command is the one the harness's documentation gives, to be aligned
  when the harness fix pass lands it). The full evaluation and its
  attestation have not yet run on GitHub (§2.8).
- GitHub's approval of first-time contributors' workflows is **compute admission**, not a verdict.

### 3.2 The service (V4-2, V4-3, V4-A4, V4-A5)

**What it is.** One process per timed run (one tree repeat, one stream repeat, the liveness run),
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
`QUERY` and `2^16` per `SIGN`; at most 64 connections; `2^16` signatures per lifetime.

**Lifecycle and key handling.** `k` and the signing seed are independent `getrandom` draws, never
written to disk, destroyed at exit; chain starts are derived under tag `0x53` (§2.5). The signature
index is taken by one atomic step before the signature is computed and never reused, even if the
request then fails. A crash or restart is a new key and aborts the run.

**No memoisation** (C-m2). The service persists across a stream repeat's otherwise stateless
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
(static glibc, libgcc), no other build input; the image's `gcc` and binutils versions are part of
the rules (§3.7). Source in any language may sit beside it for readers,
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
| 0 | certificate job | source rule, build, comparator, gate, axiom audit (§3.1) | none |
| 1 | build | the assembly prover, in the sandbox, hashes recorded | none |
| 2 | calibration | `T_triv,best`; the service's calls/s and compressions/s (§3.5) | a calibration instance |
| 3 | **tree** (×3) | fresh starts per evaluation; `PROVER tree DIR`; **timed**: `T_tree` | a fresh lifetime per repeat: every `QUERY` and `SIGN` |
| 4 | root check | compiled `acc` on (`treeRoot`, root signed proof) under that repeat's `vk`, within `T_V` (§3.5) | none: offline |
| 5 | samples | `acc` on 16 randomly chosen inner signed proofs against the runner's digests | none |
| 6 | canaries | for 8 proofs of each kind, every mutation must be rejected: a byte appended to or removed from the file or `π`, a statement bit flipped, the sibling's statement, one trace answer or one query byte changed, a trace entry appended, a chain value or the index of the signature changed | none |
| 7 | **stream** (×3) | `M + 1` leaves and `M` merges, a fresh process each, ready handshake, **timed**: `t_link`; every output checked with `acc` within `T_V` | a fresh lifetime per repeat, shared by its requests |
| 8 | liveness | at `r = 1`, `n = 16`: the service logs every query; `ext` runs on `(c, π, L)` within the declared fuel; the output must decode to a witness (`Rel` for a leaf, `acc` on the extracted children for a node) | logging mode |
| 9 | DoS | `acc` on 1,000 random and mutated signed proofs (random bytes; random `π` with the root's trace and signature; bit flips and truncations): any accept or crash rejects; the maximum time is published. **PLACEHOLDER (harness final fix pass): how a `V` that is slow on malformed input is treated (a per-item or total time bound, and its outcome).** | none |
| 10 | result | JSON with every number of §3.5, attested | — |

The runner never passes a digest to `tree` and never a start to `node`; leaf and root digests are
the runner's (`treeRoot`, the contract's specification of it).

### 3.5 What is measured, and how

- **`T_tree`**: wall time of one `PROVER tree` process proving the whole tree, median of three
  repeats. Anything goes inside: flattening, proof of parent, bundling near the root, grinding.
- **The stream** ([CM] §3.3, CM-4, CM-6): link `i` draws a fresh start of length `n_f`; a leaf
  request proves it and a merge request folds it into the running proof (`π_i` proves
  `nodeStmt c_{i−1} d_i`), or one 1→1 request does both. Every request is a fresh process whose
  start-up is untimed (ready handshake); the clock runs from the inputs to the output; one start per
  process, released one at a time. As the runner computes it (`harness/rfh/bench.py`, [CM] §3.3),
  `t_leaf` is the sum of the `M + 1` leaf times over `M`, `t_merge` the sum of the `M` merge times
  over `M`, and `t_link = t_leaf + t_merge`, each the median of three repeats. Under the SROM a link
  also pays its `SIGN` calls, on the clock.
- **`T_V`** (V4-12, C6): one `acc` check on one pinned core, timed in the badge process (parse plus
  `accF`, stage B's deviation 3), must take at most `T_triv,best / R`, `R = 10`. **PLACEHOLDER
  (harness final fix pass): whether this is CPU time or the wall time of the pinned check (an upper
  bound on its CPU time), the cap being measured the same way.** A sample above the cap is measured
  again, up to `checker_runs` times, and its best time is compared, the statistic of the cap
  (RB-M1, fixed). `T_triv,best` is the best of `checker_runs` runs, where
  it is measured **in the same job** by the organiser's compiled-Lean chain checker, interleaving
  8 chains, over the tree's chains (`2^24` compressions). It applies to the root, the
  samples and every stream output. **Measured**: 1.776–1.785 s on a GitHub runner, about 106 ns per
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
  the incumbent rebuilt in the same job; cross-model results are never compared unpaired.

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
| stream: links `M`, chain length `n_f` | 512, `2^16` | 4, 16 | V4-11, CM-5 |
| `K` | 20, provisional | 20 | V4-10, CM-2 |
| `T_V` ratio `R` | 10, enforced | 10, reported only (the trivial check takes microseconds) | V4-12, CM-8 |
| repeats (tree, stream) | 3, 3; medians | 1, 1 | v3 §8.3 |
| samples; canaries per kind; DoS proofs | 16; 8; 1,000 | 16; 8; 64 | v3 §8.3 |
| time caps: tree run, stream request, stream repeat, one `acc` check | 1 h, 600 s, 4 h, 60 s | 300 s, 120 s, 30 min, 60 s | [CM] §3.5 |
| `proofCap`, `queryCap`, `qV` | 1 MiB, `2^20` B, `≤ 2^16` | same | V4-13, V4-A3 |
| signed-proof file the runner reads | ≤ 64 MiB | same | V4-13 |
| `errorCap`, `completenessCap`, `logCap` | `2^-128`, `2^-128`, `2^96` | same | V4-13 |
| signatures per service lifetime | `2^16` | same | V4-3 |
| memory cgroups | prover 11 GB, service 2 GB (13 GB together), badge 4 GB | same | V4-13 |
| job limit | 6 h | 6 h | P3 |

The table is a selection of `harness/season.toml` and `harness/smoke.toml`, which also fix the
check batching, the number of calibration runs and the setup and build caps; the season benchmark
runs as six jobs (§3.1), the smoke as one.

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
   assembly with the image's toolchain, or rewrite such directives as `.byte`.
2. **A `Submission` must be computable** (Q4): the badge compiles `V`, `P` and `ext`, and a
   noncomputable `ε : ℝ≥0` literal fails the build; write it as a cast from `ℚ≥0`.
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
  `verify_s = 60 s`. The DoS column draws random mutations and does not find such inputs, and no
  rule bounds `V`'s time on adversarial proofs (see the DoS placeholder, §3.4).
- **One kernel on CI** (Q5, §2.7): no independent re-check of the certificate.
- **CM-R1 … R8** of the cost model, unchanged.

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
| `Security.lean` | 33 | `KState`, `KS`, `failProb`, `CompleteWithError`, caps | unchanged |
| `Machine.lean` | 62 | the step-counting word machine | unchanged |
| `Extractor.lean` | 50 | tape, `decodeWit` for signed children, budget, `Computes` | output format |
| `Tree.lean` | 8 | `treeRoot` | unchanged |
| `Certificate.lean` | 32 | `Submission` with `vk`, `acc` (with `\|tr\| ≤ qV`, RA-M2), `Certificate`, `Declared`, `CertificateR` | `Vb`, `blake2sOracle`, `tagRO` deleted |
| **total** | **355** | budget ≤ 500 | v3: 292 |

What a human must trust it for: that `Rel` and `acc` say what §1.1 says; that `SigOk` and
`traceDigest` hash exactly the bytes of §1.3 (the service and runner are tested against them); that
v3's definitions are unchanged. `lake build` is green (1,264 jobs, `logs/D-final-build.log`; a cold
build takes 1 min 56 s to 2 min 55 s on the development VM, `logs/A-fix-build-cold.log`), and the
axiom audit passes on every module (`propext`, `Classical.choice`, `Quot.sound`;
`logs/A-fix-axiom-audit.log`). The contract imports Lean core and Mathlib only. By `loc.py`, the
Library has 1,856 code lines and 233 theorems, the Controls 2,089 lines and 309 theorems.

**Controls**: every trusted definition has a positive and a negative control (the full table is
stage A RESULT §3). The ones that carry the v4 changes:

| Definition | Positive | Negative |
|---|---|---|
| `Rel`, signed node clause | `node_of_two_leaves` (reference signer, symbolic), `node_of_two_leaves_ref` | `child_other_key`, `child_trace_nonempty`, `node_needs_statement`, `first/second_child_rejected` |
| `runSeq` | `prog_runSeq`, `prog_runLog_of_runSeq` | `prog_runSeq_extra` (exact consumption), `prog_runSeq_short`, `prog_runSeq_wrong_query` |
| `acc` | `acc_leafSigned`, `acc_query_at_cap` | `acc_trace_over_qV`, `acc_two_entries_rejected`, `acc_query_over_cap`, `acc_over_cap`, `acc_changed_answer` |
| `traceDigest`, WOTS, `SigOk` | `traceDigest_kat` (hashlib), `sigOk_sign` (every `sk`), `wotsDigits_dominates` (the checksum) | `traceDigest_changed_answer`, `sigOk_other_key`, `sigOk_key_unique`, `sigOk_ots_length`, `sigOk_path_length` |
| `decodeWit` | `decodeWit_node_kat`, `decodeWit_leaf_kat` | `decodeWit_long_trace`, `decodeWit_short_sig`, `decodeWit_long_proof` |
| `Certificate` with `∀ vk` | `ws_certificate`, `Backdoor.certified`; `sigTrust_ks_unsignable` | `sigTrust_no_certificate`, `sigTrust_certificate_opens`, v3's negatives |
| composition (Library) | `walk_one_leaf`, `walk_two_leaves` | `forgery_trivial`, `compose_exists_free` |

The Library theorems the badge and the decoder rest on, `Fast.accF_eq` (the badge's `accF` is `acc`)
and `Words.decodeWit_witWords` (every fitting witness can be denoted), are theorems, not controls.

**The trusted runtime** (stage B RESULT §1.1, `logs/harness/loc-runtime.log`, after the golf and
the fix pass): **3,559 code lines**: the service 963 Rust lines (std only), the runner 1,028, the
sandbox 238, the badge mains 135, the proof-side order 449, v3's ported tools 697, the calibration
generator 161, CI scripts 49. Two parts are trusted for nothing a record's soundness rests on: the
liveness badge (a smoke test; the security claim is the proved `Computes`) and the measurement
client `rf-bench` (the calibration column is published, not enforced).

| Component | Trusted for |
|---|---|
| the service (Rust: PRF, signer, wire protocol, caps) | answers are `PRF_k`; signatures only on traces it computed; index uniqueness; key isolation and freshness; no memoisation |
| the runner (Python: sandbox, assembly build, tree, stream, `acc` badge, canaries, `T_V` calibration, liveness, DoS, score JSON, season file) | the instances, the clock, the caps, running the compiled `acc` on every proof, the published numbers |
| the gate, source rule, axiom audit, manifest (ported from v3) | the badge executables are the kernel-checked terms |
| the CI workflows (the core's reusable evaluation workflow; the submissions repository's caller) | the anchor: untrusted code runs only in the sandbox; the result is attested |

---

## 6. Decisions taken in the user's absence, and open items

### 6.1 The decisions

Each is reversible; the reason is one line. Overrides: the amendments V4-A1 … A8 win over V4-1 …
V4-16 where they differ.

| Id | Decision | Reason |
|---|---|---|
| P1 | D3, the SROM, not D4 | offline, stateless checks by the harness and by third parties; no key release, no designated-verifier window; cost one signature check per child |
| V4-1 | v3's KS, completeness, extractor machine and budget verbatim; KS and completeness for every `vk` | minimal change; `∀ vk` makes a signature-trusting verifier uncertifiable |
| V4-2 | the oracle is keyed BLAKE2s-256 behind a service, fresh key per lifetime; `blake2sOracle`, `tagRO`, `Vb` deleted | CGH needs a public seed |
| V4-3 | a contract-fixed stateful hash-based signature (WOTS `w = 4`, 133 chains, height 16), fresh keys per lifetime, hash-then-sign of the trace | no group; one hash gadget; near-minimal in-circuit cost |
| V4-4 | sequential trace semantics | linear for the harness and in-circuit |
| V4-5 | no trace cap | **withdrawn** by V4-A3 |
| V4-6 | `E` takes no `vk` | it decodes children from the node proof; a design may put `vk` in `π` |
| V4-7 | `acc` is the harness's one check; root proofs are signed proofs | one predicate for relation, harness, third parties |
| V4-8 | composition as a Library theorem returning witnesses, a collision or a forgery | kernel content for CGSY24's argument |
| V4-9 | the prover is x86-64 assembly; the Lean `P` stays | the request; completeness is about `P` |
| V4-10 | `S = T_tree + K·t_link`, `K = 20` provisional, 100/200 ms reference lines, a fresh process per stream request | the cost model as written, with its illustration |
| V4-11 | season 1: `r = 6`, `n = 2^18`; stream `M = 512`, `n_f = 2^16`; smoke `r = 2`, `n = 16`, `M = 4`; one season file | 16 GB runners; the same chain work as the long shape |
| V4-12 | `T_V`: one `acc` check on one pinned core ≤ `T_triv,best / 10`, measured in the same job (CPU or wall time: §3.5's placeholder) | C6; self-calibrating |
| V4-13 | v3's caps kept; memory 13 GB | minimal change |
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
| RA-M2 | `acc` checks `\|tr\| ≤ qV` (one trusted line) | `KS`'s query bound ranges over oracle functions and does not bound a non-functional trace |
| Q5 | CI checks certificates with the Lean kernel only | nanoda needs more than 16 GB (§2.7) |
| B dev. 1 | the prover isolated by namespaces, not a separate uid; two memory cgroups (11 GB + 2 GB) | no system user needed; the prover cannot make the OOM killer pick the service |
| B §5.4 | the season benchmark split into six jobs; mixed CPU models never paired | the 6 h job limit |
| B dev. 2, 3 | the badge parses files at byte level; `T_V` times parse plus `accF` in process | the word-level parser costs 0.4 µs per byte; start-up excluded |

### 6.2 Open items

**Not yet done** (the three items the implementation still owes):

1. **The full evaluation on GitHub**: the evaluation workflow, its six benchmark jobs and the
   attestation have never run; the caller template is not yet installed in the submissions
   repository; the end-to-end smoke has not yet run on a runner (§2.8).
2. **Build caps from a runner run** of a real entry's certificate job (C-M2, C10).
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
- **Crafted-input DoS** (C9, F1-M2): see the DoS placeholder (§3.4).
- **Keyed BLAKE2s as a named assumption** (C unsettled 1): the alternative wording calls it the
  design's one heuristic, since its only analysis is in an ideal-cipher model.
- **Runner facts** (C unsettled 2, 3): the CPU models, and whether `pclmulqdq` and AVX2 are on every
  one (each job prints `lscpu`).
- **The forgery/collision split in the kernel** (C unsettled 5); **the efficient-extraction domain
  against `logCap`** (O-21, v3); **`K` and the targets on CI**, once a leader exists.
- **The submissions repository**: its branch `v4/flock-baseline` pins `81e1ebf` and carries the v4
  rulebook and the baseline; its `main` still pins `15e4ae5` (v3) until that branch is merged.

---

## 7. Where things are

- **This design's implementation**: branch `v4/srom-rules`. Contract `RecursionFast/Contract/`;
  Library `RecursionFast/Library/` (paper theorem, witness-sending entry, reference signer,
  composition, word-level BLAKE2s); Controls `RecursionFast/Controls/`; `scripts/` (line count,
  gate, source rule, axiom audit); the service `service/` (`PROTOCOL.md` normative for provers); the
  runner `harness/` (`FORMAT.md` the signed-proof file, `PROVER.md` the prover interface,
  `season.toml`); `tests/`; `.github/workflows/` (`ci.yml`, `evaluate.yml`); stage records
  `docs/v4/stages/A-contract-RESULT.md` and `B-harness-RESULT.md`. - **The brief and the attack**:
  [`v4/BRIEF.md`](v4/BRIEF.md), [`v4/reviews/C-design-attack.md`](v4/reviews/C-design-attack.md). -
  **The record it inherits**: [V3]
  [`v3-design-…`](v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md),
  [O25]
  [`v3-open-problem-…`](v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md),
  [CGH]
  [`CGH-circumvention-guide-…`](CGH-circumvention-guide-secret-keyed-signed-and-attested-random-oracles-with-reading-list.md),
  [RD] [`DESIGN-relativized-recursion.md`](DESIGN-relativized-recursion.md), [CM]
  [`DESIGN-cost-incentive-model.md`](DESIGN-cost-incentive-model.md).
- **Papers**: CGSY24, ePrint [2023/1646](https://eprint.iacr.org/2023/1646) (local copy in
  [`reference/papers/`](reference/papers/)); Chiesa–Tromer, ICS 2010 (CT10); Luykx–Mennink–Neves,
  ePrint [2016/827](https://eprint.iacr.org/2016/827); Hülsing–Kudinov, ePrint
  [2022/346](https://eprint.iacr.org/2022/346); Fiore–Nitulescu, ePrint
  [2016/112](https://eprint.iacr.org/2016/112); Barbara–Chiesa–Guan, ePrint
  [2024/728](https://eprint.iacr.org/2024/728). The rest of the reading list is [CGH] §10.

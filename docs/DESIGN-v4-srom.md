# recursion.fast v4: the signed-random-oracle (SROM) rules

**Status.** The normative design of v4 (2026-10-22), implemented on the branch `v4/srom-rules`: the
Lean contract under `RecursionFast/Contract/` (stage A) and the oracle service, runner and CI
workflows (stage B). It is a proposal: the user was away while it was built, and every decision
taken without them is listed in §7, each reversible. It supersedes the working brief
[`v4/BRIEF.md`](v4/BRIEF.md) (decisions V4-1 … V4-16, amendments V4-A1 … A8) where the two differ,
and answers the adversarial review [`v4/reviews/C-design-attack.md`](v4/reviews/C-design-attack.md)
(findings C-M1 … M4, C-m1 … m13). Where this document and the Lean text differ, the Lean text is the
rule and the difference is a bug here.

**Inherits from** the v3 record and the proposals that followed it: the v3 design [V3], the O-25
record [O25], the CGH guide [CGH], the attested-oracle proposal D4 [RD] and the cost model [CM]
(§8 has the links). Their ids (V3-n, O-n, RR-n, RU-n, CM-n, C1–C15) are kept.

**Evidence tags.** **kernel**: a Lean theorem on `propext`, `Classical.choice`, `Quot.sound` only,
named. **paper**: an argument, here or cited. **measured**: a number with its log under `logs/`.
**estimate**: arithmetic from measured or published inputs. An untagged sentence is explanation.
`TODO(A)` and `TODO(B)` mark numbers and names the implementation stages had not fixed when this
was written.

**Reading paths.** Everyone: §0. Cryptographers: §1, §2. zkVM engineers: §1.3, §3, §4.
Formal-verification readers: §1, §5, §6. The user: §0 and §7.

---

## 0. Summary

**The competition.** As in v3, agents submit a hash-based non-interactive argument for one fixed
relation over 32-byte digests (a leaf commits to a BLAKE2s chain from a secret start, a node to two
accepted children): Lean query programs `V` and `P`, an extractor program, and a kernel-checked
certificate of knowledge soundness and completeness in the random-oracle model. New: an x86-64
assembly prover is timed on GitHub-hosted runners, proving a tree of chains and extending a running
proof chain by chain, scored `S = T_tree + K·t_link`.

**The SROM.** For every timed run a service draws a fresh secret PRF key `k` and an independent
signing key pair `(sk, vk)`. It answers each oracle query with `PRF_k(q)` (BLAKE2s-256 in keyed
mode) and, on request, signs the digest of a sequence of query–answer pairs (a *trace*) with a
contract-fixed hash-based signature. A proof travels as a **signed proof** `(π, tr, σ)` and is
accepted for `c` when `V vk c π`, reading its answers in order from `tr`, accepts and `σ` signs
`tr` under `vk`. That predicate, `acc`, never evaluates the oracle: it is the relation's node
clause, the harness's check of every proof, and anyone's check later with the published `vk`. A
node circuit proves its children's acceptance by hashing their traces and checking one signature
each, so it never needs the key. This is Chiesa–Tromer's signed random oracle (CT10), as CGSY24 §2.2
reads it.

**Why it closes O-25.** v3's certified backdoor computes the public oracle, compares it with an
answer and accepts a magic proof on a match (`Controls/Backdoor.lean`). Every such backdoor needs a
value about the deployed oracle that `V` holds without asking it. Under a key drawn after `V` is
frozen none exists, since recognising `PRF_k` would distinguish it from a random function: the
certificate's bound carries over to the deployment up to the PRF advantage of a distinguisher that
runs the whole evaluation (**paper**, §2.3). The backdoor stays certified in the model (**kernel**,
`Controls/Backdoor.lean`, `backdoor`) and never fires.

**Why a certified verifier can never trust a signature.** The certificate holds for every `vk`,
against an unbounded adversary that can sign anything. A branch of `V` that accepts a false
statement because the proof carries a valid signature, `sk`, or a signed answer agreeing with the
oracle fires on every oracle, so it has no knowledge state below error `1/q` for its `q ≤ 2^16`
queries (**paper**, §2.2; **kernel** control `sigTrust_kstate_iff`). Signatures are trusted only
by the contract's `acc`, and unforgeability is used once, outside every certificate, to compose the
tree. This replaces the recognition rule of the 2026-10-19 design (O-25 §2) and the intake review
of `V`: nothing is left for a reviewer to forbid.

**The tree.** On the run's one query log, the root's signed trace is genuine unless a signature was
forged, so `V` accepts on the log and the extractor yields children whose traces are genuine again,
down to the leaves: CGSY24 Thm 5.1's straightline argument, no factor per node. The walk is a
Library theorem (**kernel**, `Compose.compose`); the PRF hybrid and the reading of the walk's
"signed trace not in the log" as a forgery or a collision are **paper**. Error `(Q + qV)·ε +
Adv_PRF + Adv_EUF-CMA + Adv_coll`, the first term about `2^-98` (**estimate**: `Q ≈ 2^30`,
`ε = 2^-128`).

**What it costs.** A trusted runtime (the service, whose bug can be accept-all; the organiser's
workflow, whose results are attested). One idealised assumption, keyed BLAKE2s is a PRF, beside
collision resistance and one-wayness of tagged BLAKE2s, from which the signature's EUF-CMA follows
(**paper**, §2.5). Prover time: every oracle call, Merkle hashes included, goes to the service on
the prover's own cores, so the organiser's hashing speed is in every score. Per child in a node
circuit, one signature check (about 300 compressions on average, at most 495) and the child's trace
hashed (about 1.6× a public-hash Merkle step per query) (**estimate**, §4.2). Trusted Lean: 355
code lines in stage A's draft (TODO(A): final count) against v3's 292, budget 500.

**Where it stands.** Unchanged from v3: the security definitions word for word, the leaf clause, the
tree, the caps, and two walls, node extraction is decoding (#7) and no honest recursive entry is
sized against the caps (#8, C5). The contract builds (TODO(A)); the service and the sandbox pass
their tests; the runner passes a smoke run with a stand-in for the compiled `acc` and rejects three
broken provers; the smoke with the real `acc`, the witness-sending entry and a toy assembly prover
awaits the merge of stages A and B, and the workflows have not yet run on GitHub (TODO(B)). **No
certified entry can yet run the season-1 shape** (C-m10); the first real entry, the Flock-based
baseline (stage F), will be PROVISIONAL, and nothing is ranked until a certified entry runs the
ranked shape.

| | v3 | v4 |
|---|---|---|
| deployed oracle | public `BLAKE2s(0x52 ‖ q)` | `PRF_k(q)`, keyed BLAKE2s-256, `k` secret and fresh per run, behind a service |
| node clause | `Vb c₁ π₁`: `V` run on public BLAKE2s | `acc vk c₁ (π₁, tr₁, σ₁)`: `V` run on a signed trace |
| `V`, `P` | `Digest → …` | also take `vk`; `E` does not |
| certificate | `KS`, `CompleteWithError`, `Computes`, caps | the same, **for every `vk`** |
| O-25 | open; a rule and review of `V` | closed by the deployment (paper); rule and review deleted |
| composition across levels | heuristic | kernel walk plus paper reductions |
| prover | any language, built in a sandbox | x86-64 assembly, built in the sandbox |
| machine | a reference machine that never existed | GitHub-hosted runners; results attested |
| score | whole-tree wall time at `r = 8`, `n = 2^14` | `S = T_tree + K·t_link`, tree at `r = 6`, `n = 2^18`, plus a stream |
| trusted runtime | the runner | the runner, the service, the evaluation workflow |

---

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
  decide (p.π.size ≤ proofCap) && decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) &&
    SigOk vk (traceDigest p.tr) p.σ && decide ((S.V vk c p.π).runSeq p.tr = some true)

structure Certificate (S : Submission) : Prop where
  secure   : ∀ vk, KS (Rel (S.acc vk)) (S.V vk) S.E S.ε S.qV
  complete : ∀ vk, CompleteWithError (Rel (S.acc vk)) (S.P vk) (S.V vk) S.δ
  computes : Computes S.ext S.E S.fuel
  cap      : S.ε ≤ errorCap ∧ S.δ ≤ completenessCap ∧ S.qV ≤ 2 ^ 16 ∧
             (∀ t, S.fuel t ≤ extractorBudget t) ∧ S.ext.body.size ≤ progCap
```

Both caps, `proofCap` and `queryCap`, are `2^20` (`Relation.lean`).

**In words.** A signed proof is accepted for `c` under `vk` when the proof is at most 1 MiB, every
query in the trace is at most 1 MiB, the signature on the trace's digest verifies under `vk`, and
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
| The trace is used up exactly | The signed trace is then exactly `V`'s query sequence: at most `qV` entries, fixed by the verifier's own design. A suffix-tolerant trace gave the relation witnesses with traces of every length, so a fixed-size node prover could not be complete (C-M3). | V4-A3 |
| `queryCap = 2^20` bytes per query in `acc` | Makes `enc64 \|q\|` exact, so the trace encoding is injective on every accepted trace by a fact inside the relation, and a trace-digest collision is a genuine BLAKE2s collision; equals the service's cap. | V4-A3 |
| Conjunct order: size, query cap, `SigOk`, `runSeq` | Cheapest rejection first: a bogus proof costs a signature check (about 300 compressions), not a verifier run. | V4-A3, C-m5 |
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

**Cost of one check** (**estimate**, arithmetic on the layouts): the chain walks take `Σ (3 − dᵢ)`
steps, about 200 for a random digest (192 for the message digits, about 8 for the checksum) and at
most 396; the leaf takes 67 compressions and the path 32. So about 300 compressions on average and
at most 495; a fixed circuit that always takes three steps per chain with selectors pays 498.
**Why `w = 4`** (C-M4 item 5, **estimate**): `w = 2` (265 chains) costs about the same, `w = 16`
(67 chains, 15 steps each) more; a height of 11–12 instead of 16 saves about 3%; `w = 4` with a
flat leaf is near the optimum for this leaf size.

**Why a stateful scheme with no public seed.** No group (V3-5), one hash gadget for agents
(BLAKE2s already proves the chains), the smallest in-circuit check of the hash-based options sized.
It is none of the published schemes (WOTS+, XMSS/RFC 8391, WOTS-TW): it has no public seed and no
bitmasks, so its security is argued directly (§2.5). A per-run public seed in every hash would make
it a WOTS-TW instance at one trusted line and one field of `Sig`, with no in-circuit cost; it is
not adopted (V4-A4), and is the fallback if a reviewer insists on a published scheme.

### 1.4 What v3 contributes verbatim

`Contract/Security.lean`, `Machine.lean` and `Tree.lean` are v3's, word for word (V4-1, V4-16); v3
§6 and §7.1 explain them. In brief:

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
one answer changed (`acc_changed_answer`: both digests verify only if they collide), a
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
harness's checks and the walk, with the PRF challenge as the oracle. For a certified `V` frozen
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
| the walk over the harness's tree, returning leaf starts, a BLAKE2s collision (as an explicit pair), or an explicit signed trace not contained in the log, given a functional log of at most `logCap` entries with potential below 1 and an accepted root | **kernel**, Library (untrusted, kernel-checked): `Library/Compose.lean`, the computable `walk` and the theorem `compose` (V4-8) |
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

**Operational conditions** (§3.2): the index is assigned under one lock and committed before the
signature is returned; the signer refuses after `2^16`; a restart is a new key and aborts the run
(earlier proofs no longer verify under the new `vk`); `k` and the seed are independent `getrandom`
draws.

**Key separation** (C-M4 item 3). If the seed were `k`, every chain start would be an oracle
answer: `PRF_k(0x53 ‖ enc64 j ‖ byte i)` is what the service returns to that 10-byte query, which
any prover may ask, and every signature would be forgeable. Oracle queries carry no tag (V4-2), so
the derivation's tag `0x53` does not prevent this: the brief's sentence that with the tag "no
oracle query can equal a derivation input even under a shared key" (V4-A4) would hold for a
separation in BLAKE2s's parameter block (its personalisation field), not for a byte in the message.
What the design relies on is the independence of the two draws; the tag only fixes the reference
derivation, and a personalisation is the hardening if a shared key is ever contemplated. The Lean
reference signer (`Library/Signer.lean`: `chainStart`, `sign`, `pk`) is the specification the
service is tested against, derivation included.

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
> rendered challenge (nanoda's result is stated where it ran); the benchmark job, on a
> GitHub-hosted runner, started a fresh service for every timed run, checked every signed proof it
> was given with the compiled `acc` under that run's `vk` within `T_V`, and measured `T_tree` and
> the stream; and the result JSON, binding `vk`, the CPU model, the runner image, the harness commit
> and the service binary's hash, carries a GitHub artifact attestation that verifies against the
> organiser's evaluation workflow. Its reader trusts:
>
> 1. Lean v4.34.1's kernel (and nanoda where it ran), the comparator's export, and Lean core,
>    Mathlib and the pinned packages as hashed in the olean manifest. *(v3 item 1)*
> 2. **The contract**: 10 files, 355 code lines (draft; TODO(A)), no theorem, three standard axioms. It now
>    includes the signature check `SigOk`, the trace digest and `runSeq`, beside v3's security
>    definitions and extractor machine.
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
>    source rule and gate rules 3, 6–9; residual O-12. *(v3 item 5)*
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

**Two jobs** (V4-A2, C-M2). The **certificate job** (source rule, the entry's `lake build`, the
comparator with the Lean kernel, the gate, the axiom audit) is deterministic and may run on any
runner with the cached package tree; the second kernel (nanoda) runs where it fits, and its absence
is stated in the result. Only the **benchmark job** must be the GitHub-hosted runner. Build caps are
set from a measurement on a runner: TODO(B) (the measured `lake build` and nanoda peak RSS, disk and
time of the witness-sending entry, with the log; whether nanoda fits).

**The anchor** (V4-A1, C-M1). A result is a JSON file plus a job log; without an anchor the
leaderboard would trust the submitter, who controls a pull request's own workflow file. So:

- Evaluation runs only from an organiser-controlled workflow definition (`pull_request_target`
  gated by a maintainer label, or `workflow_dispatch` with a PR number), with minimal `permissions`,
  `persist-credentials: false`, and the fork fetched by commit SHA into a directory that is executed
  **only inside the sandbox**. That includes the entry's Lean build, gate and axiom audit, not only
  its prover: `lake build` runs the submission's lakefile and elaborates its files, which is code
  execution. The environment is cleared for every untrusted process.
- The result JSON (with `vk`, CPU model, runner image, harness commit, service binary hash) is signed
  with a GitHub artifact attestation by a separate job that runs no entry code. A record is
  accepted only if `gh attestation verify result.json --owner scaraven --signer-workflow
  scaraven/recursion.fast/.github/workflows/evaluate.yml` passes, which rejects a fork's copy of
  the workflow. The core's reusable `evaluate.yml` has three jobs (certificate, benchmark, attest);
  the submissions repository calls it from `harness/ci-template/evaluate-entry.yml`. Written, not
  yet run on GitHub (stage B interim RESULT; TODO(B)).
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

**No memoisation** (C-m2). The service persists across a stream repeat's requests, which are
otherwise stateless. A cache of answers would let one request write state by asking chosen queries
and the next read it by timing, so every answer is computed when asked; with a PRF, recomputation
costs what a lookup does. The signature index visible in each `σ.idx` is a 16-bit counter one
request can advance and the next can read: harmless at that width, and stated.

**`SIGN` re-evaluates every query** (C-m4): an adaptive verifier's trace costs one `QUERY` per
answer while proving and one PRF per query again at signing. Provers should budget for it; it is
small against the Merkle traffic.

**Placement and memory.** The service computes on the same CPUs as the prover: outside the prover's
CPU budget it would be a free co-processor of billions of compressions (RR-8). The prover's
`oom_score_adj` is raised so that under memory pressure the kernel kills the prover, never the
service, and the kill reason is recorded (C-m4). Memory is capped per cgroup: 11 GB for the prover's
sandbox and 2 GB for the service, 13 GB together (V4-13), so a prover cannot starve the service.

**Tests** (**measured**, stage B, `logs/service/test_service.log` of its worktree): 89 checks
against Python `hashlib.blake2s(key=…)` and an independent Python WOTS, on both the scalar and the
AVX2 path, including the empty message (its only block is the key block, so a cached-key fast path
does not apply, [CGH] §9), every refused cap, 32 concurrent connections, two services giving
different `vk` and answers, and exactly `2^16` signatures followed by `EXHAUSTED`. Still to come:
the derivation and signatures against the Lean reference signer and compiled `SigOk` (TODO(B)).

**Speed** (**measured** on a 4-vCPU QEMU development VM with AVX2, not a runner,
`logs/service/measure-4cpu.log`): a round trip of about 34 µs (median); with batches of 4,096
queries of 64 bytes, about 5.9 M calls/s on one connection and 25 M calls/s on four; 105 ns per
64-byte block hashed 8-way with AVX2 (322 ns scalar); key generation (`2^16` one-time keys) about
1.1 s on four threads; a `SIGN` of 64 queries about 153 µs. Batching is what makes the service
cheap: one call per round trip runs at about 28 k calls/s.

### 3.3 The sandbox and the assembly prover (V4-9, V4-A6)

**The prover is x86-64 assembly** (P4, the user's request): one or more `prover/*.s` files in GNU `as`
syntax (AT&T or `.intel_syntax`), linked with the runner image's `gcc -static -pthread … -lm`
(static glibc, libgcc), no other build input. Source in any language may sit beside it for readers,
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
The binary dispatches on `cpuid` if it wants; a `SIGILL` fails the run. Every untrusted process
(the prover, its build, the badge executables that run the entry's compiled verifier) runs under
`bubblewrap` (stage B's `harness/rfh/sandbox.py`): new user, pid, network and ipc namespaces, no
capabilities, an empty environment, a read-only root holding only its binary, its own directory,
the setup directory and the service's socket; a seccomp filter that fails `ptrace`,
`process_vm_*`, `bpf`, `perf_event_open`, `userfaultfd`, `io_uring`, keyrings, mounts and
namespaces; a memory cap on the whole process tree; `--die-with-parent`. The prover's own user and
pid namespaces already keep it out of the service's memory; the filter is depth (the brief asked
for a separate uid; stage B isolates by namespaces instead, needing no system user). Ubuntu 24.04 restricts
unprivileged user namespaces through AppArmor, which the workflow relaxes for the job; where no
user systemd manager is reachable the memory cap falls back to an address-space limit, recorded as
the weaker method (TODO(B): confirm both against the RESULT).

### 3.4 One evaluation, step by step

| # | Step | Checked or measured | Service |
|---|---|---|---|
| 0 | certificate job | source rule, build, comparator, gate, axiom audit (§3.1) | none |
| 1 | build | the assembly prover, in the sandbox, hashes recorded | none |
| 2 | calibration | `T_triv,best`; the service's calls/s and compressions/s (§3.5) | a calibration instance |
| 3 | **tree** (×3) | fresh starts per evaluation; `PROVER tree DIR`; **timed**: `T_tree` | a fresh lifetime per repeat: every `QUERY` and `SIGN` |
| 4 | root check | compiled `acc` on (`treeRoot`, root signed proof) under that repeat's `vk`; CPU time ≤ `T_V` | none: offline |
| 5 | samples | `acc` on 16 randomly chosen inner signed proofs against the runner's digests | none |
| 6 | canaries | for 8 proofs of each kind, every mutation must be rejected: a byte appended to or removed from the file or `π`, a statement bit flipped, the sibling's statement, one trace answer changed, a trace entry appended, a chain value or the index of the signature changed | none |
| 7 | **stream** (×3) | `M + 1` leaves and `M` merges, a fresh process each, ready handshake, **timed**: `t_link`; every output checked with `acc` within `T_V` | a fresh lifetime per repeat, shared by its requests |
| 8 | liveness | at `r = 1`, `n = 16`: the service logs every query; `ext` runs on `(c, π, L)` within the declared fuel; the output must decode to a witness (`Rel` for a leaf, `acc` on the extracted children for a node) | logging mode |
| 9 | DoS | the maximum `acc` time over random signed proofs, published | none |
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
  process, released one at a time. `t_link` is the mean leaf time plus the mean merge time, median of
  three repeats. Under the SROM a link also costs its `SIGN` calls, on the clock.
- **`T_V`** (V4-12, C6): CPU time of one `acc` check on one pinned core must be at most
  `T_triv,best / R`, `R = 10`, where `T_triv,best` is measured **in the same job** by the
  organiser's interleaved compiled-Lean chain checker over the tree's chains (`2^24` compressions).
  It applies to the root, the samples and every stream output. Stage B's checker takes 3.08 s on
  the season shape on one pinned core of the development VM, 183 ns per compression (**measured**,
  stage B interim RESULT; TODO(B): its log), so `T_V` would be about 308 ms there; the value on a
  runner is measured in each job. The badge path uses
  the word-level BLAKE2s twin (V4-A7): with the contract's reference BLAKE2s (about 5 µs per
  compression) a root trace of about 8,000 compressions would spend about 40 ms of the cap in
  trusted code (C-m3). TODO(B): `acc` measured on a synthetic `2^16`-query trace.
- **The service calibration column** (C-m8): the service's measured calls/s and compressions/s on
  that runner, published beside every score like `T_triv,best`. Every Merkle hash of every
  commitment is a service call, about `10^8` per tree (**estimate**, [RD] §4.8), so `T_tree` and
  `t_leaf` measure the organiser's IPC and SIMD BLAKE2s as well as the entry. The organiser's
  hashing speed is part of the rules; a faster service in a later season moves every score, and not
  uniformly. The benefit: entries no longer compete on Merkle-hashing craft, only on proving.
- **Recorded with every result**: CPU model, runner image version, `gcc`/`as` versions, the prover
  binary's hash, the harness commit, the service binary's hash, `vk`, nanoda's status.
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
| memory | prover 11 GB, service 2 GB, in separate cgroups (13 GB together) | same | V4-13 |
| job limit | 6 h | 6 h | P3 |

The values are those of stage B's season files (`harness/season.toml`, `harness/smoke.toml`; TODO(B):
confirm against the final RESULT). The benchmark is one 6 h job; its per-run caps add up to more
than that, so an entry whose runs approach the caps does not fit one job (TODO(B): what the
harness does then, and how a paired comparison of records fits).

**Why this shape** (V4-11). The cost model's long shape (`r = 4`, `n = 2^20`) does not fit 16 GB
for a Flock-class prover (**estimate**); `r = 6`, `n = 2^18` keeps its total chain work (`2^24`
compressions) and has more leaves than cores. **Why `K = 20`**: the cost model's own illustration
(`p = 15%` for a leader at leanVM's published 0.394 s step on an M4 Max). `K` is a ratio of times,
so a uniformly slower runner leaves it unchanged; but it was computed for the long shape, whose tree
has 15 nodes against season 1's 63, so it is provisional until a leader exists on CI.

**Provisional entries** (V4-15, C-m13). An entry whose Lean builds but whose certificate does not
check (a `sorry`, a failed gate) may be benchmarked: it is published as PROVISIONAL and never ranked
or recorded. The source rule, the gate's other rules and the sandbox stay mandatory; its numbers
are marked uncomparable (no `T_V` calibration means anything without a certified `qV`); a
maintainer approves the run. This is how the Flock-based baseline (stage F) will be measured.

---

## 4. Incentives and residual risks

### 4.1 The cost model's table under the SROM

What the SROM changes in [CM] §5 is small: it changes what a record certifies, not which strategy
pays.

| Strategy | Under [CM] | Under the SROM |
|---|---|---|
| full witness-sending tree | fails `T_V` by about 10× | unchanged; `acc` adds a signature check and the root's trace, about the same for every entry |
| partial witness-sending at the root (CM-R7) | up to `1/R` of the chain work | unchanged: 10% at `R = 10` |
| concatenating leaf SNARKs | fails `T_V` and `proofCap` | unchanged; also one signature per concatenated child |
| flattening, proof of parent, bundling in the tree | allowed, priced by the stream | unchanged |
| proof of parent, folding from memory, preparation in the stream | stopped by the protocol | unchanged; the service carries no answer state between requests (no memoisation) |
| starts smuggled inside proofs (CM-R1), the tail (CM-R2), higher arity (CM-R3) | bounded, stated | unchanged |
| the service as a free co-processor (CM-R6) | the service in the prover's cgroup | same CPUs as the prover (§3.2); its speed is published |
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
- **checks one signature**: about 300 compressions on average, at most 495, 498 for a fixed circuit;
- **walks the trace in order** (`runSeq`), with no lookup argument.

So the oracle part of a child's verification costs about 1.6× a public-hash Merkle recursion step
per 64-byte query, plus one signature. Two children may share one signed trace through dummy
queries, so one signature per node is possible (V4-A3); per-child cost statements are upper bounds.
For scale, the exploration's estimate for the attested variant D4 was 1.09× a public-hash recursion
step for a spartan-chain child ([RD] §7.3), and D3 +0.5–12% per child for the signature. Whether an
honest recursive entry fits `proofCap` under v4 has not been re-sized (C5, C unsettled 4).

### 4.3 Residual risks

- **The service is accept-all-critical.** One signed answer that is not `PRF_k(q)` lets a prover
  pick its challenges; an index used twice lets anyone forge. Tested against the Lean specification,
  not proved (trust item 7).
- **The service's speed is in every score** (C-m8, CM-R6): published, but a season-2 service moves
  scores non-uniformly. If traffic dominates, W5 (public Merkle hashing, attested Fiat–Shamir
  answers only) is the recorded optimisation, at the price of an extractability heuristic (V4-14).
- **Heterogeneous runners** (P3): only paired comparisons are meaningful; `T_V` self-calibrates
  but CPU time does not remove SIMD (C6, H-m10).
- **No certified entry runs the season-1 shape** (C-m10): the only certified entry on record
  (spartan-chain) would need about 63 GB at `n = 2^18` (**estimate**: 3.95 GB measured at `2^14`,
  Lessons §4, scaled linearly), and its leaf proof is above `proofCap` already at `2^14`
  (1,464,107 B, **measured**).
  The first ranked shape should be the one the first certified entry can run.
- **The certificate job's toolchain** (C-M2, C10): the record's one data point is nanoda at 52 GB
  on one field lemma (v3 §15.4); whether a real entry's second-kernel check fits any runner is
  unmeasured (TODO(B)).
- **CM-R1 … R8** of the cost model, unchanged.

---

## 5. The trusted base and the trusted runtime

**The contract** (`RecursionFast/Contract/`, counted by `scripts/loc.py`; TODO(A): the final
counts; the figures below are a draft taken while stage A was in progress):

| File | Code lines (draft) | What | Change from v3 |
|---|---:|---|---|
| `Contract.lean` | 9 | reading order | — |
| `Hash/Blake2s.lean` | 68 | RFC 7693 | unchanged |
| `Relation.lean` | 38 | digests, tags, caps, chain, statements, `Trace`, `Sig`, `Signed`, `Wit`, `Rel` | signed children; tags `T W K M` added, `R` removed; `queryCap` |
| `Signature.lean` | 31 | `traceDigest`, WOTS digits, chain, leaf, Merkle path, `SigOk` | new |
| `Oracle.lean` | 24 | `OProg`, `runLog`, `runSeq`, `queries`, `bind` | `runSeq` added, `run` moved to Library |
| `Security.lean` | 33 | `KState`, `KS`, `failProb`, `CompleteWithError`, caps | unchanged |
| `Machine.lean` | 62 | the step-counting word machine | unchanged |
| `Extractor.lean` | 51 | tape, `decodeWit` for signed children, budget, `Computes` | output format |
| `Tree.lean` | 8 | `treeRoot` | unchanged |
| `Certificate.lean` | 31 | `Submission` with `vk`, `acc`, `Certificate`, `Declared`, `CertificateR` | `Vb`, `blake2sOracle`, `tagRO` deleted |
| **total** | **355** (draft) | budget ≤ 500 | v3: 292 |

What a human must trust it for: that `Rel` and `acc` say what §1.1 says; that `SigOk` and
`traceDigest` hash exactly the bytes of §1.3 (the service and runner are tested against them); that
v3's definitions are unchanged. Every trusted definition has a positive and a negative control
in `RecursionFast/Controls/` (one module per contract file, plus `Potential`, `LogScan`,
`Completeness`, `Backdoor`, `WitnessSending`; TODO(A): the per-definition list), and the contract
imports Lean core and Mathlib only.

**The trusted runtime** (stage B; interim sizes by `wc -l`, comments included: the service about
1,250 lines of Rust plus a 133-line measurement tool, std only; the runner about 1,800 lines of
Python; TODO(B): final counts):

| Component | Trusted for |
|---|---|
| the service (Rust: PRF, signer, wire protocol, caps) | answers are `PRF_k`; signatures only on traces it computed; index uniqueness; key isolation and freshness; no memoisation |
| the runner (Python: sandbox, assembly build, tree, stream, `acc` badge, canaries, `T_V` calibration, liveness, DoS, score JSON, season file) | the instances, the clock, the caps, running the compiled `acc` on every proof, the published numbers |
| the gate, source rule, axiom audit, manifest (ported from v3) | the badge executables are the kernel-checked terms |
| the CI workflows (the core's reusable evaluation workflow; the submissions repository's caller) | the anchor: untrusted code runs only in the sandbox; the result is attested |

---

## 6. Checks against the record

### 6.1 The constraints C1–C15 of v3 §16

| | Constraint | v4 |
|---|---|---|
| C1 | knowledge is a bounded program | kept verbatim (`XProg`, `Computes`, `B t`); the node decoder's fit to the budget remains an estimate (F-D1) |
| C2 | the certificate says what it does not say | the trust statement names the PRF assumption and every paper step (§2.7); no property rests on review |
| C3 | KS satisfiable by a Merkle/BCS verifier | the potential form is v3's, and so are its controls (`Controls/Potential.lean`: `twoLucky`, `Vcol`, `V24`) |
| C4 | extraction from what the log holds | the clause no longer instantiates the oracle; a bounded node still forces a decoding extractor, paper (#7) |
| C5 | caps admit an honest recursive entry, sized first | **not met**: no sizing redone for v4 (§4.2); no certified entry runs the season-1 shape |
| C6 | succinctness is not wall time | CPU time on one pinned core, calibrated in the same job (V4-12); the SIMD caveat stays |
| C7 | the score prices recursion | `S = T_tree + K·t_link` |
| C8 | completeness with error; the deployment checked concretely | kept; every scored proof checked with `acc`; liveness on the service's authentic log |
| C9 | the badge path linear and strict | `runSeq` linear, strict `decodeWit`, `acc` ordered for rejection, word-level BLAKE2s twin; TODO(B): `acc` timed on a `2^16`-query trace |
| C10 | the toolchain is part of the rules | certificate job separated; build caps from a runner measurement (TODO(B)); nanoda's absence stated |
| C11 | the design space stays open | no menu, no review of `V`, no manual step; the assembly rule fixes the prover's delivery format, not its proof system |
| C12 | the trusted base stays readable | 355 of 500 code lines (draft; TODO(A)), core and Mathlib only, controls for every definition, three axioms |
| C13 | a reference machine before any cap is valued | the GitHub-hosted runner; `T_V` and the service self-calibrate per job; `K` provisional |
| C14 | the pin discipline | unchanged: the submissions repository's pin moves to a core commit on the remote, in its own commit, before any entry is certified against it |
| C15 | every transcript seed binds the statement | not a contract rule; a rulebook rule and the statement-flip canary (`stmt-bit`); the secret key removes the premise of Fenzi's attack (paper) |

### 6.2 The ten criteria of O-25 §11

| # | Criterion | v4 |
|---|---|---|
| 1 | no narrowing of the design space | met in the authors' reading: the rule restricts how the oracle is deployed and what `V` reads (a signed trace), not which proof system; not put to the user |
| 2 | no large human review surface | the recognition rule and the review of `V` are deleted; the contract (355 code lines, draft) and the service (about 1,250 lines of Rust, interim) are read once |
| 3 | no manual intervention | the harness decides; approving a first-time contributor's workflow is compute admission; unlike D4 there is no key release and no designated-verifier window |
| 4 | survives the kernel attacks and the post-hoc one | the backdoor is ported and certified in the model (kernel, `Controls/Backdoor.lean`, `backdoor`; `magic_needs_trigger`: its magic proof is accepted only on a signed trace answering the empty query with the public hash) and stopped by the PRF hybrid (paper); the post-hoc attack needs `PRF_k` wires nobody outside the service can make; its signed-trace variant is uncertifiable (§2.2) |
| 5 | a kernel certificate within the trusted budget | yes: 355 of 500 code lines (draft; TODO(A)) |
| 6 | states its guarantee and adversary | §2.7: PRF, collision resistance, one-wayness, a correct service, the organiser's key management, an attested machine; "ROM-secure ⇒ BLAKE2s-secure" is not claimed |
| 7 | covers the liveness mirror | closed by the same reduction (paper); every scored proof is checked under the deployment |
| 8 | honest recursion expressible | yes: a node checks children against signed traces; the node-clause positive control uses the Lean signer (kernel, `node_of_two_leaves`); the succinct node's extractor is paper (#7) |
| 9 | statement binding of every seed | not mandated by the contract; see C15 |
| 10 | built against a real entry first | in part: the witness-sending entry is to run end to end at the smoke shape once stages A and B merge (TODO(B)); the Flock-based baseline is the first real entry and will be PROVISIONAL; no certified entry runs the season-1 shape |

---

## 7. Decisions taken in the user's absence, and open items

### 7.1 The decisions

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
| V4-12 | `T_V` by CPU time on one core ≤ `T_triv,best / 10`, measured in the same job | C6; self-calibrating |
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

### 7.2 The earlier proposals' decisions these settle

| Id | Settled as |
|---|---|
| RU-1 (leave V3-5 for a trusted service and the PRF assumption) | taken: V4-2, V4-3; W5 not adopted (V4-14) |
| RU-2 (designated-verifier window, or D3) | D3 (P1): no window |
| RU-3 ("a witness or a collision" as `final`) | moot: `final` stays v3's; collisions appear only in the composition walk |
| RU-4 (the shape, or a flattening policy) | both: `r = 6`, `n = 2^18` with flattening allowed, recursion priced by the stream |
| RU-5 (records certify the deployment) | yes, relative to the organiser's key management (V4-A8) |
| RU-6 (R3 D4+, R4 W5) | neither (V4-14) |
| RR-2, RR-7, RR-8 | adopted in substance (V4-2; `Vb` and the recognition rule deleted; the service on the prover's CPUs) |
| RR-3, RR-4, RR-9, RR-11, RR-12 | replaced by signatures; `queryCap` only; no key release; no W5; no D4+ |
| CM-1, CM-4, CM-6, CM-7 | adopted |
| CM-2 | `K = 20` for season 1, provisional |
| CM-3 | modified: `r = 6`, `n = 2^18` instead of `r = 4`, `n = 2^20` (16 GB) |
| CM-5 | `M = 512`, `n_f = 2^16` |
| CM-8 | `R = 10`; R3 not run |

### 7.3 Open items

- **The succinct node** (#7, C4, [RD] RO-1): that a decoding node extractor satisfies `final` within
  `B t` is paper; kernel only for children in the clear.
- **Sizing an honest recursive entry under v4** (C5, C unsettled 4): signature plus trace hashing per
  child against `proofCap`; WHIR-class "yes, barely" is v3's last estimate.
- **The first ranked shape** (C-m10): set it from the first certified entry that runs.
- **The certificate job's resources** (C-M2): measure the entry build and nanoda on a runner.
- **Keyed BLAKE2s as a named assumption** (C unsettled 1): the alternative wording calls it the
  design's one heuristic, since its only analysis is in an ideal-cipher model.
- **Runner facts** (C unsettled 2, 3): which CPU models, whether `pclmulqdq` and AVX2 are on every
  one (to be asserted at job start); whether relaxing AppArmor for bwrap and the user systemd scope
  for the memory cap work on GitHub's runners (written, not yet run).
- **The forgery/collision split in the kernel** (C unsettled 5).
- **`K` and the targets on CI**, once a leader exists; whether CPU time is the right `T_V` measure.
- **The efficient-extraction domain against `logCap`** (O-21, v3).
- **The submissions repository**: its guidance still calls v3 the design in force; a pull request
  there must move the pin and the rulebook to v4.

---

## 8. Where things are

- **This design's implementation**: branch `v4/srom-rules`. Contract `RecursionFast/Contract/`;
  Library `RecursionFast/Library/` (paper theorem, witness-sending entry, reference signer,
  composition, word-level BLAKE2s); Controls `RecursionFast/Controls/`; `scripts/` (line count, gate,
  source rule, axiom audit); the service `service/` (`PROTOCOL.md` normative for provers); the
  runner `harness/` (`FORMAT.md` the signed-proof file, `PROVER.md` the prover interface,
  `season.toml`); `tests/`; `.github/workflows/` (`ci.yml`, `evaluate.yml`); stage records
  `docs/v4/stages/A-contract-RESULT.md` and `B-harness-RESULT.md`.
- **The brief and the attack**: [`v4/BRIEF.md`](v4/BRIEF.md),
  [`v4/reviews/C-design-attack.md`](v4/reviews/C-design-attack.md).
- **The record it inherits**: [V3] [`v3-design-…`](v3-design-agent-written-ROM-SNARK-verifier-for-BLAKE2s-hash-chain-trees-with-Lean-certified-knowledge-soundness.md),
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

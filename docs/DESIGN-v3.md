<!-- Copied from CambridgePQ/recursion.fast/design/DESIGN-v3-narg-rom.md (2026-10-19). This copy is the one the v3 stages implement; keep the two in sync. -->
# recursion.fast v3: a non-interactive argument in the random-oracle model, a digest relation, whole-tree wall time

Status: **design in force** (user decisions of 2026-10-15 to 2026-10-19, `DISCUSSION.md` Q6).
Supersedes `design/DESIGN-v2-chips-walltime.md` (2026-10-14), which remains the design the
repository `/home/devops/Verified-zkEVM/recursion.fast` implements until the v3 stages of §11 are
built. Where v3 is silent, v2's text applies unchanged; where they differ, v3 wins. Finding and
decision IDs of v2 (S*-A*, O-*) are kept; v3 decisions are `V3-n` (§1.2) and new open items
continue the `O-` numbering (§12).

The first-time reader should read §1, §2, §4 and §6 in that order; §8 is the trust statement.

---

## 1. Objective and the one-line pitch

**One line.** Agents submit a hash-based non-interactive argument as two Lean query programs, the
verifier `V` and the honest prover `P`, prove in Lean that `V` is knowledge-sound in the
random-oracle model and that `P` is complete, supply the extractor as a RISC-V image, and are
ranked by the measured wall time of their native prover proving a whole recursion tree of hash
chains on the reference machine.

**What v3 changes and why** (the user's decision of 2026-10-19):

- v2 proved an interactive oracle proof and *compiled* it with the organiser's fixed Merkle plus
  Fiat–Shamir configuration (`Compile.lean`, 141 trusted lines, one hash, one arity, one sponge).
  That forced every agent through one shape of the BCS transform and could not express
  hash-based designs that are not "a succinct verifier per level" at all, such as accumulation
  (ARC, WARP). In v3 the only contract object is the submitted `V`; the commitment and
  Fiat–Shamir layer, or an accumulation scheme, is the agent's design, and the theorem is about
  the argument that is actually executed.
- v2's relation was a fixed circuit class (chips + CCS + bus over GF(2^64)) and the agent had to
  arithmetise the organiser's compiled verifier into it. In v3 the relation is one fixed relation
  over 32-byte digests (§2): hash chains at the leaves, "two accepting child proofs" at the nodes.
  The arithmetisation of `V` is the agent's internal matter, inside their proof. The contract never
  sees a circuit, a field or a size class. **The contract is field-agnostic** (V3-1): no field
  appears in the trusted base.
- v2 scored one 2→1 step. v3 scores the whole tree (throughput) and reports the root step beside
  it (latency), §6.

**What does not change.** The proved object is kernel-checked against a trusted base a
cryptographer reads in one sitting; the executed objects are bound to the proved ones by the
harness order comparator → gate → badge (A6-G0); knowledge means an executable extractor with a
budget (Q1); wall time on one reference machine is the score (Q2); the ROM is the only idealised
assumption (V3-5); composition across tree levels is the standard ROM-recursion heuristic (§5.4).

### 1.1 Architecture at a glance

```
                     TRUSTED (Lean, ≈ 400 code lines, no field)                 EXECUTED (harness)
  ┌──────────────────────────────────────────────────────────────┐
  │ Hash/Blake2s.lean   blake2s256 : ByteArray → Digest           │   leaf instances (s_i, n), fresh
  │ Oracle.lean         OProg α: query programs; run H; runLog L  │   per evaluation
  │ Relation.lean       Digest, Proof, chainEnd, leafStmt,        │        │
  │                     nodeStmt, Wit, Rel V, proofCap, tags      │        ▼
  │ Security.lean       KState (good/bad over logs), KS, Complete │   native prover, one program,
  │ Extractor.lean      image computes E within B(|π|,|L|)        │   the whole tree  ── timed ──▶ T_tree
  │ Machine.lean        Rv64 run with fuel (vendored semantics)   │        │ writes every proof
  │ Tree.lean           treeRoot over leaf digests (runner spec)  │        ▼
  │ Certificate.lean    Submission, Declared, Certificate         │   compiled V on (root, π_root)
  └──────────────────────────────────────────────────────────────┘   ≤ T_V (succinctness cap)
                                   ▲ certified                           sample of inner proofs
   Submission: V, P : query programs over bytes; E : extractor spec;      root step alone ─▶ T_root
   img : RISC-V image; proofs KS, Complete, computes; Rust prover.        extractor liveness at r = 1
```

The relation, in words: a statement is a digest. A leaf digest commits to the end of a Blake2s
chain of a stated length; its witness is the chain's secret start. A node digest commits to two
child digests; its witness is two proofs the submitted verifier accepts. Proving the tree means
proving 2^r leaves and 2^r − 1 nodes, the last one being the root.

### 1.2 Decisions (V3-n)

| Id | Decision | Date |
|---|---|---|
| V3-1 | The contract is field-agnostic: every interface is bytes, the field is inside `V`. "Binary fields only" becomes reference-machine and workload policy (§6.4, §7.5), never a trusted-base rule. | 2026-10-19 |
| V3-2 | The submitted object is a non-interactive argument in the ROM: `V` and `P` as query programs over bytes. No organiser compiler. | 2026-10-19 |
| V3-3 | Knowledge soundness is proved in the ROM in a local query-by-query counting form (§4), Mathlib only; ArkLib's probabilistic notion is the untrusted bridge target (§9). | 2026-10-19 |
| V3-4 | Completeness is proved in Lean for the submitted Lean prover `P` (perfect, over every oracle function, by default; a counted-error form is allowed). The native prover is executed and measured only, never proved equivalent to `P`. | 2026-10-19 |
| V3-5 | ROM-only: no groups, pairings, lattices or other assumptions are admissible. | 2026-10-19 |
| V3-6 | The oracle is instantiated with Blake2s at launch; a domain-separated menu is a declared extension (O-14 reframed, §3.4). | 2026-10-19 |
| V3-7 | One relation over digest statements, parameterised by the submitted verifier (§2). No size class, no admission caps on the relation. | 2026-10-19 |
| V3-8 | Score = whole-tree wall time (board T, ranked); root-step latency (column R) reported; succinctness is a measured admission cap on the verifier (§6.5). | 2026-10-19 |
| V3-9 | The baseline is the witness-sending argument with zero oracle queries, certified, listed and unranked by the succinctness cap; organiser library code that needs a field uses CompPoly's `BF64` and `Ext3` at the pinned revision (§7.4). | 2026-10-19 |
| V3-10 | No ArkLib fork for BCS now; BCS over a fixed compiler becomes a library theorem for agents who take the IOP route, built when upstream's chain merges (§9.2, O-19). | 2026-10-19 |
| V3-11 | v3 is written beside v2; the repository builds it as stages on a branch (§11). | 2026-10-19 |
| V3-12 | Two repositories and pull-request intake, as ots.golf: this repository is the trusted core and holds no entry; submissions, the baseline first, live in a submissions repository and enter by pull request, verified by the harness and benchmarked on the reference machine (§7.7, O-24, stage S7). | 2026-10-19 |

---

## 2. Relation (trusted): digests, chains and nodes

### 2.1 Definition (`Contract/Relation.lean`, about 35 code lines)

```lean
abbrev Digest := Fin 32 → UInt8                 -- the Blake2s output
abbrev Proof  := ByteArray                      -- any bytes, ≤ proofCap

/-- One chain step, tagged (V3-S1-A6): a 33-byte input, one compression. -/
def chainStep (d : Digest) : Digest := blake2s256 (tagChain ++ bytes d)
/-- The end of a hash chain of length `n` from the start `s`. -/
def chainEnd (s : Digest) (n : ℕ) : Digest := chainStep^[n] s
/-- Chains longer than this are not in the relation (V3-S1-A14). -/
def chainCap : ℕ := 2^20

/-- Statement digests. The tags separate the three uses of Blake2s (§3.4). -/
def leafStmt (h : Digest) (n : ℕ) : Digest := blake2s256 (tagLeaf ++ bytes h ++ enc64 n)
def nodeStmt (c₁ c₂ : Digest)     : Digest := blake2s256 (tagNode ++ bytes c₁ ++ bytes c₂)

inductive Wit
  | leaf (s : Digest) (n : ℕ)
  | node (c₁ c₂ : Digest) (π₁ π₂ : Proof)

/-- The one relation, for an instantiated verifier `Vb` (a total function on bytes). -/
def Rel (Vb : Digest → Proof → Bool) : Digest → Wit → Prop
  | c, .leaf s n         => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ π₁ π₂ => c = nodeStmt c₁ c₂ ∧ Vb c₁ π₁ = true ∧ Vb c₂ π₂ = true
```

`Rel` is defined for any `Vb`; the submission plugs in its own verifier instantiated with Blake2s
(§3.2). That self-application happens in the submission's theorem, not in a definition, so there
is no circularity anywhere in the contract.

**Why the chain is bounded** (V3-S1-A14, the Stage S1 review). `n ≤ chainCap` in the leaf clause
keeps completeness from demanding proofs of chains no prover could handle, and keeps a verifier
that recomputes chains from being driven past its time cap by a proof that declares a huge `n`.

**Why digests as statements** (V3-7). One statement type, 32 bytes, at every level. Node
statements do not grow with depth; the children's digests are in the statement and their
preimages, the child statements and proofs, are in the witness. The harness recomputes the root
digest from the leaves by hashing up (§5.1), and the extractor hands back child digests and proofs
one level at a time (§5.3).

**Why `V` is a parameter and not part of the statement.** A function is not data one can hash or
arithmetise; a description of `V` in the statement would put an interpreter into the trusted
relation. Parameterising is free, because the submission fixes `V` and the harness runs exactly
that `V` on the root. v2's two key digests per node statement (`d0`, `d1`) disappear.

**Why the execution trace is not in the witness.** The trace is the witness of the agent's own
circuit for `V`. Their knowledge-soundness proof must contain "a satisfying trace of my circuit for
`V` implies `V` accepts", because that is how their extractor turns a trace into child proofs, and
their completeness proof must contain the converse. Both are lemmas inside the agent's proof,
never contract structure.

### 2.2 Admission (pass/fail, trusted where it is a definition)

| Cap | Where | Value |
|---|---|---|
| `proofCap` | `Relation.lean`; checked by `V`'s wrapper and by the runner on every proof it verifies | 1 MiB |
| chain length `n` | `chainCap = 2^20` in the leaf clause of `Rel`; the benchmark's `n` is an input, carried in the leaf preimage | ≤ 2^20 (the benchmark uses 2^14, §7.1) |
| verifier queries `qV` | declared in the certificate; the error bound charges them (§4.2) | ≤ 2^16 |

There are no caps on the relation itself: no size class, no cell counts, no index. Succinctness
is not a relation property in v3; it is an admission measurement on `V` (§6.5).

### 2.3 Controls (`Controls/Relation.lean`, CI)

Positive: chains of length 1, 2, 16 and `chainCap` against `hashlib` known answers (the commands in
the docstrings); a node with two leaf children under a verifier that recomputes chains. Negative:
a wrong chain end; a chain of `chainCap + 1`; the four tags are pairwise distinct and each
preimage starts with its own; a node whose first or second child is rejected, and a node whose
statement does not match its accepted children; a proof above `proofCap`; a known-gap control,
`Controls/Backdoor.lean`, certifies a verifier that recognises the deployment oracle (§5.4, O-25). Every negative control is a kernel-checked `¬ Rel …` or a `decide`-free `rfl` on
a concrete digest.

---

## 3. What the agent submits and the model

### 3.1 Query programs (`Contract/Oracle.lean`, about 25 code lines)

```lean
/-- A computation that queries one oracle `ByteArray → Digest` and returns an `α`. -/
inductive OProg (α : Type) | ret (a : α) | query (q : ByteArray) (k : Digest → OProg α)

def OProg.run (H : ByteArray → Digest) : OProg α → α                      -- any oracle function
abbrev Log := List (ByteArray × Digest)                                   -- a partial oracle table
def OProg.runLog (L : Log) : OProg α → Option α   -- answers from `L` only; `none` on a miss
def OProg.queries (H : ByteArray → Digest) : OProg α → List ByteArray       -- what a run asked
```

`OProg` is inductive, so every program terminates; the query count of `V` is bounded by the
declared `qV` (`Certificate`, checked as a theorem `∀ H c π, (V c π).queries H |>.length ≤ qV`).
The information-theoretic model is the one v2 had, one level down: v2 modelled oracle access to
IOP messages, v3 models oracle access to one random function.

### 3.2 The submission (`Contract/Certificate.lean`)

```lean
structure Submission where
  V   : Digest → Proof → OProg Bool            -- the verifier, a query program
  P   : Digest → Wit → OProg Proof             -- the honest prover (Lean; executable)
  E   : Digest → Proof → Log → Option Wit      -- the extractor's specification
  img : Image                                  -- the extractor as a RISC-V image (Q1)
  ε   : ℝ≥0                                    -- per-fresh-query knowledge error (§4.2)
  qV  : ℕ                                      -- verifier query bound
  fuel : ℕ → ℕ                                 -- step budget of `img` as a function of the tape length (≤ B)

/-- `V` with the oracle instantiated: the function the relation and the harness use. -/
def Submission.Vb (S : Submission) : Digest → Proof → Bool :=
  fun c π => if π.size ≤ proofCap then (S.V c π).run (fun q => blake2s256 (tagRO ++ q)) else false

structure Certificate (S : Submission) : Prop where
  secure   : KS (Rel S.Vb) S.V S.E S.ε S.qV             -- §4.2
  complete : Complete (Rel S.Vb) S.P S.V                 -- §4.3
  computes : ImageComputes S.img S.E S.fuel              -- §4.4
  cap      : S.ε ≤ errorCap ∧ S.qV ≤ 2^16 ∧ (∀ t, S.fuel t ≤ B t) ∧ S.img.byteSize ≤ 2^20
```

`Declared` and `CertificateR` carry over from v2 (S5-A13, S9-A41): the image literal and the
declared numbers are rendered from the claim and the certificate requires `S.img = D.img`.

**The native prover** is the agent's program in any language, built from source in the sandbox
with the pinned toolchains. It is not proved and need not agree with `P` in any way (V3-4): its
proofs are checked by the compiled `Vb`. `P` exists so that completeness is a theorem and so that
the harness can produce honest proofs and query logs for the extractor's liveness check (§6.3);
`P` may be slow.

### 3.3 The fixed point lives inside `V`

In practice `V` is a universal inner verifier applied to the index of its own circuit, or an
accumulation decider. The circularity is broken the way every recursive SNARK breaks it: the proof
carries a commitment to the key, the circuit checks the opening, and `V`'s Lean definition refers
to the inner verifier and a fixed index, not to itself. The contract does not know and does not
care; it sees a total function on bytes. v2's "fits" condition (the verifier's layout must fit the
size class) is gone: the recursion closes for any agent whose prover can prove its own `V`, and the
score prices how well.

### 3.4 Blake2s in three roles, and the heuristic

Blake2s is (1) the chain hash and statement hash inside `Rel`, concretely; (2) the instantiation of
the oracle `V` and `P` query, concretely at run time; (3) the random oracle in the theorem. Roles 1
and 2 are separated by four one-byte domain tags with distinct first bytes: `tagChain` on every
chain step, `tagLeaf` and `tagNode` on the statement preimages, and `tagRO` that `Submission.Vb`
prepends to every query of `V` and `P` (`blake2s256 ∘ (tagRO ++ ·)`). So no chain, leaf or node
preimage equals an oracle input (V3-S1-A6; without the chain tag a 31-byte query collided with a
chain step). The one place the relation does hash `tagRO` strings is inside `Vb` in the node
clause: that is the recursion itself and is not a collision. Role 3 is the standard heuristic: the
theorem holds for a random function; deployment uses Blake2s. It is stated in §5.4, together
with the tree heuristic and the uninstantiability gap O-25.

**Menu** (V3-6, O-14 reframed). The contract fixes `blake2s256` in `Submission.Vb` and in `Rel`.
A later season may add a second instantiation for role 2 only, by a `Cfg.hash` as in v2 §3.2,
with its own Lean specification and tag. Agents' proofs are in the ROM and unaffected. The
consequence to decide then: with a cheaper oracle the node becomes cheaper than the Blake2s leaf
and the tree time is dominated by leaves.

---

## 4. Security definitions (trusted, `Contract/Security.lean`, about 70 code lines)

### 4.1 The idea

v2's round-by-round definition counted bad challenges per prefix of an interactive transcript.
v3 counts bad oracle answers per prefix of the query log. The agent exhibits a state predicate
on logs and a bad-answer predicate on (log, fresh query, answer) with four laws; the union bound
over all fresh queries is the paper theorem (§4.5). No probability monad, no adversary type:
Mathlib's `Nat.card` over `Digest` is the only measure.

### 4.2 Knowledge soundness

```lean
/-- A knowledge state over logs for the verifier `V`, relation `R` and extractor `E`. -/
structure KState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) where
  good : Log → Prop
  bad  : Log → ByteArray → Digest → Prop
  empty : good []
  step  : ∀ L q a, good L → q ∉ L.map Prod.fst → ¬ bad L q a → good (L ++ [(q, a)])
  final : ∀ L c π, good L → (V c π).runLog L = some true →
            ∃ w, E c π L = some w ∧ R c w

/-- Every fresh query has at most an `ε` fraction of bad answers. -/
def KState.Bounded (k : KState R V E) (ε : ℝ≥0) : Prop :=
  ∀ L q, (Nat.card {a // k.bad L q a} : ℝ≥0) ≤ ε * Nat.card Digest

/-- Knowledge soundness in the ROM, counting form. -/
def KS (R) (V) (E) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  (∃ k : KState R V E, k.Bounded ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV

noncomputable def errorCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 128
```

**Reading.** `good L` says the table `L` admits no accepted-but-unextractable proof of any
statement; `final` is that promise at the end; `step` says a good table stays good after a fresh
query unless its answer is bad; `Bounded` says bad answers are rare. The statement `c` is
quantified only in `final`, so an adversary that chooses `c` after seeing answers is covered
without any union bound over statements: the state is global over the table, as in the
state-restoration treatment of Fiat–Shamir, where the "key" is parsed from the query, not from a
statement fixed in advance.

**Which proofs count.** `runLog L` answers `V`'s queries from the final table only, so the
verifier's own queries are in `L`: they are charged like the prover's (`qV` of them, §4.5).
Repeated queries are not fresh and are not charged.

**What `KState` alone does and does not exclude** (corrected by the Stage S1 review, V3-S1-A13).
Whether a verifier that accepts everything admits a `KState` is equivalent to every digest having
a witness (`acceptAll_kstate_iff`, Library): no digest can be shown to have none, so the state
exists with a non-constructive extractor, and the claim that accept-all "admits no `KState`" is
dropped. The knowledge content of the certificate therefore sits in `ImageComputes` together with
the named extractor and its budget: accept-all with an extractor that returns nothing is not
certified (`final` fails), and an extractor that inverted Blake2s within budget is what accept-all
would need. The controls (`Controls/Security.lean`, `Controls/Certificate.lean`): a `KState` with
`bad := True` is `Bounded` only at `ε ≥ 1`, above `errorCap`; the `step` law is exercised by a
verifier that queries once and accepts, whose any `KState` needs `ε ≥ 1`; the witness-sending
argument has a `KState` with `good := True`, `bad := False` and the identity extractor (positive);
reject-everything is knowledge-sound and not complete, which is why completeness is required;
accept-everything with a nothing-returning extractor, a flipped image bit, a too-low fuel and
`ε = 1` each fail `Certificate`.

### 4.3 Completeness

```lean
/-- Perfect completeness over every oracle function (default). -/
def Complete (R) (P : Digest → Wit → OProg Proof) (V) : Prop :=
  ∀ (H : ByteArray → Digest) c w, R c w → (V c ((P c w).run H)).run H = true

/-- Counted error (opt-in): on all but a `δ` fraction of answer vectors to `P`'s fresh queries. -/
def CompleteWithError (R) (P) (V) (δ : ℝ≥0) : Prop := …   -- counts over `Fin (2^256)^q`
```

Perfect completeness over all `H` is the simplest statement and what Merkle plus Fiat–Shamir
designs satisfy. The counted form admits grinding and proof-of-work rounds; `δ ≤ 2^-64`
(`Certificate.cap`, if the counted form is used). Completeness is required (V3-4), because
knowledge soundness alone is satisfied by a verifier that rejects everything.

### 4.4 The extractor image (Q1, `Contract/Extractor.lean`, about 45 code lines)

v2's image, machine and tape serialisation carry over with the input re-serialised as bytes:
`⟦c, |π|, π, |L|, L⟧` with the log as a length-prefixed list of (query, answer). `ImageComputes
img E fuel` says: for every `c`, `π ≤ proofCap` and every log `L` whose tape fits the machine's
addressable words, the machine run on the image and that tape halts within `fuel t` steps, `t` the
tape length in words, with an output that decodes (through the contract's total decoder) to
`E c π L` (the empty output for `none`; V3-S1-A7). The budget is `B t = 2^40 + 2^8 · t` steps, a
contract constant: linear in the tape with a fixed term, because the straight-line extractor's work
is reading the log and running the agent's decoder, and a budget in a size class no longer exists
(S4-A1's `witCap` becomes the output cap `2^24` words, a cap on the image, since every `Rel`
witness fits in far fewer). The Stage S1 review removed an earlier `2^24`-entry bound on the log,
which would have limited efficient extraction to 2^24 queries against the 2^64 of §4.5, and moved
the budget from log entries to tape words, so that a log of huge entries cannot exhaust it (A12).

### 4.5 What the paper theorem says

For every adversary making `Q` oracle queries, the probability over the random oracle that the
adversary outputs `(c, π)` with `V^H c π = true` and `E c π L ∉ Rel c` is at most
`(Q + qV) · ε`: by `step` and `Bounded`, the table is good at the end except with that
probability, and by `final` a good table makes every accepted proof extractable. At the caps,
`ε ≤ 2^-128` and `qV ≤ 2^16`, an adversary with `2^64` queries has advantage `≤ 2^-64 + 2^-112`.
Whether to tighten `errorCap` is O-21. The bridge to the probabilistic statement, in VCVio's
terms, is §9.1.

---

## 5. Recursion

### 5.1 The tree (`Contract/Tree.lean`, about 15 code lines, a specification of the runner)

Leaves `i = 0 … 2^r − 1` have starts `s_i` (fresh per evaluation, §6.3), one length `n`, ends
`h_i = chainEnd s_i n` and digests `c_i = leafStmt h_i n`. `treeRoot : List Digest → Digest` pairs
adjacent digests with `nodeStmt` until one remains. The runner computes `treeRoot` in Python
from the leaf digests (tested against the Lean definition by a known-answer control) and runs the
compiled `Vb` on `(treeRoot cs, π_root)`.

### 5.2 Proving a node

The native prover, for a node with children `(c₁, π₁)` and `(c₂, π₂)`, must produce `π` with
`Vb (nodeStmt c₁ c₂) π = true`. By `Rel`, that means proving knowledge of two proofs `Vb`
accepts: the agent's circuit for `Vb`, run twice, or an accumulation step. The verifier's cost is
priced by the prover's time for the node, which is the v2 mechanism (S9-A35) with the circuit
inside the agent's prover instead of inside the contract.

### 5.3 What knowledge soundness gives the tree

An accepting root proof yields, by `final`, child digests and proofs that `Vb` accepts; by the
same theorem one level down, their children; and at the leaves, chain starts. Knowledge
soundness therefore also enforces the topology: a prover cannot flatten the tree and skip the
nodes without contradicting the theorem, since valid child proofs must be extractable from its
own log.

### 5.4 What is *not* claimed

- **Composition across levels.** The theorem is for one level. Peeling the tree re-runs the
  extractor on extracted proofs whose query logs nobody holds; that is the standard
  ROM-recursion heuristic, as in v2 §6.6 and in every deployed recursive SNARK.
- **Blake2s is a random oracle.** The theorem holds for a random function; deployment uses
  Blake2s with the tags of §3.4.
- **A certified `V` may recognise the deployment oracle** (the Stage S1 review's major M1, open
  item O-25). `V`'s local computation is unrestricted, so it may compute Blake2s itself, compare
  with the oracle's answer, and on a match accept a fixed "magic" proof; among all oracle
  functions the match is a `2^-256` event, so `KS` and `Complete` hold, and the probe
  `Controls/Backdoor.lean` certifies exactly such a `V` (kernel-checked). This is the
  Canetti–Goldreich–Halevi uninstantiability of the ROM. No salt helps (the proof can carry it), a
  secret-keyed oracle is impossible because the recursion circuit evaluates the oracle, and v2 had
  the same exposure through recomputed Fiat–Shamir challenges. It passes every harness check of
  §6.3. Until O-25 is resolved, board T relies on the rule of §6.7 and review of `V` at intake.
- **The native prover's correctness**, or its completeness on statements outside the benchmark.
  Only the proofs it writes are checked.
- **Efficiency of `E` beyond the budget**, and any security of `Vb` on proofs above `proofCap`
  (`Submission.Vb` rejects them).

---

## 6. Scoring: whole-tree wall time on the reference machine

### 6.1 Principle (Q2 as resolved in v2, V3-8)

One reference machine, measured wall time, no cost model. The agent's native prover is one
program that proves the whole tree; the clock runs from its start to its exit (the makespan).
The prover schedules its own parallelism on the fixed core count.

### 6.2 Boards and columns

| Board | What | Status |
|---|---|---|
| **T** | wall time of the whole-tree prover run at depth `r = 8`, chain length `2^14` (§7.1): 256 leaves, 255 nodes | **ranked** |
| R | the root step alone: a fresh prover process given the two level-7 proofs and digests from the T run | reported beside T, not ranked |
| DoS | maximum `Vb` time over 1,000 random proofs (v2 §6.3 item 7) | published; a crash or an accept rejects |

Board L (leaf proving) and board W (v2's whole tree with per-step processes) are retired: T is
the whole tree, and a leaf board is won by a prover that recomputes the chain (S9I-M1); the
succinctness cap of §6.5 is what rules that out at the root, where it matters.

### 6.3 Benchmark run (one evaluation)

1. **Instances.** `2^r` chains, starts `s_i` from `os.urandom` per evaluation, held by the runner
   (S9-A38); the runner writes each start only into the prover's input directory. Leaf and root
   digests are the runner's (`treeRoot`); the prover receives the starts and `n`, never a digest
   it could substitute.
2. **Setup** (untimed, ≤ 1 h, sandboxed): the native prover's build, and an optional `setup`
   invocation for its own keys, with no access to the instances.
3. **Tree** (timed): `PROVER tree DIR`, one process, all cores, no network, no GPU, in its own
   sandbox and memory cgroup (v2 §6.4, S6b-A23); writes `proofs/<path>.bin` for every node and
   leaf, and `root.bin`. Budget `tree_s` (§6.6).
4. **Root check** (untimed, ≤ `verify_s`): the compiled `Vb` on `(treeRoot, root.bin)`; must
   accept. **Succinctness cap**: its wall time must be ≤ `T_V` (§6.5).
5. **Sample checks** (untimed): `Vb` on 16 inner proofs chosen at random against their runner
   digests; every one must accept. Defence in depth: the root check suffices under the theorem.
6. **Root step** (timed, column R): `PROVER node DIR` with the two level-7 children's digests and
   proofs copied from step 3; its output must verify.
7. **Canaries** (S9-A37): the first 8 proofs of each kind must be rejected with one appended byte,
   with the last byte removed, with one statement bit flipped and under a swapped child digest.
8. **Extractor liveness** (untimed): at `r = 1`, `n = 16`, the harness runs the compiled
   Lean prover `P` with a logging Blake2s wrapper, feeds `(c, π, L)` to `img` on the contract
   machine (the riscv-zkvm emulator, differential-tested against `Machine.run` as in v0.3), and
   requires an output decoding to the witness within `fuel t` steps, `t` the tape length, for one
   leaf and one node; the log must contain the verifier's queries as well as the prover's.
9. **Repeat** steps 3 to 6 three times on the same instances; `T_tree` and `T_root` are medians.
10. **DoS column** as in v2 §6.3 item 7, on the root digest.

**The prover interface.** `PROVER tree DIR` reads `DIR/leaves.json` (`n`, and for each leaf `i`
the start `s_i` in hex) and writes `DIR/proofs/L<i>.bin`, `DIR/proofs/N<level>_<j>.bin` and
`DIR/root.bin`. `PROVER node DIR` reads `DIR/child1.{stmt,proof}`, `DIR/child2.{stmt,proof}` and
writes `DIR/proof.bin`. The verifier is `verify STMT.hex PROOF.bin`; exit 0 is accept. The
runner never passes a digest to `tree`, and never passes a start to `node` or `verify`.

**What a result was measured under** carries over (S9-A39): `config_sha256`, `hardware_id`,
`entry_id` over `verify`, the prover's source and build, the claim.

### 6.4 Measurement policy (carried over from v2 §6.4, with two changes)

The reference machine, isolation, timed region, record rule (paired ABBA confirmation, 5 pairs,
median ratio ≤ 0.97, calibration before ranking), Sybil limit and re-run policy are v2's. The
changes:

- **Field policy** (V3-1). The machine still exposes carry-less multiply (`pclmulqdq`,
  `vpclmulqdq`, `gfni`; Zbc on RISC-V) so that binary fields are not disadvantaged, and has no
  GPU. The field is the agent's choice and is priced by this hardware; a binary-field board by
  declaration is a scoring option (§7.5), not a rule.
- **One process per tree.** The memory cgroup caps the whole process tree of the single prover
  run at `mem_gb` (96 GB on the proposed 128 GB machine, O-6); the step start-up overhead that
  dominated v2's smoke timings is paid once.

### 6.5 Succinctness: an admission cap on the verifier (new; the reason it is needed)

With 32-byte witnesses, no proof-size cap separates a SNARK from the witness-sending argument:
the trivial root proof is `2^r · 32` bytes, 8 KiB at `r = 8`, under any sensible cap. What
separates them is verifier time: the trivial verifier recomputes `2^r · n` Blake2s
compressions, a SNARK verifier does polylogarithmic work. So:

- **Rule.** The root check (§6.3 step 4) must complete within `T_V` on the reference machine, with
  the compiled `Vb`. Default `T_V = 2 s`. A violation rejects board T and column R.
- **Calibration against the baseline.** Each season the trivial baseline (§7.3) is run at the
  benchmark size and `T_V` must satisfy `T_triv ≥ 5 · T_V`; otherwise `n` is raised. Estimates
  from the compiled-Blake2s measurements of O-9 (5.3–7.0 µs per compression): at `r = 8`,
  `n = 2^14` the trivial root check takes 22–29 s; a FRI-shaped verifier with `2^12` compressions
  and `2^20` field operations in compiled Lean takes 0.5–2 s. The margin is 10× or more.
- **Why a measurement.** A proof-checkable bound needs a cost model of `V`'s computation, which
  is either a RISC-V image of the verifier with a proved step bound (v0.3's `Agrees.lean`; a
  program-verification effort that would dominate the agent's work) or a circuit size (which v3
  deliberately keeps out of the contract). An admission measurement with a 10× margin is immune
  to the noise that matters for ranking.
- **Upgrade path** (O-18): the deterministic step count of an organiser-compiled RISC-V image of
  `Vb` on the contract machine, replacing wall time by a machine-independent number with the
  same margin; needs a Lean-to-RISC-V build of the badge executables, which is O-12's territory.

### 6.6 Caps (pass/fail, never scored)

| Cap | Default |
|---|---|
| `lake build` of the submission | ≤ 1 h, ≤ 48 GB |
| harness (comparator + nanoda + gate + axiom audit) | ≤ 2 h |
| proof | ≤ 1 MiB (`proofCap`), every proof the runner verifies |
| verifier queries `qV` | ≤ 2^16 (certificate) |
| per-query knowledge error `ε` | ≤ 2^-128 (`errorCap`) |
| completeness error `δ` (counted form) | ≤ 2^-64 |
| extractor steps | `B t = 2^40 + 2^8·t`, `t` the tape length in words; declared `fuel t ≤ B t` |
| extractor image | ≤ 2^20 bytes; output ≤ 2^24 words |
| native prover build + setup | ≤ 1 h, in the sandbox |
| tree run `tree_s` | ≤ 4 h |
| root step `step_s` | ≤ 600 s |
| one `Vb` run (root, sample, DoS) `verify_s` | ≤ 60 s; the root check also ≤ `T_V` = 2 s (§6.5) |
| memory of the tree run | ≤ 96 GB cgroup `MemoryMax` |
| whole evaluation | derived from the per-process caps (S9-A42) |

### 6.7 Incentive analysis

| Channel | What closes it |
|---|---|
| Witness-sending argument (no proving, root verifier recomputes everything) | §6.5: root check above `T_V`; listed, unranked (§7.3) |
| SNARK leaves, concatenation above (no recursion) | root proof `2^r · |π_leaf|` exceeds `proofCap` for `|π_leaf| ≥ 4 KiB`; root check verifies `2^r` proofs, above `T_V` at any realistic per-proof time |
| Recursion only near the root, concatenation below | allowed; the first recursing node arithmetises `2^j` verifications and pays in `T_tree` |
| A verifier that accepts a magic proof on any oracle | `KS` with the named extractor and `ImageComputes`: the extractor would have to produce a witness, and for a false digest none exists within budget; random-proof DoS column |
| A verifier that accepts a magic proof only when the oracle is Blake2s (O-25) | **not closed by the contract** (§5.4). Rule: `V`'s local computation must not evaluate the oracle's instantiation; review of `V` at intake (S7); the candidate contract fix of O-25 |
| A verifier that rejects everything | `KS` holds, `Complete` fails; no accepting proofs, no score |
| A verifier whose `KState` is trivial | `KState` alone excludes little (§4.2); `ImageComputes` with the budget is the knowledge clause |
| Precomputed proofs | starts are fresh per evaluation; digests depend on them; `setup` sees no instance |
| Reusing one child proof for both children | leaves are distinct with probability `1 − 2^-255` |
| A prover that writes invalid inner proofs | root check under the theorem; sample checks; canaries |
| A slow verifier under `T_V` | priced in the node's proving time (§5.2); the cap only excludes linear work |
| Exploiting Blake2s where the relation hashes | four tags with distinct first bytes: `tagChain`, `tagLeaf`, `tagNode`, `tagRO` (§3.4) |
| Grinding / proof of work | allowed through the counted completeness form; costs prover time |
| Level-aware verifiers (cheaper checks for leaf children) | allowed; the proof may carry hints, the digest does not |
| Field choice | free; the machine has carry-less multiply and no GPU (§6.4) |
| Parallelism, memory, timing noise, Sybil, records | v2 §6.4 unchanged: fixed cores, cgroup cap, medians, paired ABBA, one ranked entry per submitter |
| Gaming column R with a special-cased root | R is measured on the T run's own level-7 outputs, in a fresh process |
| Compiled-code forgery on the badge path | the harness order, gate rules 3, 6–9, the source rule; residual O-12 |

---

## 7. Benchmark and baseline

### 7.1 Parameters

| | Ranked (board T) | Smoke / CI |
|---|---|---|
| depth `r` | 8 (256 leaves, 255 nodes) | 2 |
| chain length `n` | 2^14 | 16 |
| why | 256 leaves exceed any core count, so T measures throughput; `n = 2^14` makes one leaf (about 2^14 compressions in-circuit) comparable to one node (two verifier circuits), so neither dominates; the trivial root check is 10× above `T_V` | fast end-to-end |

A hash chain with a private start is still the leaf (v2 §7.1): the witness is the start, the
statement its end; nothing about the chain can be precomputed, and the chain's hash is the
verifier's hash, so one Blake2s gadget serves both.

### 7.2 The leaf and node circuits are the agent's

v2's organiser layout `L_chain(n)` (`harness/gen-chain-layout.py`, 9,225·n + 786,505 cells) is
retired as a contract object. It survives as a worked example in the library for agents who use
a CCS-shaped relation internally, with `check-chain.py` as its oracle.

### 7.3 Baseline (phase 1)

The witness-sending argument: `V c π` decodes `π` as a `Wit` and decides `Rel` directly, with
zero oracle queries (the node case runs `Vb` on the children recursively, so the root proof is the
list of all chain starts); `P c w` serialises `w`; `E` deserialises; `img` copies its input to its
output. `KS` holds with `good := True`, `bad := False`, `ε := 0`, `qV := 0`; `Complete` holds for
every `H` by `rfl` on the decoder; `ImageComputes` is a copy loop with a linear step count. It is
certified, passes the comparator, gate and badge path, proves the smoke tree, and is **listed,
unranked**: at the ranked size its root check takes about 25 s against `T_V = 2 s` (§6.5). Unlike
v2's baseline (S7-A2), its exclusion is a measurement, not a theorem; the measurement is what
calibrates `T_V`.

**Where it lives** (V3-12). The baseline is the first entry of the submissions repository (§7.7),
with that repository's contract pin; this repository holds no entry and keeps only the toy controls
as harness fixtures. Stage S2 builds it there.

### 7.4 The baseline's and the library's field: CompPoly `BF64` and `Ext3` (V3-9)

The contract has no field. Where organiser code needs one, in the library's worked examples, the
controls, and the reference entry of O-7 if funded, it uses CompPoly's
`CompPoly/Fields/Binary/BF64` at the pinned revision `572f997` (2026-09-29, byte-identical to
`main` on 2026-10-19): `BF64 = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, a computable 64-bit carrier
with carry-less product and a two-fold reduction by `0x1B`, Itoh–Tsujii inversion, a bridge
`BF64.toQuot` into `AdjoinRoot basePoly` with a kernel-checked Rabin irreducibility certificate,
little-endian byte serialisation, and `Ext3 = BF64[y]/(y^3 + y + 1)` from CompPoly's computable
extension framework. 1,742 lines, no `sorry`, no `implemented_by`, no `extern`; finiteness is a
proposition, so nothing enumerates the field at executable start-up (the S6b-A5 trap). These are
exactly v2's `K` and `E`, so v2's `Contract/Field.lean` and `Library/Field.lean` are deleted and
their facts imported. Gate rule 6's allowlist gains the `BF64` modules and their closure, and the
manifest is regenerated.

### 7.5 A binary-field track (policy, not contract)

If a season wants a board restricted to binary fields, the certificate carries a free-text
`declared_field` and the organiser reviews the submission's Lean sources by hand before listing
it on that board. The trusted base does not change; the ranked board T stays field-agnostic.

### 7.6 What the organiser runs per submission

The harness order of v2 §7.4 is unchanged (A6-G0): source rule, comparator in a fresh sandboxed
tree, gate in a second fresh tree bound byte for byte, then the badge path. The badge executables
are `verify` (the compiled `Submission.Vb`) and `prove-lean` (the compiled `P` with the logging
oracle, used only by the liveness check); `index` is gone. Rule 4's computable fields are `V`, `P`,
`E` and `img`. The benchmark run is §6.3.

### 7.7 Intake: two repositories, pull requests and CI (V3-12, O-24, stage S7)

The model is ots.golf's (`docs/reference/neighbouring-competitions.md` §1; research note R1 §1.5
and §4), with one change forced by wall-time scoring.

- **Two repositories.** This repository is the trusted core: contract, vendored machine, library,
  controls, harness, challenge stubs, documentation, and no entry. A separate submissions
  repository holds one flat root per entry, the baseline first, a `records.json` registry, and a
  `.contract` submodule pinned to a core commit so that a submitter can run the harness locally.
- **Pull-request intake.** An entry is a pull request that creates or changes only its own root.
  The intake fetches the head commit, exports that root alone as flat regular files, lays it over
  a copy of the trusted core, and runs the harness (§7.6) in the sandbox. Pull requests are never
  merged: after a verdict the intake copies the verified root and its registry entry into the
  submissions repository's `main` in its own commit. Every head is retained under a creation-only
  tag, and the verdict comment with the commit status is the durable record, so the intake host
  is disposable.
- **Where each part runs.** The proof part, source rule, comparator, gate and badge build, needs no
  particular machine and may run on a hosted runner. The benchmark (§6.3) is a measurement and
  runs only on the reference machine (§6.4), by a self-hosted runner or a verifier service the
  intake dispatches to, as the Proximity Prize's remote service does. Both halves report into the
  same verdict. This is the one place the ots.golf model does not transfer: there every score is a
  proof and the pipeline can run anywhere.
- **Contract pin and id.** A protected-file list covers the contract, the vendored machine, the
  lakefile and manifest, the toolchain file, the challenge stubs and the harness scripts; their
  SHA-256 digests are pinned in one file, and the contract id is the digest of that file. Every
  verdict and every record carries the contract id and the core commit. A change to a protected
  file is a contract change: it re-pins, and standing records are ported or revalidated with
  provenance, never silently kept (the record-porting procedure §6.4 names).
- **Records.** The record rule of §6.4 (paired confirmation) applies to board T; `records.json`
  holds, per board, the standing entry with its contract id, hardware id, `entry_id` and the
  verdict's commit. A later identical or copied entry never takes a record.
- **Agent-facing rules.** The submissions repository carries the rules a submitter reads: the root
  layout, the claim file, the allowed imports, the limits, the attribution lines frozen at
  admission, and an untrusted `NOTES.md` journal published whatever the verdict, as ots.golf does
  and as sig.golf's "consequences that bite" does.

What the trusted core already has for this: the harness order, the sandbox, the rendered claim,
the manifest and the gate (§7.6), and the runner's instance secrets (§6.3). What stage S7 adds is
the repository split, the intake automation, the pin file with its id, the registry, and the
dispatch to the reference machine.

---

## 8. Trusted base (what a human must read)

| File | Code lines (estimate) | Status |
|---|---:|---|
| `Contract.lean` (reading order) | 10 | rewritten |
| `Contract/Hash/Blake2s.lean` | 68 | unchanged |
| `Contract/Oracle.lean` (§3.1) | 25 | **new** |
| `Contract/Relation.lean` (§2) | 35 | **new**, replaces `Layout.lean` (80) and `Protocol.lean` (45) |
| `Contract/Security.lean` (§4.2, §4.3) | 70 | **rewritten** over logs; was 55 over rounds |
| `Contract/Extractor.lean` (§4.4) | 45 | byte serialisation; budget `B t` over the tape; was 65 |
| `Contract/Machine.lean` | 109 | unchanged |
| `Contract/Tree.lean` (§5.1) | 15 | **new**, replaces `Recursion.lean` (67) |
| `Contract/Certificate.lean` (§3.2) | 30 | rewritten |
| **deleted** | | `Field.lean` 24, `Shapes.lean` 47, `Layout.lean` 80, `Protocol.lean` 45, `Compile.lean` 141, `Recursion.lean` 67: 404 of v2's 726 |
| vendored Rv64 | 205 declarations reached | unchanged; serves the extractor only (O-16 stands) |

About 400 code lines against v2's 726, no field, no compiler, no circuit class, every file with
docstrings that say what, not how. Budget ≤ 500.

**The complete trust statement** (v2 §8 updated):

> A ranked record means: the kernel accepted `Certificate` for the rendered challenge, and the run,
> every checked proof verifying and the root check within `T_V`, measured the times. Its reader
> trusts:
> 1. Lean v4.34.1's kernel and nanoda, the comparator's export, and Lean core, Mathlib and the
>    packages as hashed in `scripts/olean-manifest.sha256`.
> 2. The contract: 9 files, about 400 code lines, no theorem, three standard axioms.
> 3. The vendored RV64 model (riscv-zkvm `6810fc1`): 205 declarations, for the extractor.
> 4. BLAKE2s = RFC 7693, its collision resistance (the statement tree), and the heuristic that
>    it instantiates the random oracle of the theorem, under the tags of §3.4.
> 5. Knowledge soundness and completeness once per tree level, with no composition theorem
>    (§5.4); the paper union bound of §4.5 from the counting form; and, until O-25, that the
>    submitted `V` does not recognise the deployment oracle (§5.4), which the contract cannot
>    state in the ROM.
> 6. The badge code: what Lean's compiler emitted for `Vb` and `P`, guarded by the source rule and
>    gate rules 3, 6–9; residual O-12.
> 7. Harness tools: `Gate.lean`, the harness order with build binding, the manifest, the axiom
>    audit, the source rule, the renderer, the sandbox.
> 8. Tested, not proved: the runner (Python `treeRoot`, the prover interface, the caps, the
>    succinctness measurement, the liveness check), the riscv-zkvm emulator used for liveness.
> 9. The reference machine and the season's `T_V` calibration (§6.5).
>
> Not trusted: `Library/`, `Bridge/`, `Controls/`, `Clean/`, `probes/`, the baseline, the native
> prover. Not claimed: §5.4.

---

## 9. Libraries (untrusted, kernel-checked)

### 9.1 ArkLib and VCVio: the bridge target

ArkLib's security definitions at the pin `7653a90` are sorry-free; we restate locally for audit
surface (their definitional closure beyond Mathlib is about 33,000 lines across ArkLib, VCVio,
PolyFun and CompPoly) and for churn (the probability layer was rewritten on 2026-09-21 and is
being rewritten again for Lean 4.35.0, VCVio #821 / ArkLib #1251). The bridge is one direction,
contract → ArkLib: the counting form of §4.2 implies the probabilistic straight-line knowledge
soundness over VCVio's lazily sampled random oracle, by the query-by-query union bound that VCVio
proves as `prEvent_randomOracle_le_of_bad_queries` (in VCVio from `d606eab`, 2026-10-03, one
commit past our pin; the bump is O-20). Until the bump, the bridge is stated against our pin's
API as in v2 (`Bridge/ArkLib.lean`), without the ROM instance.

### 9.2 The IOP route: BCS as a library theorem (V3-10, O-19)

Agents who design an IOP and compile it with Merkle trees and Fiat–Shamir need "RBR knowledge
soundness of the IOP implies `KS` of the compiled argument" for their compiler. Upstream is close
to supplying the probabilistic version: VCVio at our pin has Merkle extractability in the ROM
(51 files, sorry-free); ArkLib HEAD `db7005f` has state-restoration knowledge soundness in its
native `Interaction` framework; the open PR chain #1267–#1283 (approved, unmerged, stacked on
`integration/fs-bridge-pr-base-20261004`) adds Fiat–Shamir security, Merkle transfer and a bridge
to the legacy `OracleReduction` framework where the proof systems live. The organiser's library
theorem, for one fixed compiler (v2's `Compile.lean` shape, moved to the library), is a gluing of
those results once that chain has merged. Its counting-form
restatement, which is what an agent needs to discharge `KS`, reuses VCVio's deterministic
extraction kernels and redoes the union bound, which the counting form makes a definition.
Nothing in the contract or the baseline depends on it.

### 9.3 Clean, and other frontends

Clean (`42fe4b26`) remains an optional, untrusted circuit frontend for agents whose internal
relation is Clean-shaped; the `RecursionFastClean` bridge, `toLayout_rel_iff` and the
characteristic-2 balance note (`docs/upstream/clean-char2-balance.md`, O-5) carry over as library
assets. v2's gate rule 9 ("no Clean on the badge path") stays, since `Vb` and `P` are executed.

### 9.4 Candidate IOPs over GF(2^64)

ArkLib PR #383 (completeness and RBR knowledge soundness of Binary Basefold, ring switching and
FRI-Binius, being ported in #1298–#1302; knowledge soundness via unique-decoding proximity,
characteristic 2 plus an additive-NTT basis) is the natural reference IOP for an entry over
`BF64`; whether its basis conditions accept the pentanomial modulus is unchecked (O-22).

---

## 10. What carries over from v2 and what does not

| v2 | v3 |
|---|---|
| `Hash/Blake2s.lean`, `Machine.lean`, vendored Rv64, `Certificate` shape, `Declared`/`img` rendering | unchanged |
| `Extractor.lean` (image, fuel, tape) | kept; input re-serialised as bytes; budget `B t` over the tape |
| `Security.lean` (RBR over rounds) | rewritten over query logs (§4) |
| `Field.lean`, `Shapes.lean`, `Layout.lean`, `Protocol.lean`, `Compile.lean`, `Recursion.lean` | deleted from the contract; `Compile`'s shape and `Layout` move to the library as worked examples |
| Gate rules 1–9, source rule, comparator order, manifest, axiom audit, renderer, sandbox, cgroups | unchanged; rule 4's fields become `V`, `P`, `E`, `img`; allowlist gains CompPoly `BF64` |
| Runner: secrets, sandbox, caps, canaries, DoS, ABBA record rule, calibration | kept; per-step processes become one tree process plus one root step; `treeRoot` replaces `rootOK`; new succinctness and liveness checks |
| `gen-chain-layout.py`, `check-chain.py`, `L_chain(n)` | library examples |
| Clean bridge, ArkLib bridge | kept, untrusted; the ArkLib bridge gains the ROM instance after O-20 |
| Baseline `triv` | re-proved against §4; unranked by measurement (§7.3) |
| `submissions/baseline/` in this repository | moves to the submissions repository as its first entry (§7.7) |
| Boards R (ranked), L, W | T ranked; R a column; L and W retired |

---

## 11. Build order for the organiser (stages on a branch of the v2 repository, V3-11)

The stage protocol of the repository's `CLAUDE.md` applies (implement → adversarial review + golf
→ fix → commit). Each stage says what it must leave behind.

1. **S1 Contract.** `Oracle`, `Relation`, `Security`, `Extractor` (bytes), `Tree`, `Certificate`;
   delete the six v2 files; controls of §2.3 and §4.2; `loc.py` under 500.
2. **S2 Baseline.** The witness-sending argument certified against S1, built as the first entry of
   the submissions repository (§7.7) with its contract pin; `BF64` replaces `Field.lean` in the
   library; allowlist and manifest regenerated. If S7 has not yet created that repository, S2
   creates it with the baseline root alone.
3. **S3 Harness.** Tree generator and `treeRoot` KAT, the prover interface, the succinctness
   cap, sample checks, the liveness check with `prove-lean` and the emulator, gate rule 4's new
   fields, CI.
4. **S4 Library.** v2's `Compile` shape and `Layout` as worked examples with their proofs
   re-targeted to `KS`-shaped obligations where cheap; the counting-form ⇒ probabilistic bridge
   after O-20.
5. **S5 Docs.** `docs/DESIGN.md` ← this file, `docs/RESULT.md` §7 updated, amendments ledger.
6. **S6 (later, O-19/O-7).** The BCS library theorem; a reference entry over `BF64`.
7. **S7 Intake (O-24).** The repository split; the intake automation (fetch, export, lay over the
   core, harness, verdict, snapshot, retention tags); the protected-file pin and contract id with
   the porting procedure; `records.json` and the record rule; the dispatch of the benchmark to
   the reference machine; the agent-facing rules. Depends on O-6 for the benchmark half; the proof
   half can run before the machine exists.

Readiness: nothing in S1–S3 depends on upstream; S4's bridge depends on O-20; S7's benchmark
dispatch depends on O-6.

---

## 12. Open items

| Id | Item | Owner |
|---|---|---|
| O-6 | Reference machine SKU, noise calibration, and now the field policy (carry-less multiply, no GPU) and the tree memory cap (96 GB) | organiser / user |
| O-7 | Whether to fund a reference entry over `BF64` (§7.4, §9.4) | user |
| O-8 | Report rewrite for v3 | report |
| O-9 | Compiled Lean field arithmetic is slow (`K.mul` ≈ 27 µs); now a library and `T_V` concern only, since the contract has no field; CompPoly's `BF64` carrier should be benchmarked compiled | library |
| O-12 | Badge executables regenerated from kernel terms; required before board T opens | organiser |
| O-14 | Hash menu for the oracle instantiation (§3.4) | user / organiser |
| O-15 | Organiser assets, reframed: (1) a verified Blake2s gadget kit for agents' circuits, (2) a verified decoder extractor image, (3) the IOP-soundness library and the BCS theorem of O-19 | organiser / user |
| O-16 | ZiskAccel dead arms in the vendored machine | contract / upstream |
| O-18 | **Succinctness cap as a deterministic step count** of an organiser-compiled image of `Vb` (§6.5 upgrade path) | organiser |
| O-19 | **The BCS library theorem** for one fixed compiler (§9.2): wait for ArkLib #1267–#1283 to merge, then glue | organiser |
| O-20 | **VCVio bump** to `d606eab` or later for the ROM union-bound lemma (§9.1); re-pin, manifest, Clean patches re-verified | organiser |
| O-21 | **Error caps and budgets**: `errorCap = 2^-128` per fresh query gives `2^-64` against `2^64` queries (§4.5); decide whether to tighten to `2^-160` (Blake2s allows it; agents' challenge fields decide what they can meet). The extractor budget `B t = 2^40 + 2^8·t` over the tape length (§4.4) is a placeholder for a later stage to justify against a straight-line extractor's real cost | user / contract |
| O-22 | Whether ArkLib's Binary Basefold (#383 port) accepts `BF64`'s pentanomial basis | library |
| O-23 | **Counted-error completeness** (§4.3): the exact form over answer vectors, and whether `δ ≤ 2^-64` is the right cap | contract / user |
| O-24 | **Intake** (§7.7, stage S7): the submissions repository, pull-request intake with durable verdicts, the protected-file pin and contract id, `records.json`, and the dispatch of the benchmark to the reference machine | organiser |
| O-25 | **Uninstantiability** (§5.4, Stage S1 review M1): a certified `V` may recognise the deployment oracle and accept a magic proof; the probe is a kernel-checked control. Candidate contract fix: make `V` (and `P`) polymorphic in the digest type, `V : ∀ (D : Type) [DecidableEq D], D → Tape D → OProg D Bool`, with statements and the proof's digest slots injected by the contract's wrapper and structured queries `List (ByteArray ⊕ D)` serialised by the contract; such a `V` can compare oracle answers only with each other, never with a value it computed, so no instantiation is recognisable, and the gate checks `V`'s type. Costs: a contract-defined proof grammar with digest slots, a structured query type, about thirty trusted lines, and the agent's arithmetisation at `D := Digest`. Alternatives: a rule plus review at intake (weak against obfuscation); a textual check for the Blake2s constants in `V`'s code (raises the bar only). **User decision** | user / contract |

Resolved by v3: O-1, O-3, O-10, O-11 (the extractor budget is no longer a function of a size
class), O-13 (rule 4 has no `Fin`-family field), O-17 (no `IDX`), the v2 fixed-point part of
O-14 (no `fits`).

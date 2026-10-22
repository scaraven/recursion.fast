# recursion.fast v3: an agent-written ROM SNARK verifier for BLAKE2s hash-chain trees, with Lean-certified knowledge soundness

Status: **the design as it stood when v3 stopped (2026-10-22), with the record of why it stopped.**
This document is self-contained. It folds in every amendment that the stages made to the design
in force (`DESIGN-v3.md` of 2026-10-19 and its ledger `DESIGN-AMENDMENTS.md`, entries V3-S1-A1 …
A27, V3-KS-A1 … A8, V3-S2R-A1 … A9), so that no reader needs the ledger, which no longer exists on
`main`. Decision and finding ids are kept as the sources wrote them (V3-n, O-n, Q-n, D-n, V3-S<n>-M<i>,
ADV-M<i>, O25-M<i>, O25T-M<i>, …) so that the history stays traceable to the archived branch
`v3/contract-archive` (contract state `6202402`; the branch head is `f4de3b8`, which adds only
the `evidence/` folder of probes and interim harness patches) and to the submissions repository.

Its two companions are the lessons document (`v3-lessons-from-building-a-witness-sending-entry-and-an-honest-Spartan-Ligero-SNARK-entry.md`,
cited "Lessons §n") and the O-25 document (`v3-open-problem-ROM-uninstantiability-CGH-backdoors-and-why-each-proposed-fix-failed.md`,
cited "O-25 §n"). §1 is the summary; a first-time reader should then read §2, §3, §5, §7 and §14,
and then §15–§17 (the walls, the constraints and the design space), which are the reason the
record exists. A reader-only path through all three documents: §1, §15–§17 here; then O-25 §0,
§10, §11 and §13; then Lessons §5 and §8.4.

## 1. Summary

**The pitch, in one paragraph.** Agents submit a hash-based non-interactive argument as two Lean
query programs over bytes, the verifier `V` and the honest prover `P`; they prove in Lean that `V`
is knowledge-sound in the random-oracle model (ROM) and that `P` is complete with error at most
`2^-128`; they supply the extractor as a program of the contract's step-counting machine with a
proved step bound; and they are ranked by the measured wall time of their native prover proving a
whole recursion tree of BLAKE2s hash chains on one reference machine. The contract never sees a
circuit, a field or a size class: the one relation is over 32-byte digests (a leaf digest commits
to the end of a hash chain of stated length, a node digest to two child digests whose proofs the
submitted verifier accepts), the arithmetisation of `V` is the agent's own business inside their
proof, and the only idealised assumption is that BLAKE2s instantiates the random oracle.

**What was built** (2026-10-19 to 2026-10-22; Lessons §1):

- **S1, the contract**: 9 trusted Lean files, 292 code lines at the end (budget 500), with
  positive and negative controls for every trusted definition and a kernel-checked certificate
  for the witness-sending argument (`Library/WitnessSending.lean`).
- **S2a, the witness-sending entry** in the submissions repository: certified against the pin
  `15e4ae5`, comparator under both kernels, gate `PASS`, `HARNESS: ACCEPT`; unranked by the
  succinctness cap (root check 20.9 s against `T_V = 2 s` on the development VM).
- **S2-KS, the knowledge-soundness amendment** (PR #11, merged `059812f`): the S1 counting form
  was kernel-checked to be unsatisfiable at `errorCap` for every Merkle/BCS verifier; it became a
  potential on query logs with a log-length guard `logCap = 2^96`, and the paper theorem
  `(Q + qV)·ε` became a kernel-checked library theorem.
- **S2b, the honest entry `spartan-chain`**: a leaf SNARK for the BLAKE2s chain (Spartan-style
  R1CS sumchecks over GF(2^64) with challenges in GF(2^192), 64-bit packing with Frobenius ring
  switching, a Ligero tensor commitment under unique decoding, Merkle and Fiat–Shamir over the
  contract's oracle) with witness-sending nodes; 61 Lean modules, 16,766 code lines, 1,561
  theorems, a dependency-free Rust prover; `Challenge.certified` kernel-checked against the
  amended contract with no hypothesis; `HARNESS: ACCEPT`. Not recursive, and unrankable: its leaf
  at the ranked chain length is 1,464,107 B against `proofCap = 1 MiB`.
- **S2R, the rules stage** (`4b3356a` … `6202402`): the RISC-V extractor image was replaced by a
  deep step-counting word language with a proved step bound (`Computes`, `B t = 2^48 + 2^16·t`);
  perfect completeness over every oracle was replaced by `CompleteWithError` over a lazily
  sampled random oracle with cap `2^-128`; gate rule 4 was repointed; the library's verifier was
  made strict and linear-time.
- **The O-25 exploration** (O-25 document): two design rounds and two adversarial reviews on the
  one gap the contract cannot state.

**Where it hit the wall.** Three walls, each a precise statement rather than a feeling (§15):

1. **O-25.** A certified `V` may recognise the deployment oracle (compute BLAKE2s itself, compare
   with an answer, accept a magic proof). `Controls/Backdoor.lean` is kernel-checked: certified,
   and the deployed verifier accepts a 32-byte proof of every statement. No ROM theorem can see
   it (Canetti–Goldreich–Halevi). In the F2 design track, the only construction found that
   removes it by construction is a contract-owned verifier template over first-order data
   (Candidate T, O-25 §6); the user rejected its wider menu form MG1 on 2026-10-22, in their
   words "this severely restricts the design space for autoresearch agents, while still adding
   a huge gap for reviewing proposals, and requiring manual intervention", and the authors read
   that objection as covering T, which is narrower (§14). Every narrower fix was broken, by a
   kernel probe (the literal trigger, the byte projection, the pre-seed challenge computation)
   or by a paper argument (the Fiat–Shamir obstruction, the post-hoc attack, the field-naming
   density bound). A separate exploration on record, the relativized node relation with an
   attested secret oracle (D-L, §17.1; O-25 §13), proposes closing O-25 by the deployment rather
   than by the verifier's code, at the cost of a trusted harness service; it has had an
   adversarial review and was not put to the user before v3 stopped.
2. **Honest recursion is unproven at the caps, and every way to make room changes the trusted
   base.** By paper estimate (#8), with BLAKE2s-only hashing, R1CS, the provable unique-decoding
   regime and `proofCap = 1 MiB`, only a WHIR-class PCS fits `proofCap` at node size, and only
   just ("yes, barely"); no such PCS has a Lean knowledge-soundness proof. Node extraction is
   decoding a committed word of about `2^29` symbols (#7), and no decoder was written. Preprocessing
   SNARKs and accumulation are not expressible (#8). The honest entry measured only that a Ligero
   leaf does not fit (1,464,107 B); it showed nothing about recursion. Every other route (a hash
   menu, a larger cap, a named proximity hypothesis, an accumulation-shaped relation) changes
   the trusted base or the relation; #8's option (i), accept WHIR-class sizes and say so, changes
   nothing but has no Lean proof behind it.
3. **The scoring rule does not price what it was meant to price.** `T_V` as wall time does not
   exclude the witness-sending argument (37–43 ms with a threaded unrolled BLAKE2s), and board T
   rewards sending witnesses below some level and recursing only above it (#6). The proposed
   rules (CPU time on one core; a cap at every level or ranking the root step) were never
   calibrated, because there is no reference machine.

The constraints these impose on any next design are §16; the directions on record, with their
known costs, are §17.

**Two facts about the archived state.** Neither entry is certified against the archived
contract: S2a was certified at `15e4ae5` and `spartan-chain` at `05fde28`, both with the interim
harness (now `evidence/interim-harness/` on the archive branch), and both use the S1/KS shape
(`img`, `Complete`, `Declared.img`); porting them to the S2R contract (S2R RESULT Q11) never
happened. And the archive branch's head is `f4de3b8`, whose contract state is `6202402`: the two
later commits add only `evidence/`.

## 2. History: how v3 came to be

The competition was designed three times before the Lean of v3 existed, and each time the user
removed a layer that pre-decided the agents' architecture. v3 is the point at which the contract
had nothing left to remove except the verifier itself, which is where it stopped.

- **v0.3 and the report (v1.0, 162 pages, 2026-10-10 to 13).** A universal R1CS relation in three
  size classes over GF(2^64); the verifier a RISC-V image with proved cycle counters; a cost model
  priced by four zkVM profiles. The interactive design discussion (`DISCUSSION.md`, Q1–Q4 and
  Q2 revisited; no Q5 was held, although Q2's note refers to "Q3–Q5"; §14 below) decided: the extractor is a RISC-V program with a proved cycle bound, B(k) = 2^(2k+16)
  (**Q1**); all runs are scored, not only accepting ones (**Q3**); the universal R1CS relation
  stays and semantic relations are rejected because they would put large relation definitions
  in the trusted base (**Q4**, option A); the cost model is too complicated and is parked
  (**Q2**, revisited as "flat instructions plus one hash price", never decided).
- **v2 (2026-10-14 to 18, stages S1–S9 on the core's `main`, now the tag `v2-archive`).** A
  structured relation (chips, each a uniform CCS row gadget, connected by buses, over GF(2^64)); the
  agent submits an interactive oracle proof that the organiser's fixed compiler (`Compile.lean`,
  141 trusted lines: one hash, one arity, one sponge) turns into a non-interactive argument;
  recursion by verifier-as-circuit, the agent supplying the layout of their own compiled verifier;
  the score the measured wall time of one 2→1 step. Its harness (comparator in a sandboxed tree
  with two kernels, the gate with rules 1–9, the source rule, the olean manifest, the badge
  executables bound byte for byte to the kernel-checked build) carries over to v3 unchanged.
- **v3 (decided 2026-10-15 to 19, `DISCUSSION.md` Q6).** The user's gripe with v2: it forces
  every agent through one configuration of the BCS transform and cannot express hash-based
  designs that are not "a succinct verifier per level" (accumulation); fields are a large part of
  the cost and the fixed GF(2^64) relation should not be a contract rule. So in v3 the submitted
  object is the argument itself (`V` and `P` as query programs; **no organiser compiler**), the
  relation is one fixed relation over digests, the contract is **field-agnostic**, knowledge
  soundness is a local query-by-query form over the oracle's log proved with Mathlib only,
  completeness is proved for the Lean `P`, the native prover is only executed and measured, and
  the score is the whole tree (throughput) with the root step reported (latency). ArkLib's
  probabilistic definitions were not used in the trusted base because of audit surface (a
  33,000-line definitional closure through VCVio's probability monad) and churn (two rewrites of
  the probability layer in a month); they remained the untrusted bridge target.
- **The two repositories (V3-12, 2026-10-19).** As in ots.golf: the trusted core holds the
  contract, library, controls, harness tools and design and no entry; a separate submissions
  repository holds one root per entry, the registry, the rulebook `AGENTS.md`, and a `.contract`
  submodule pinned to a core commit. Entries enter by pull request there.
- **The relativized exploration (2026-10-20 to 22, branch `explore/relativized-nark`, head
  `043bcb3`).** In parallel with the O-25 design track, a separate exploration started from the
  user's own idea of a verifier knowledge-sound for a *relativized* recursion relation (children
  accepted "with the same oracle" as the game) and ended with a recommendation for an attested
  secret oracle (D4). It is summarised in O-25 §13 and listed as D-L in §17.1; it was not merged,
  not implemented, and not put to the user before v3 stopped.

What did not change across the three designs: the proved object is kernel-checked against a
trusted base a cryptographer reads in one sitting; executed objects are bound to proved ones by
comparator → gate → badge; knowledge means an executable extractor with a budget (Q1); wall time
on one reference machine is the score (Q2 as resolved in v2); the ROM is the only idealised
assumption; composition across tree levels is the standard ROM-recursion heuristic.

## 3. Architecture at a glance, and the decisions V3-1 … V3-12

The trusted base is nine Lean files that a cryptographer reads in one sitting; everything else
is either kernel-checked against them or executed under a harness that binds the executed code to
the kernel-checked terms.

```
                 TRUSTED (Lean, 292 code lines, no field)                       EXECUTED (harness)
  ┌────────────────────────────────────────────────────────────────┐
  │ Hash/Blake2s.lean   blake2s256 (RFC 7693)                       │   leaf instances (s_i, n), fresh
  │ Relation.lean       Digest, Proof, chainStep, chainEnd, chainCap,│   per evaluation
  │                     leafStmt, nodeStmt, Wit, Rel Vb, proofCap   │        │
  │ Oracle.lean         OProg: query programs; run H; runLog L;     │        ▼
  │                     queries; bind                               │   native prover, one process,
  │ Security.lean       Fintype Digest, errorCap, logCap, KState    │   the whole tree ── timed ──▶ T_tree
  │                     (potential μ), KS, failProb,                │        │ writes every proof
  │                     CompleteWithError, completenessCap          │        ▼
  │ Machine.lean        XOp, XStmt, XProg, XProg.run (step counted) │   compiled Vb on (root, π_root)
  │ Extractor.lean      tape, decodeWit, extractorBudget, Computes  │   ≤ T_V (succinctness cap)
  │ Tree.lean           treeRoot (the runner's specification)       │   sample of inner proofs
  │ Certificate.lean    Submission, Vb, Certificate, Declared,      │   root step alone ─▶ T_root
  │                     CertificateR                                │   extractor liveness at r = 1
  └────────────────────────────────────────────────────────────────┘
   Submission: V, P : query programs over bytes; E : extractor specification; ext : XProg;
               ε, δ, qV, fuel; proofs KS, CompleteWithError, Computes, caps; a native prover.
```

The relation in words: a statement is a digest. A leaf digest commits to the end of a BLAKE2s
chain of a stated length (at most `2^20` steps); its witness is the chain's secret start. A node
digest commits to two child digests; its witness is two proofs the submitted verifier accepts.
Proving the tree means proving `2^r` leaves and `2^r − 1` nodes, the last one the root.

### 3.1 Decisions (V3-n), as finally amended

| Id | Decision | Status at the end |
|---|---|---|
| V3-1 | The contract is field-agnostic: every interface is bytes, the field is inside `V`. "Binary fields only" is reference-machine policy (carry-less multiply, no GPU), never a trusted-base rule. | held; the only reversal on record (Candidate T, O-25 §6) was rejected by the user |
| V3-2 | The submitted object is a non-interactive argument in the ROM: `V` and `P` as query programs over bytes. No organiser compiler. | held; same remark |
| V3-3 | Knowledge soundness is proved in the ROM in a local query-by-query form, Mathlib only; ArkLib's probabilistic notion is the untrusted bridge target. | held, with the form changed from counting to a potential (V3-KS-A1) |
| V3-4 | Completeness is proved in Lean for the submitted Lean prover `P`, **with error `δ ≤ 2^-128` over a uniformly random oracle** (V3-S2R-A2, the user's decision of 2026-10-20; perfect completeness over every oracle function is the case `δ = 0`). The native prover is executed and measured only. | amended |
| V3-5 | ROM-only: no groups, pairings, lattices or named conjectures are admissible. | held; it is what confines proximity arguments to the unique-decoding regime (#8) |
| V3-6 | The oracle is instantiated with BLAKE2s at launch; a domain-separated menu is a declared extension (O-14). | held, undecided menu |
| V3-7 | One relation over digest statements, parameterised by the submitted verifier. No size class, no admission caps on the relation. | held, with `chainCap = 2^20` added to the leaf clause (V3-S1-A20) |
| V3-8 | Score = whole-tree wall time (board T, ranked); root-step latency (column R) reported; succinctness is a measured admission cap on the verifier. | held in form; the measuring rule was found gameable (#6) and its replacement is undecided |
| V3-9 | The baseline is the witness-sending argument with zero oracle queries, certified, listed and unranked by the succinctness cap; organiser library code that needs a field uses CompPoly's `BF64` and `Ext3`. | done (S2a) |
| V3-10 | No ArkLib fork for BCS now; BCS over a fixed compiler becomes a library theorem for agents who take the IOP route, when upstream merges (O-19). | not started |
| V3-11 | v3 is written beside v2; the repository builds it as stages on a branch. | done; the v2 tree was then removed (V3-S1-A27, PR #3) |
| V3-12 | Two repositories and pull-request intake, as ots.golf: the core holds no entry; submissions enter by pull request into a submissions repository, verified by the harness and benchmarked on the reference machine. | the split is done; the intake automation (S7) is not |

## 4. The relation (trusted, `Contract/Relation.lean`, 25 code lines)

The relation is the whole of what the competition asks to be proved: one statement type, 32
bytes, at every level of the tree, and two ways to be true. It is the final text of the archived
branch, which differs from the 2026-10-19 design only by amendments recorded here.

```lean
abbrev Digest := Vector UInt8 32            -- V3-S1-A4: a vector, not `Fin 32 → UInt8`
abbrev Proof  := ByteArray
def proofCap : ℕ := 2 ^ 20                  -- 1 MiB: `Vb` rejects longer proofs
def chainCap : ℕ := 2 ^ 20                  -- V3-S1-A20: the longest chain a leaf may commit to

def blake2sDigest (m : List UInt8) : Digest := …   -- BLAKE2s-256 of a byte string (V3-S1-A3)
def tagChain : UInt8 := 0x43   -- 'C' (V3-S1-A19)
def tagLeaf  : UInt8 := 0x4C   -- 'L' (V3-S1-A5)
def tagNode  : UInt8 := 0x4E   -- 'N'
def tagRO    : UInt8 := 0x52   -- 'R': the prefix of every oracle input (Certificate.lean)
def enc64 (n : ℕ) : List UInt8 := …                -- the 8 little-endian bytes of n mod 2^64

def chainStep (d : Digest) : Digest := blake2sDigest (tagChain :: d.toList)   -- 33 bytes, one compression
def chainEnd (s : Digest) (n : ℕ) : Digest := chainStep^[n] s
def leafStmt (h : Digest) (n : ℕ) : Digest := blake2sDigest (tagLeaf :: h.toList ++ enc64 n)  -- 41 bytes
def nodeStmt (c₁ c₂ : Digest) : Digest := blake2sDigest (tagNode :: c₁.toList ++ c₂.toList)   -- 65 bytes

inductive Wit where
  | leaf (s : Digest) (n : ℕ)
  | node (c₁ c₂ : Digest) (π₁ π₂ : Proof)

def Rel (Vb : Digest → Proof → Bool) : Digest → Wit → Prop
  | c, .leaf s n         => n ≤ chainCap ∧ c = leafStmt (chainEnd s n) n
  | c, .node c₁ c₂ π₁ π₂ => c = nodeStmt c₁ c₂ ∧ Vb c₁ π₁ = true ∧ Vb c₂ π₂ = true
```

`Rel` is defined for any `Vb`; the submission plugs in its own verifier instantiated with
BLAKE2s (§5.2). That self-application happens in the certificate's statement, not in a
definition, so nothing in the contract is circular.

**Why each choice is what it is.**

- **Digests as statements (V3-7).** One statement type at every level; node statements do not
  grow with depth; the children's digests are in the statement and their preimages (child
  statements and proofs) are in the witness. The runner recomputes the root digest from the
  leaves by hashing up (§7.1), and the extractor hands back child digests and proofs one level
  at a time.
- **`V` is a parameter, not part of the statement.** A function is not data one can hash or
  arithmetise; a description of `V` in the statement would put an interpreter into the trusted
  relation. Parameterising is free because the submission fixes `V` and the harness runs exactly
  that `V` on the root.
- **The execution trace is not in the witness.** It is the witness of the agent's own circuit for
  `V`; "a satisfying trace implies `V` accepts" and its converse are lemmas inside the agent's
  proof, never contract structure.
- **`Digest` is a vector (V3-S1-A4).** A function-typed digest is a closure that compiled code
  re-evaluates on every byte read, so a chain step cost 32 evaluations of the previous step:
  measured in the interpreter at 600 ms for 2 steps and 15.5 s for 3 (`32^n`); the vector
  computes 1,000 steps in 428 ms.
- **The chain is tagged and bounded (V3-S1-A19, A20).** Without `tagChain`, a 31-byte oracle
  query's instantiated input (`tagRO ‖ q`, 32 bytes) equalled the chain step of every digest
  starting with `0x52` (V3-S1-A6). With four tags of distinct first bytes, no chain, leaf or node
  preimage is an oracle input; the relation hashes oracle inputs only inside `Vb` in the node
  clause, which is the recursion itself. `chainCap` keeps completeness from demanding proofs of
  chains no prover handles (a SNARK whose leaf circuit covers a range of `n` would otherwise need
  a fallback for every other `n`, and the fallback spreads to the nodes, V3-S1-A14) and keeps a
  verifier that recomputes chains from being driven past its time cap by a proof declaring a
  huge `n` (the submissions agent's finding). It is checked before any hash.
- **`enc64` reads `n mod 2^64`**, which is injective on the admitted range.

**Admission caps that live here.** `proofCap` (checked by `Submission.Vb` and by the runner on
every proof it verifies) and `chainCap` (the benchmark uses `n = 2^14`). There are no caps on
the relation itself: no size class, no cell count, no index. Succinctness is not a relation
property in v3; it is an admission measurement on `V` (§8.5).

**Controls** (`Controls/Relation.lean`, kernel-checked in CI). Positive: chains of length 1, 2
and 16 and the leaf and node preimage layouts against `hashlib` known answers (the `python3 -I`
command in each docstring); a node of two leaf children under a verifier that recomputes chains
(`node_of_two_leaves`, for every two starts and lengths); a chain of exactly `chainCap` is in
the relation (`leaf_at_chainCap`). Negative: a wrong chain end (`wrong_end`, every `Vb`); a chain
of `chainCap + 1` (`leaf_over_chainCap`); the four tags pairwise distinct and `tags_separate` stated
structurally (V3-S1-m7); a node whose first or second child is rejected and a node whose
statement does not match its accepted children (`node_needs_statement`, V3-S1-m1); every
submission's `Vb` rejects above `proofCap` (`Vb_over_cap`), and the witness-sending `V` accepts a
13-level proof of 1,114,024 bytes that `Vb` rejects (`deep_accepted_but_capped`: the cap is what
rejects). Kernel evaluation of BLAKE2s costs about 2.4 s per compression, which is why the
controls evaluate few of them (Lessons §8).

## 5. What the agent submits, and the model

A submission is a verifier and a prover that talk to one oracle, an extractor with the program
that computes it, four declared numbers, and a certificate: knowledge soundness of `V` for the
relation of its own instantiated self, completeness of `P`, the extractor's step bound, and the
caps. The harness runs `V` with BLAKE2s and the prover's proofs; the theorems are about a random
function.

### 5.1 Query programs (`Contract/Oracle.lean`, 22 code lines)

```lean
inductive OProg (α : Type) where
  | ret (a : α)
  | query (q : ByteArray) (k : Digest → OProg α)

abbrev Log := List (ByteArray × Digest)                     -- a partial oracle table, in query order

def OProg.run (H : ByteArray → Digest) : OProg α → α        -- against any oracle function
def OProg.runLog (L : Log) : OProg α → Option α             -- answers from L only (first match); none on a miss
def OProg.queries (H : ByteArray → Digest) : OProg α → List ByteArray   -- what a run asked (V3-S1-A24: H first)
def OProg.bind : OProg α → (α → OProg β) → OProg β          -- one program, then another (V3-S2R-A2)
```

`OProg` is inductive, so every program terminates and asks finitely many queries; the
information-theoretic model is v2's, one level down: v2 modelled oracle access to IOP messages,
v3 models oracle access to one random function. The continuation `k` is an arbitrary Lean
function, which is both what makes `V` expressive and what O-25 exploits (`V`'s local computation
is unrestricted, so it may compute BLAKE2s itself).

### 5.2 The submission and the certificate (`Contract/Certificate.lean`, 31 code lines)

```lean
structure Submission where
  V    : Digest → Proof → OProg Bool            -- the verifier
  P    : Digest → Wit → OProg Proof             -- the honest prover (Lean; executable)
  E    : Digest → Proof → Log → Option Wit      -- the extractor's specification (may be noncomputable)
  ext  : XProg                                  -- the extractor as a program of the contract's machine (V3-S2R-A1)
  ε    : ℝ≥0                                    -- per-fresh-query knowledge error
  δ    : ℝ≥0                                    -- completeness error (V3-S2R-A2)
  qV   : ℕ                                      -- verifier query bound
  fuel : ℕ → ℕ                                  -- the program's step budget as a function of the tape length (V3-S1-A21)

def blake2sOracle (q : ByteArray) : Digest := blake2sDigest (tagRO :: q.data.toList)

/-- The instantiated verifier: the function the relation and the harness use. -/
def Submission.Vb (S : Submission) (c : Digest) (π : Proof) : Bool :=
  if π.size ≤ proofCap then (S.V c π).run blake2sOracle else false

structure Certificate (S : Submission) : Prop where
  secure   : KS (Rel S.Vb) S.V S.E S.ε S.qV                   -- §6.1
  complete : CompleteWithError (Rel S.Vb) S.P S.V S.δ         -- §6.4
  computes : Computes S.ext S.E S.fuel                         -- §6.5
  cap      : S.ε ≤ errorCap ∧ S.δ ≤ completenessCap ∧ S.qV ≤ 2 ^ 16 ∧
             (∀ t, S.fuel t ≤ extractorBudget t) ∧ S.ext.body.size ≤ progCap

structure Declared where                        -- rendered from the entry's claim file by the organiser
  ε : ℝ≥0 ; δ : ℝ≥0 ; qV : ℕ ; fuel : ℕ → ℕ

structure CertificateR (D : Declared) (S : Submission) : Prop extends Certificate S where
  bounds : S.ε ≤ D.ε ∧ S.δ ≤ D.δ ∧ S.qV ≤ D.qV ∧ ∀ t, S.fuel t ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t
```

`Declared` and `CertificateR` are v2's pattern (S5-A13, S9-A41): the challenge file the organiser
renders from `claim.json` states the declared numbers, and the entry proves its own are within
them, so a record reports bounds that hold. The extractor program is no longer rendered as a
literal (V3-S2R-A3): `ext` is the submission's own term, executed by the compiled contract
interpreter, and gate rule 4 requires `V`, `P` and `ext` to have compiled code (`E` is
specification data and may be noncomputable).

**The native prover** is the agent's program in any language, built from source in the sandbox
with the pinned toolchains. It is not proved and need not agree with `P` in any way (V3-4): its
proofs are checked by the compiled `Vb`. `P` exists so that completeness is a theorem and so that
the harness can produce honest proofs and query logs for the extractor's liveness check; `P` may
be slow (the honest entry's Lean `P` takes 34.9 s for a 16-step leaf the Rust prover proves in
0.18 s, Lessons §4), and its fuel binds only the certified prover, never the native one.

### 5.3 The fixed point lives inside `V`

In practice `V` is a universal inner verifier applied to the index of its own circuit. The
circularity is broken the way every recursive SNARK breaks it: the proof carries a commitment to
the key, the circuit checks the opening, and `V`'s Lean definition refers to the inner verifier
and a fixed index, not to itself. The contract sees a total function on bytes. v2's "fits"
condition (the verifier's layout must fit the size class) is gone: the recursion closes for any
agent whose prover can prove its own `V`, and the score prices how well. (How hard that is under
the caps is #8 and §15.)

### 5.4 BLAKE2s in three roles, and the heuristic

BLAKE2s is (1) the chain hash and statement hash inside `Rel`, concretely; (2) the instantiation
of the oracle `V` and `P` query, concretely at run time (`blake2sOracle`); (3) the random oracle
in the theorem. Roles 1 and 2 are separated by the four one-byte tags (§4). Role 3 is the
standard heuristic: the theorem holds for a random function; deployment uses BLAKE2s. It is
stated with everything else that is not claimed in §6.7, together with O-25.

**Menu (V3-6, O-14).** A later season could add a second instantiation for role 2 only, with its
own specification and tag; agents' proofs are in the ROM and unaffected. The consequence to
decide then: with a cheaper oracle the node becomes cheaper than the BLAKE2s leaf and the tree
time is dominated by leaves. #8 made this a live question, because an arithmetisation-friendly
hash is one of the four ways to make recursion fit `proofCap` (§13.6).

## 6. Security definitions, as finally amended (`Contract/Security.lean` 33 code lines, `Machine.lean` 62, `Extractor.lean` 35)

The idea in one sentence: instead of a probability monad and an adversary type, the contract
asks the submitter to exhibit a **potential** on the oracle's query log that rises by at most `ε`
on average per fresh answer and below which every accepted proof is extractable; the paper theorem
(`(Q + qV)·ε`) is then a stopped supermartingale and Markov's inequality, and it is kernel-checked
in the library. The uniform average over the `2^256` digests is the only measure.

### 6.1 Knowledge soundness: the potential form (V3-KS-A1, A6, A7)

```lean
noncomputable instance : Fintype Digest :=                    -- V3-KS-A8: noncomputable
  Fintype.ofSurjective (fun f : Fin 32 → Fin 256 => Vector.ofFn fun i => UInt8.ofFin (f i)) …
noncomputable def errorCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 128
def logCap : ℕ := 2 ^ 96                                        -- V3-KS-A6

structure KState (R : Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Wit) (ε : ℝ≥0) where
  μ : Log → ℝ≥0
  empty : μ [] = 0
  step : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256
  final : ∀ L c π, L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
    ∃ w, E c π L = some w ∧ R c w

def KS (R) (V) (E) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  Nonempty (KState R V E ε) ∧ ∀ H c π, ((V c π).queries H).length ≤ qV
```

**Reading.** `μ L` measures how close the table `L` is to admitting an accepted-but-unextractable
proof; `final` is the promise below `1`; `step` says that, below `1` and within `logCap`, the
average over the `2^256` answers to a fresh query of the next potential is at most `μ L + ε`. The
statement `c` is quantified only in `final`, so an adversary choosing it after seeing answers is
covered without a union bound over statements. `runLog L` answers `V`'s queries from the final
table only, so the verifier's own `qV` queries are in `L` and are charged like the prover's;
repeated queries are not fresh and are not charged. Two guards are redundant and spare the
submitter a stopping argument (`KState.step_unstopped`, `KState.final_unguarded`, V3-KS-A7); the
load-bearing restriction is `step`'s `L.length < logCap`. The literal `2 ^ 256` rather than
`Fintype.card Digest` is deliberate: a failing unification otherwise tries to evaluate the
instance ("maximum recursion depth", V3-S2-KS-m2). The instance is `noncomputable` because as a
computable closed term it made every compiled binary that imports the contract enumerate the
`256^32` functions at start-up (a hello-world reached 22.9 GB in 20 s; V3-KS-A8, D-9).

**Why a potential and not a boolean state (V3-KS-A1; #5).** S1's form (`good : Log → Prop`,
`bad : Log → ByteArray → Digest → Prop`, at most `ε·2^256` bad answers for every log of any
length) is embedded as `KState.ofBool` (`μ := 0` on good logs, `1` elsewhere), so nothing a
submitter could do before is lost. The potential also prices a challenge spread over several
answers, which no boolean state can: the query phase of a hash-based IOP draws positions from
`H(T ‖ 1), …, H(T ‖ k)`, its error is the product of the answers' conditionals, and a boolean
state charges the largest conditional per answer (`Controls/Potential.lean`, `twoLucky`: a
potential at `2^-192`, no boolean state below `2^-96` even on short logs; kernel-checked).

**The length guard (V3-KS-A2, A6).** A Merkle commitment binds only up to collisions and late
preimages, whose bad sets have one element per earlier digest of the log; over unbounded logs no
state exists at `errorCap` (`collision_no_bool_kstate`). The guard gives this up: **nothing is
claimed for `Q + qV > logCap`**, where S1's form claimed `(Q + qV)·ε` for every `Q`. Within it a
`t`-bit comparison costs about `logCap · 2^-t` per query, so the value of `logCap` fixes which
collision-type events are chargeable at `errorCap`: at `2^96`, those of at least `224` bits
(birthday cost `2^112`); a full digest costs `2^-160`; an honest Merkle verifier comparing at
most `2^15` digests per query about `2^-145`. The first draft had `2^64`; the review (V3-S2-KS-M1)
showed that value certifies a verifier that compares digests on 24 bytes, 96-bit generic security,
at the 128-bit cap (`Probe.v24_ks`), and the fix moved it to `2^96`, where `v24_no_bool_kstate`
holds. Not kernel-checked: that no *potential* of such a verifier exists at `errorCap` (V3-S2-KS-m1,
`V31`, a paper argument).

### 6.2 What `KState` alone does and does not exclude (V3-S1-A13, A23)

Whether a verifier that accepts everything admits a `KState` is equivalent to every digest having
a witness (`acceptAll_kstate_iff`, library): no digest can be shown to have none, since `nodeStmt`
may be onto. So the knowledge content of the certificate sits in `Computes` together with the
named extractor and its budget (§6.5): accept-all with an extractor that returns nothing is not
certified (`final` fails), and an accept-all extractor within the budget would have to invert
BLAKE2s. The controls: a potential that is `1` off the empty log needs `ε ≥ 1`; a verifier that
queries once and accepts needs `ε ≥ 1` (`queryThenAccept_ge_one`, which is also the control that
`step` is not vacuous, V3-S1-M2); the witness-sending argument's state is `μ := 0`;
reject-everything is knowledge-sound and not complete, which is why completeness is required.
Nothing here constrains how `V` behaves on one particular oracle function: O-25.

### 6.3 The paper theorem (V3-KS-A2; `Library/PaperTheorem.lean`, `paper`, 113 code lines)

For every adversary making `Q` oracle queries with `Q + qV ≤ logCap`, the probability over the
random oracle that it outputs `(c, π)` with `V^H c π = true` and `E c π L ∉ Rel c` is at most
`(Q + qV)·ε`: along the fresh queries, `min 1 μ`, stopped when `μ` first reaches `1`, rises by at
most `ε` in expectation per query (`step`), so it reaches `1` with probability at most `(Q + qV)·ε`
(Markov); otherwise the final log is within `logCap` with potential below `1`, and `final`
extracts. Kernel-checked for a lazily sampled oracle and a deterministic game; the passage to a
random function and to randomised adversaries is standard and on paper. At the caps an adversary
with `2^64` queries has advantage `≤ 2^-64 + 2^-112`, with `2^96` queries `≤ 2^-32`. Whether to
tighten `errorCap` to `2^-160` is O-21, undecided.

**Efficient** extraction (§6.5) is claimed only for tapes of at most `2^64` words with queries
under `2^64` bytes, about `2^61` log entries, so the efficient-knowledge claim holds for
`Q + qV ≤ min(logCap, 2^61)` (V3-S2R-A6, A9, #9 item 6). Beyond it the named extractor may be a
non-constructive choice (`choice_certificate`, V3-S2R-m2), and the bound is a soundness-type
statement. With `logCap = 2^96` the two domains disagree; `logCap ≤ 2^58` would make them agree
(S2R RESULT Q3, undecided).

### 6.4 Completeness with error (V3-S2R-A2; O-23 resolved by the user's decision of 2026-10-20)

```lean
/-- The probability that `p` returns `false` under a lazily sampled random oracle started from the
table `L`: a fresh query is answered uniformly and recorded, a repeated one from the table. -/
noncomputable def failProb : OProg Bool → Log → ℝ≥0
  | .ret b, _ => if b then 0 else 1
  | .query q k, L => match L.find? fun e => e.1 = q with
    | some e => failProb (k e.2) L
    | none => (2 ^ 256)⁻¹ * ∑ a : Digest, failProb (k a) (L ++ [(q, a)])

def CompleteWithError (R) (P) (V) (δ : ℝ≥0) : Prop :=
  ∀ c w, R c w → failProb ((P c w).bind (V c)) [] ≤ δ

noncomputable def completenessCap : ℝ≥0 := (2 : ℝ≥0)⁻¹ ^ 128
```

On every statement and witness of the relation, the honest prover's proof, produced and then
verified against **one** random oracle, is rejected with probability at most `δ ≤ 2^-128`. The
prover's queries are sampled like the verifier's, so the verifier sees the answers the prover saw
(`failProb_eq_prob` identifies it with the paper theorem's lazy-sampling probability). This admits
proof-of-work grinding, rejection sampling and challenge-dependent exceptional cases (an
out-of-domain point landing in the evaluation domain, a zero challenge where something is
inverted), which perfect completeness over every oracle function forbade (#8 (2)): an adversarial
`H` defeats any bounded nonce search, and `OProg` is inductive, so unbounded search is impossible.
Perfect completeness is the case `δ = 0` (`Library/Completeness.lean`, `complete_withError_zero`),
so existing arguments port unchanged. Controls (`Controls/Completeness.lean`): `grind_exact`, `k`
nonces fail with probability exactly `2^-k` (the fallback must be an already-tried nonce,
V3-S2R-H-m1); `grind128_complete` at the cap for every relation; `grind127_not_complete`;
`fixed_not_complete`, a verifier that tests one fixed answer is not complete at any `δ < 1/2`
whatever the prover does.

**The grinding arithmetic (the user's decision of 2026-10-20).** A fuel of `T` attempts at
difficulty `2^g` fails with probability `(1 − 2^-g)^T ≈ e^{−T/2^g}`, so `δ = 2^-128` needs
`T ≈ 128·ln 2·2^g ≈ 89·2^g` attempts and `δ = 2^-96` needs `67·2^g`; the expected work `2^g` is the
same, only the certified `P`'s worst-case fuel differs by a constant. The user recommended
`2^-128`, which matches `errorCap`'s scale, with `2^-96` as the alternative; `2^-128` was
implemented, and S2R RESULT Q1 asks for confirmation.

**Two things completeness does not say (V3-S2R-H-M4, H-m7).** It is over a random oracle, so it
does not imply that an honest proof verifies under the deployed BLAKE2s: a `V` that rejects every
honest proof exactly when the oracle is BLAKE2s is certified (the liveness mirror of O-25; it
harms only its submitter, and the harness's concrete checks are the only guarantee, §8.3 step 8).
And it is about `V`, not `Vb` with its size cap: a `V` that accepts only proofs longer than
`proofCap`, with a prover that pads, is complete at `δ = 0` and its `Vb` rejects every proof
(`vb_rejects_all_certified`, V3-S2R-m1); the harness's root check fails such an entry. Requiring
`|P c w| ≤ proofCap` in the completeness clause would exclude the witness-sending baseline, whose
node proofs legitimately exceed the cap (V3-S1-A18), and would still say nothing about BLAKE2s.

### 6.5 The extractor program (Q1 as amended by V3-S2R-A1, A8, A9; `Contract/Machine.lean`, `Contract/Extractor.lean`)

Knowledge needs an *efficient* extractor; otherwise "the extractor finds a witness" collapses to
"a witness exists". The extractor is a program of the contract's step-counting machine:

```lean
abbrev Word := BitVec 64
inductive XOp   | add | sub | mul | mulhu | divu | remu | and | or | xor | shl | shr | ltu | eq
                | clmul | clmulh                       -- one instruction each; clmul/clmulh are pclmulqdq or Zbc
inductive XStmt | op (o : XOp) (d a b : ℕ) | const (d : ℕ) (w : Word) | load (d a : ℕ)
                | store (a s : ℕ) | input (d a : ℕ) | out (s : ℕ)
                | seq (p q : XStmt) | ite (c : ℕ) (p q : XStmt) | loop (c : ℕ) (p : XStmt)
structure XProg where mem : ℕ ; memPerWord : ℕ ; body : XStmt        -- memory mem + memPerWord · t words
def XProg.run (p : XProg) (input : List Word) (fuel : ℕ) : Option (List Word)
  -- one unit of fuel per memory word (charged first) and per statement executed; none if the fuel runs out

def Computes (p : XProg) (E) (fuel : ℕ → ℕ) : Prop :=
  ∀ c π L, π.size ≤ proofCap → (∀ e ∈ L, e.1.size < 2 ^ 64) →
    (extractorInput c π L).length ≤ 2 ^ 64 →
    ∃ o, p.run (extractorInput c π L) (fuel (extractorInput c π L).length) = some o ∧
      o.length ≤ outCap ∧ decodeWit o = E c π L
def extractorBudget (t : ℕ) : ℕ := 2 ^ 48 + 2 ^ 16 * t      -- B t
def outCap : ℕ := 2 ^ 24 ; def progCap : ℕ := 2 ^ 20          -- output words; statements
```

**Why this shape (V3-S2R-H-M1, H-M2, H-m5).** The user's decision of 2026-10-20 reads "the
extractor is a computable Lean function with a proved step bound". It is implemented as a
**deep program** plus a specification `E` tied by `Computes`, because every shallow form fails:
a step monad whose bind takes a Lean continuation lets the continuation compute for free
(kernel-checked, `logs/s2r/probes/Shallow.lean`: `bruteForce_steps : … = 1 := rfl` for a `2^k`
search), and a monad parametric in the word type still lets a continuation read the input bit by
bit and compute any function of the bits uncharged. So the program is **data**: no syntax node has
a function-typed field, every operand is a memory cell named by a constant, an operation reads
two cells and writes one, no statement contains a sub-expression (an expression tree evaluated in
one step would hide a `progCap`-fold factor), and one step is a bounded amount of word-RAM work.
Memory is charged one step per word before the first statement, so steps bound memory, and it is
**affine in the tape** (V3-S2R-A8, review V3-S2R-M1): with one constant, a certified program's
memory was at most about `2^48` words whatever the tape (probe P2), so the stated log-sorting
derivation of the budget was not an algorithm of the machine, and every leaf liveness run would
have allocated a node decoder's memory. The user's reinterpretation is recorded as S2R RESULT Q13,
unconfirmed.

**The tape and the output (V3-S1-A7, A22; unchanged from S1).** `extractorInput c π L` in 64-bit
words: `c` (4 words), `|π|`, `π` packed 8 bytes per word little-endian, `|L|`, then per entry
`|q|`, `q` packed, the answer (4 words). The output **denotes** a witness through the total
decoder `decodeWit` (tag `0` a leaf: start, length word; tag `1` a node: two digests and two
length-prefixed proofs, each at most `proofCap`; missing words read as `0`, trailing words
ignored) rather than equalling a canonical serialisation, which is what lets the witness-sending
program output the proof's words in place. `packBytes`, `wordByte` and `bytesAt` are
specifications: their compiled code is quadratic (563 s to reject a random 1 MiB proof, #10), and
the library has linear twins proved equal.

**Domain and the query bound (V3-S1-A11, V3-S2R-A9).** Proofs of at most `proofCap` bytes, logs
whose queries have fewer than `2^64` bytes each, tapes of at most `2^64` words (the input address
is a word; about `2^61` log entries). The query bound was found by the fix pass's log-scan
control: a length word is the number's low 64 bits, so with a query of `2^64` bytes or more two
logs with different answers would have one tape, and no program could extract from both; without
it no log-reading extractor could be certified. **This is a paper argument** (the ledger entry
A9 gives the construction; it was not kernel-checked; what is kernel-checked is that the log-scan
proof `scan_computes` closes with the bound and could not be closed without it), and it is the
one trusted change of the stage that nobody requested or confirmed: S2R RESULT Q14 asks the user
to confirm it or to prefer a tape of at most `2^61` words, which implies it but shrinks the
domain. Beyond the domain `E` is unconstrained.

**The budget's derivation (V3-S2R-A8; O-21).** A node extractor must decode the Reed–Solomon
word committed in the log, about `2^29` symbols for the node circuit (**estimate**, F1 §3.3):
quasi-linear decoding about `2^38.7` field operations, one GF(2^64) operation about `2^4`
statements, `2^42.7` in all; the fixed `2^48` leaves `2^5` of room. The linear term: copy each
entry's answer and tape position into memory and merge-sort them by answer in a scratch of the
same size (`memPerWord = 2`), `t · log t ≤ 64·t` comparisons of 4-word digests at about `2^5`
statements each, about `2^11` steps per word, inside `2^16`. One linear scan of the log for an
answer is kernel-checked within `16·t` steps (`Controls/LogScan.lean`, `scan_computes`). Within the
domain `B t < 2^81` (`B(2^64) = 2^80 + 2^48`), so enumerating `2^128` candidates is excluded
(`enum_no_computes`: a program enumerating `2^64 − 1` candidates computes no extractor within the
budget, for every specification and fuel), and the relation has no shorter secret. The fixed term
remains a paper estimate: no decoder was written in the language (deviation F-D1, S2R RESULT Q15).
The witness-sending extractor is a 21-statement program with fuel `8·t`.

### 6.6 Recursion and what knowledge soundness gives the tree

An accepting root proof yields, by `final`, child digests and proofs that `Vb` accepts; by the
same theorem one level down, their children; and at the leaves, chain starts. Composition across
levels is **not** a theorem: peeling the tree re-runs the extractor on extracted proofs whose
query logs nobody holds; that is the standard ROM-recursion heuristic, as in every deployed
recursive SNARK and as Barbara–Chiesa–Guan (2024/728) show it must be in a black-box ROM.
Knowledge soundness also **does not enforce recursion** (V3-S2R-A6, #6 (b)): it guarantees that
valid child proofs exist, not that they were produced by recursion. A prover may send witnesses
below some level `j` (witness-sending proofs cost nothing to produce) and run one SNARK per
level-`j` node over all the chains beneath it, replacing 255 node proofs by `2^{8−j} − 1`; at
`j = 8` there is one flat SNARK and no recursion. What prices or forbids this is a measuring rule
(§8.5), not the theorem.

### 6.7 What is *not* claimed

- **Composition across levels** (above).
- **BLAKE2s is a random oracle.** The theorem holds for a random function; deployment uses
  BLAKE2s with the tags of §4.
- **A certified `V` may recognise the deployment oracle** (V3-S1-M1, O-25). `V`'s local
  computation is unrestricted, so it may compute BLAKE2s itself, compare with the oracle's answer,
  and on a match accept a fixed magic proof; among all oracle functions the match is a `2^-256`
  event, so `KS` and completeness hold, and `Controls/Backdoor.lean` certifies exactly such a `V`
  (kernel-checked). No salt helps (the proof can carry it); a secret-keyed oracle is impossible
  **under this node clause**, because the recursion circuit must evaluate the oracle to prove
  `Vb` on a child (a relativized node clause removes that premise and is the route of the
  exploration in O-25 §13); and v2 had the same exposure through recomputed Fiat–Shamir
  challenges. It passes every harness check. The O-25 document is the full record.
- **That honest proofs verify under BLAKE2s** (§6.4).
- **The native prover's correctness**, or its completeness outside the benchmark; only the proofs
  it writes are checked.
- **Efficiency of `E` beyond the budget and the domain**, and any security of `Vb` on proofs
  above `proofCap`.
- **Security under a BLAKE2s collision**, same-tag or cross-tag: the ROM heuristic itself.

## 7. The tree and the benchmark shape

The benchmark is a binary tree of hash chains: the runner picks fresh secret starts, hashes the
leaf digests up to a root with `nodeStmt`, and the prover must produce a proof of the root that
the compiled `Vb` accepts. Every digest the prover must prove is the runner's; every secret is the
runner's.

### 7.1 The tree (`Contract/Tree.lean`, 8 code lines, a specification of the runner)

Leaves `i = 0 … 2^r − 1` have starts `s_i` (fresh per evaluation), one length `n`, ends
`h_i = chainEnd s_i n` and digests `c_i = leafStmt h_i n`. `treeLevel` pairs adjacent digests with
`nodeStmt` and carries an odd last digest up unhashed; `treeRoot cs = (treeLevel^[|cs|] cs).headD 0`
(V3-S1-A8: one digest is its own root, the empty list has the zero digest; the runner always has
`2^r` leaves). The runner computes `treeRoot` in Python from the leaf digests, tested against the
Lean definition by a known-answer control (`treeRoot_kat`, four leaves against `hashlib`), and
runs the compiled `Vb` on `(treeRoot cs, π_root)`.

### 7.2 Proving a node

The native prover, for a node with children `(c₁, π₁)` and `(c₂, π₂)`, must produce `π` with
`Vb (nodeStmt c₁ c₂) π = true`. By `Rel`, that means proving knowledge of two proofs `Vb`
accepts: the agent's circuit for `Vb`, run twice. The verifier's cost is priced by the prover's
time for the node, which is v2's mechanism (S9-A35) with the circuit inside the agent's prover
instead of inside the contract. What the node circuit must contain, at the caps, is #8 (§13.6):
BLAKE2s for the child's transcript (the seed, every absorb and squeeze, every Merkle node), the
fixed sumcheck arithmetic, the matrix evaluation of the child's constraint system at the child's
challenge point, and the commitment checks, all as gadgets over the child's transcript in the
node's witness. **Accumulation is not expressible** (V3-S2R-A6, #8 (4), ADV-M8): the node clause
demands full verification of each child under BLAKE2s, so the accumulator witness would be above
`proofCap`, a decider outside the circuit gives no transfer from the parent's random-`H` theorem
to the child's concrete `Vb`, and the extractor has no source for a child proof. §1 of the
2026-10-19 design named accumulation (ARC, WARP) as a reason for v3; that claim was withdrawn:
v3 as built admits full recursion only, every intermediate proof succinct and fully verified.

### 7.3 Parameters

| | Ranked (board T) | Smoke / CI |
|---|---|---|
| depth `r` | 8 (256 leaves, 255 nodes) | 2 |
| chain length `n` | `2^14` | 16 |
| why | 256 leaves exceed any core count, so T measures throughput; `n = 2^14` makes one leaf (about `2^14` compressions in-circuit) comparable to one node (two verifier circuits; leanVM measures a 2→1 step at about 18,400 compressions, Lessons §5), so neither dominates | fast end to end |

A hash chain with a private start is the leaf because the witness is the start, the statement its
end, nothing about the chain can be precomputed, and the chain's hash is the verifier's hash, so
one BLAKE2s gadget serves both. v2's organiser leaf layout `L_chain(n)` (9,225·n + 786,505 cells)
is retired as a contract object; the leaf and node circuits are the agent's.

**What the shape costs an honest entry (measured, Lessons §4).** At `n = 2^14` the honest
entry's Ligero leaf proof is 1,464,107 B, above `proofCap`; leaves fit only up to `n = 4,096`;
and a witness-sending node embeds its children, so the depth-8 root of 256 leaves fits only for
leaves under 4 KiB. The honest entry's acceptance run is therefore the smoke tree (`r = 2`,
`n = 16`, root 575,112 B). No entry of the shape "SNARK leaves, witness-sending nodes" can be
ranked at this shape, and the shape itself (fewer, longer leaves; `r = 4`, `n = 2^20` was
proposed for `T_V` calibration, #6) was never re-decided.

## 8. Scoring: whole-tree wall time on the reference machine

The score is a measurement, not a proof: one reference machine, the makespan of one prover
process proving the whole tree, medians over repetitions, paired confirmation for records. What
the certificate guarantees is that the proofs mean something; what the measurement guarantees is
that producing them cost what it cost. The two walls of this section are that the admission cap
meant to separate SNARKs from the trivial argument did not, and that the reference machine never
existed.

### 8.1 Principle (Q2 as resolved in v2, V3-8)

One reference machine, measured wall time, no cost model. The agent's native prover is one
program that proves the whole tree; the clock runs from its start to its exit. The prover
schedules its own parallelism on the fixed core count. The field is the agent's choice and is
priced by this hardware (V3-1): the machine exposes carry-less multiply (`pclmulqdq`,
`vpclmulqdq`, `gfni`; Zbc on RISC-V) so that binary fields are not disadvantaged, and has no GPU.

### 8.2 Boards and columns

| Board | What | Status |
|---|---|---|
| **T** | wall time of the whole-tree prover run at `r = 8`, `n = 2^14` | **ranked** |
| R | the root step alone: a fresh prover process given the two level-7 proofs and digests from the T run | reported beside T, not ranked; ranking it is one of the two proposed answers to #6 (b) |
| DoS | maximum `Vb` time over 1,000 random proofs | published; a crash or an accept rejects |

Board L (leaf proving) and board W (v2's whole tree with per-step processes) are retired: T is the
whole tree, and a leaf board is won by a prover that recomputes the chain (S9I-M1).

### 8.3 Benchmark run (one evaluation)

1. **Instances.** `2^r` chains, starts `s_i` from `os.urandom` per evaluation, held by the runner
   (S9-A38); the runner writes each start only into the prover's input directory. Leaf and root
   digests are the runner's (`treeRoot`); the prover receives the starts and `n`, never a digest
   it could substitute.
2. **Setup** (untimed, ≤ 1 h, sandboxed): the native prover's build, and an optional `setup`
   invocation for its own keys, with no access to the instances.
3. **Tree** (timed): `PROVER tree DIR`, one process, all cores, no network, no GPU, in its own
   sandbox and memory cgroup (96 GB); writes `proofs/<path>.bin` for every node and leaf, and
   `root.bin`. Budget `tree_s`.
4. **Root check** (untimed, ≤ `verify_s`): the compiled `Vb` on `(treeRoot, root.bin)`; must
   accept. **Succinctness cap**: its time must be within `T_V` (§8.5).
5. **Sample checks** (untimed): `Vb` on 16 inner proofs chosen at random against their runner
   digests; every one must accept.
6. **Root step** (timed, column R): `PROVER node DIR` with the two level-7 children's digests and
   proofs copied from step 3; its output must verify.
7. **Canaries** (S9-A37): the first 8 proofs of each kind must be rejected with one appended byte,
   with the last byte removed, with one statement bit flipped and under a swapped child digest.
   (The library's own verifier failed two of these until #10 was fixed.)
8. **Extractor liveness** (untimed; V3-S2R-A1, A4; a smoke test, never the security claim, which
   is the proved step bound): at `r = 1`, `n = 16`, the harness runs the compiled Lean `P` with a
   logging BLAKE2s wrapper, **and also** the native prover's proofs with the query log the native
   prover emits (the harness checks every entry's hash and that the log contains `V`'s queries;
   #9 item 1, so that a fallback branch is not the only path exercised). It feeds `(c, π, L)` to
   `ext` on the compiled contract interpreter with the declared `fuel t`, and requires an output
   decoding to a witness: `Rel` for a leaf, `Vb` on the extracted children for a node. A leaf is
   always run. A node is run only when the declared `fuel t` at its tape length is at most a
   liveness cap (proposed `2^36` steps; a node decoder at real size needs about `2^43`,
   V3-S2R-H-M3), otherwise the record says "node liveness not run"; and only when the program's
   memory `mem + memPerWord · t` is within a liveness memory cap (proposed `2^27` words, 1 GiB).
   Both values are the user's and were never set.
9. **Repeat** steps 3 to 6 three times on the same instances, each in a fresh step directory that
   is the only writable path (v2's rule, #9 item 2); `T_tree` and `T_root` are medians. A prover
   that fails to produce an accepted proof fails the evaluation; with `δ ≤ 2^-128` an honest
   prover meets this with negligible error, and the native prover may check its own proofs and
   retry.
10. **DoS column** on the root digest.

**The prover interface.** `PROVER tree DIR` reads `DIR/leaves.json` (`n`, and for each leaf the
start in hex) and writes `DIR/proofs/L<i>.bin`, `DIR/proofs/N<level>_<j>.bin` and `DIR/root.bin`.
`PROVER node DIR` reads `DIR/child1.{stmt,proof}`, `DIR/child2.{stmt,proof}` and writes
`DIR/proof.bin`. The verifier is `verify STMT.hex PROOF.bin`; exit 0 is accept. The runner never
passes a digest to `tree`, and never passes a start to `node` or `verify`. Both entries implement
this interface (Lessons §3, §4).

### 8.4 Measurement policy (v2 §6.4, kept)

The reference machine, isolation, timed region, record rule (paired ABBA confirmation, 5 pairs,
median ratio ≤ 0.97, calibration before ranking), Sybil limit (one ranked entry per submitter) and
re-run policy are v2's. The memory cgroup caps the whole process tree of the single prover run at
96 GB on a proposed 128 GB machine (O-6). What a result was measured under carries over
(S9-A39): `config_sha256`, `hardware_id`, `entry_id` over `verify`, the prover's source and
build, the claim.

### 8.5 Succinctness: an admission cap on the verifier, and why its first form failed (#6)

With 32-byte witnesses no proof-size cap separates a SNARK from the witness-sending argument: the
trivial root proof is `2^r · 32` bytes, 8 KiB at `r = 8`. What separates them is verifier time:
the trivial verifier recomputes `2^r · n` compressions, a SNARK verifier does polylogarithmic
work. The 2026-10-19 rule was "the root check's **wall time** must be within `T_V = 2 s`,
calibrated so that `T_triv ≥ 5·T_V`, with 22–29 s measured for the trivial check and a margin of
10× or more". That does not hold (V3-S2R-A6, ADV-M1). Measured on the development VM for the
whole ranked tree (`2^22` compressions):

| root check: the chain recomputation | time |
|---|---|
| the certified S2a `Vb`, the contract's reference BLAKE2s, sequential | 20.7–21.2 s |
| reference BLAKE2s with `Task.spawn` | 1.17–1.31 s |
| an unrolled BLAKE2s in core Lean, sequential | 0.64–0.69 s |
| unrolled BLAKE2s with `Task.spawn` | **37–43 ms** |

The first row is the certified entry end to end; the other three are **chain-only
microbenchmarks** (`RefChain.lean`, `FastChain.lean`, archived as `evidence/probes/refchain.log`
and `fastchain.log`): no threaded `Vb` was built as a certified entry, and the unrolled BLAKE2s
agrees with `hashlib` on a known-answer chain but was never proved equal to `chainStep`. What is
kernel-checked is that `Task.spawn`/`Task.get` are core definitions with transparent bodies
(`(Task.spawn f).get = f ()` by `rfl`, `TaskRfl.lean`), so a threaded check would be provably
equal to the sequential one and the certificate would carry over; the source rule accepts it. The
conclusion, that a certified entry which proves nothing could win board T, is therefore a strong
paper argument on measured parts, not a measured certified entry. Raising `n` does not close the
gap: at `n = chainCap` the threaded unrolled check extrapolates to about 2.6 s (**estimate,
derived**: 64 × 40 ms) against the required 10 s. The calibration also depends on how well the
trivial baseline is implemented, and a quality difference of about 500× between the certified
verifier and an unproved microbenchmark of the same function (21 s against 40 ms) is larger than
any margin a rule can set.

**Proposed rule (V3-S2R-A7; awaiting the user's value on a reference machine that does not
exist).** Measure the root check's **CPU time** (user + system) on one pinned core, and calibrate
against the organiser's best compiled-Lean chain checker, which interleaves at least 8 chains so
that instruction-level parallelism counts too: `T_V ≤ T_triv,best / 10` (about 65 ms of CPU on the
development VM, an **estimate derived** from the 151–164 ns per compression of the unrolled
microbenchmark; H-m10 notes that CPU time does not remove SIMD, so the measure itself is
unvalidated). If that is below what a compiled-Lean succinct verifier can reach, change the
benchmark shape (`r = 4`, `n = 2^20`). The honest entry's smoke root (four 16-step leaves,
575 KB) verifies in 0.99–1.71 s over nine runs on this VM with a word-level field (1.06–1.45 s
through `Run.verifyProof`; 1.22–1.26 s in the two harness runs; Lessons §4.4), so its margin
under 2 s was as small as 0.29 s; a CompPoly-field verifier would take 4–40 s for a WHIR-class
verifier's `10^4`–`10^5` extension multiplications (an R7 **estimate**) at the measured 415 µs
each (#9 item 9). So `T_V` is bound to compiled field speed, and the order is: fix the measuring
rule, then the shape (A7 lets the rule change the shape), then calibrate `T_V` on the reference
machine.

**Why a measurement and not a theorem.** A proof-checkable bound needs a cost model of `V`'s
computation: a RISC-V image of the verifier with a proved step bound (v0.3's `Agrees.lean`, a
program-verification effort that would dominate the agent's work) or a circuit size (which v3
keeps out of the contract). The step-counting language of §6.5 could price `V` only if `V` were
itself a deep program with an oracle primitive, since `OProg`'s continuations do uncharged work
(V3-S2R-H-M1); that is O-18's upgrade path, recorded and not assumed.

**The recursion incentive (#6 (b), V3-S2R-A7).** Either the CPU-time cap applies to every sampled
proof at every level (a level-`j` witness-sending proof costs `2^{j+14}·160 ns`: about 42 ms at
`j = 4`, 84 ms at `j = 5`, so a 65 ms cap forces recursion from level 5 up and every level needs
`n ≈ 2^20`), or column R is ranked beside T. The user's decision; not taken.

### 8.6 Caps (pass/fail, never scored)

| Cap | Default |
|---|---|
| `lake build` of the submission | ≤ 1 h, ≤ 48 GB |
| harness (comparator + nanoda + gate + axiom audit) | ≤ 2 h |
| second kernel (nanoda) and comparator | **proposed** ≤ 16 GB and ≤ 30 min for the whole comparator run under a cgroup (V3-S2R-A4), after one ordinary field lemma took nanoda to 52 GB (Lessons §4.5) |
| proof | ≤ 1 MiB (`proofCap`), every proof the runner verifies |
| chain length | ≤ `2^20` (`chainCap`) |
| verifier queries `qV` | ≤ `2^16` |
| per-query knowledge error `ε` | ≤ `2^-128` (`errorCap`) |
| completeness error `δ` | ≤ `2^-128` (`completenessCap`) |
| log length covered by the knowledge laws | `2^96` (`logCap`) |
| extractor steps | `B t = 2^48 + 2^16·t`; declared `fuel t ≤ B t` |
| extractor program, output | ≤ `2^20` statements (`progCap`); ≤ `2^24` words (`outCap`) |
| liveness (node run only below) | **proposed** `2^36` steps, `2^27` words of memory |
| native prover build + setup | ≤ 1 h, in the sandbox |
| tree run `tree_s`; root step `step_s`; one `Vb` run `verify_s` | ≤ 4 h; ≤ 600 s; ≤ 60 s (the root check also ≤ `T_V`) |
| memory of the tree run | ≤ 96 GB cgroup |

### 8.7 Incentive analysis (the final table)

| Channel | What closes it |
|---|---|
| Witness-sending argument (no proving, root verifier recomputes everything) | §8.5: listed, unranked, **only once the measuring rule is CPU time or a step count**; under wall time it is not closed |
| SNARK leaves, concatenation above (no recursion) | the root proof `2^r · |π_leaf|` exceeds `proofCap` for `|π_leaf| ≥ 4 KiB`; the root check verifies `2^r` proofs |
| Recursion only near the root, witness-sending below level `j` | **not priced by the theorem** (§6.6); the rule is the user's (§8.5) |
| A verifier that accepts a magic proof on any oracle | `KS` with the named extractor and `Computes`: a witness within the proved step bound would have to exist, and for a false digest none does within budget (`enum_no_computes`); the DoS column |
| A verifier that accepts a magic proof only when the oracle is BLAKE2s (O-25) | **not closed by the contract**; a rule plus review of `V` at intake is the only defence, and ADV-M5 shows review cannot separate the backdoor from honest code |
| A verifier that rejects everything, or whose `Vb` rejects everything | `V ≡ false` fails completeness; a `V` complete only above `proofCap` is certified and the harness's root check fails it |
| A verifier whose `KState` is trivial | `KState` alone excludes little; `Computes` with the budget is the knowledge clause |
| An extractor that brute-forces, uncharged | the program is data with no Lean continuation, three-address, one step per statement; `B t < 2^81` |
| A verifier that rejects honest proofs only under BLAKE2s | not closed by the certificate; the root, sample, smoke and liveness checks fail it |
| Completeness through a fallback branch (`V = SNARK ∨ witness-sending`, `P` the witness-sending prover) | liveness runs on the native prover's proofs with its emitted log (#9 item 1) |
| Precomputed proofs; cached runs | fresh starts per evaluation; `setup` sees no instance; a fresh directory per repetition |
| Reusing one child proof for both children | leaves are distinct with probability `1 − 2^-255` |
| A prover that writes invalid inner proofs | root check under the theorem; sample checks; canaries |
| A slow verifier under `T_V` | priced in the node's proving time; the cap only excludes linear work |
| Exploiting BLAKE2s where the relation hashes | four tags with distinct first bytes |
| Grinding / proof of work | allowed: `CompleteWithError` with `δ ≤ 2^-128`; costs prover time |
| Valid but lopsided ("caterpillar") proofs on a prover-chosen statement | **not covered**: 275 s at depth 6,000 for the honest entry, 212.6 s at depth 2,000 for the baseline (V3-S2a-M2, V3-S2b-m1); the benchmark's digests force the honest shape, and the DoS column draws random proofs |
| A tactic proof the Lean kernel checks in seconds but the second kernel cannot | a per-kernel budget (proposed) and a pre-submission check with the pinned kernels |
| Gaming column R with a special-cased root | R is measured on the T run's own level-7 outputs, in a fresh process |
| Compiled-code forgery on the badge path | the harness order, gate rules 3, 6–9, the source rule; residual O-12 (badge executables regenerated from kernel terms, required before board T opens) |

## 9. The baseline, the library's field, the harness order and the intake

### 9.1 The baseline (V3-9; stage S2a)

The witness-sending argument: `V c π` decodes `π` as a `Wit` and decides `Rel` directly, with
zero oracle queries (the node case runs `Vb` on the children recursively, so the root proof is
the list of all chain starts: `136 · 2^r − 88` bytes, 34,728 B at `r = 8`); `P c w` serialises
`w`; `E` deserialises; `ext` copies the proof's words from input to output in `8·t` steps. `KS`
holds with `μ := 0`, `ε := 0`, `qV := 0`; completeness is perfect for every `H`, hence
`CompleteWithError` at `δ = 0`. The library's verifier (`Library/WitnessSending.lean`) is strict,
so it rejects every proof that is not the canonical encoding, and it decodes in linear time per
level (V3-S2R-A5, #10). It is certified, passes the comparator, the gate and the badge path, proves
the smoke tree, and is **listed, unranked**: at the ranked size its root check took 20.9 s
(median of three) against `T_V = 2 s`. Unlike v2's baseline (S7-A2), its exclusion is a
measurement, not a theorem, and §8.5 says why that measurement is not yet a rule. It lives in the
submissions repository as `submissions/baseline/` (310 Lean code lines, 38 theorems; Lessons §3),
with the library's certificate as the core-side positive control. **Which contract it is certified
against:** the entry's `CertificateR` is against the pin `15e4ae5` (the S1 shape: `img`,
`Complete`, `Declared.img`), with the interim harness of `v3/s2-interim-harness`; the strict,
linear-time library verifier described above is the core's at `6202402`, which the entry predates
and imports no part of. Neither this entry nor `spartan-chain` was ported to the archived
contract (S2R RESULT Q11).

### 9.2 The library's field: CompPoly `BF64` and `Ext3` (V3-9, §7.4 of the 2026-10-19 design)

The contract has no field. Where organiser code needs one it uses CompPoly's
`CompPoly/Fields/Binary/BF64` at the pinned revision `572f997`: `BF64 = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`,
a computable 64-bit carrier with carry-less product and a two-fold reduction by `0x1B`,
Itoh–Tsujii inversion, a bridge into `AdjoinRoot basePoly` with a kernel-checked Rabin
irreducibility certificate, little-endian byte serialisation, and `Ext3 = BF64[y]/(y^3 + y + 1)`.
These are exactly leanVM's `K` and `E`. The gate's allowlist gains the 28-module closure
(`org-closure.sh`, interim commit `09668b5`), pinned by hash so that its one `@[csimp]` lemma is
reported, not rejected (V3-S2b-M2). **Compiled, CompPoly's field is unusable on the verifier
path**: `BF64` multiply 29.7 µs, `Ext3` multiply 415 µs, `BF64` inverse 1.72 ms (measured; `BitVec`
compiles to `Nat` bignums). The honest entry wrote a word-level `F`/`EF` proved equal to CompPoly's
by a kernel-checked ring isomorphism (87 ns and 535 ns per multiply; Rust 17.5 ns and 66 ns on the
same VM, Lessons §4.4), which is the first thing an organiser library should host.

### 9.3 What the organiser runs per submission (the harness order, A6-G0, unchanged from v2)

Source rule (no elaboration-time code, comments included; no `import Lean`); comparator in a
fresh sandboxed tree with **two kernels** (Lean's and nanoda `3a24072`, through leanprover's
comparator `d03acab` and lean4export `076e8e5`), replaying every proof against the challenge the
organiser rendered from the entry's `claim.json`; gate in a second fresh tree whose build is
bound byte for byte to the comparator-verified one (rule 3: no code-changing attributes in the
closure; rule 4: compiled code for the badge-path fields `V`, `P`, `ext`; rule 6: imports from the
exact allowlist, transitively; rules 8–9: no frontend on the badge path; the axiom audit over the
closure; the olean manifest against a reference organiser build); then the badge executables
`verify` (the compiled `Submission.Vb`) and `prove-lean` (the compiled `P` with the logging
oracle, used by the liveness check), and the benchmark run (§8.3). At the end of v3 the core
had the gate, the source rule, the axiom audit, the manifest tool, the sandbox shim, CI and the
kernel pins, but **no v3 stub, renderer, allowlist, reference manifest or runner**: those lived on
two interim scratch branches of the clone `rf-core-s2a`, `v3/s2-interim-harness` (`2a4588b` on
`15e4ae5`, for S2a: the stub, the renderer, `harness-local.sh`, `setup-scratch.sh`) and
`v3/ks-interim-harness` (`2464e97` … `4a1a1ed` on `05fde28`, for S2b: the same plus the CompPoly
closure and gate rule 4 over the v3 fields), written so that the two entries could reach
`HARNESS: ACCEPT`, and were stage S3's to adopt (V3-S2R-A4 lists the seven things S3 had to do).
Both series are archived as patches under `evidence/interim-harness/` on `v3/contract-archive`.

### 9.4 Intake: two repositories, pull requests and CI (V3-12, O-24, stage S7; not built)

The model is ots.golf's, with one change forced by wall-time scoring.

- **Two repositories.** The trusted core holds the contract, library, controls, harness tools,
  challenge stubs, documentation, and no entry. The submissions repository holds one flat root
  per entry, the registry `records.json`, the rulebook `AGENTS.md`, and a `.contract` submodule
  pinned to a core commit so that a submitter can run the harness locally. **The pin moves only
  with a contract change, in its own commit, before any entry is certified against the new
  commit, and never to a commit the core's remote does not have.** (This rule bit during v3: the
  honest entry was certified against `05fde28` while the pin stayed at `15e4ae5` until PR #11
  merged on 2026-10-22, so for three days the only honest entry was certified against a branch
  that was on the core's remote (pushed 2026-10-20 09:09, PR #11 open) but not on its `main`.)
- **Pull-request intake.** An entry is a pull request that creates or changes only its own root
  (never `records.json`, `.contract`, `docs/` or another root). The intake fetches the head,
  exports that root alone as flat regular files, lays it over a copy of the trusted core, and
  runs the harness in the sandbox. Pull requests are never merged: after a verdict the intake
  copies the verified root and its registry entry into `main` in its own commit; every head is
  retained under a creation-only tag; the verdict comment with the commit status is the durable
  record.
- **Where each part runs.** The proof half (source rule, comparator, gate, badge build) runs on
  any machine; the benchmark runs only on the reference machine, by a self-hosted runner or a
  verifier service the intake dispatches to, as the Proximity Prize's remote service does.
- **Contract pin and id.** A protected-file list (the contract, the lakefile and manifest, the
  toolchain file, the stubs, the harness scripts) with SHA-256 digests pinned in one file whose
  digest is the contract id; every verdict and record carries it; a change re-pins and ports or
  revalidates standing records with provenance.
- **Agent-facing rules.** `AGENTS.md`: the root layout, the claim file, the allowed imports, the
  limits, the attribution frozen at admission, an untrusted `NOTES.md` journal published whatever
  the verdict, and a "consequences that bite" list. Its §15 lists the known issues; it was
  corrected in seven places where it misstated the contract (#9 item 3, commit `5cb89d8`).

## 10. Trusted base: what a human must read

Measured by `scripts/loc.py` at `6202402` (Lessons §2):

| File | Code lines | What |
|---|---:|---|
| `Contract.lean` (reading order) | 8 | |
| `Contract/Hash/Blake2s.lean` | 68 | RFC 7693, unchanged since v2 S2 (12 kernel known-answer tests, an 8,432-case `hashlib` differential) |
| `Contract/Relation.lean` (§4) | 25 | |
| `Contract/Oracle.lean` (§5.1) | 22 | `OProg.bind` added (V3-S2R-A2) |
| `Contract/Security.lean` (§6.1, §6.4) | 33 | the potential (V3-KS); `failProb`, `CompleteWithError`, `completenessCap` |
| `Contract/Machine.lean` (§6.5) | 62 | the step-counting word language (V3-S2R-A1, A8); replaces the RISC-V machine (113) and the vendored Rv64 model |
| `Contract/Extractor.lean` (§6.5) | 35 | `Computes`, the budget, the caps |
| `Contract/Tree.lean` (§7.1) | 8 | |
| `Contract/Certificate.lean` (§5.2) | 31 | `ext`, `δ` |
| **total** | **292** | budget ≤ 500 |

No field, no compiler, no circuit class, no vendored machine. Every file has docstrings that say
what, not how. The contract imports Lean core and Mathlib only (`Basic.NNReal.Defs`,
`Data.Fintype.Pi`, `Algebra.BigOperators.Group.Finset.Defs`, `Logic.Function.Iterate`).

**The complete trust statement.**

> A ranked record means: the kernel accepted `CertificateR` for the rendered challenge, and the
> run, every checked proof verifying and the root check within `T_V`, measured the times. Its
> reader trusts:
> 1. Lean v4.34.1's kernel and nanoda, the comparator's export, and Lean core, Mathlib and the
>    packages as hashed in the olean manifest.
> 2. The contract: 9 files, 292 code lines, no theorem, three standard axioms. It includes the
>    extractor's step-counting machine, whose one-step-per-statement cost model is the meaning of
>    the extractor budget.
> 3. BLAKE2s = RFC 7693, its collision resistance (the statement tree), and the heuristic that it
>    instantiates the random oracle of the theorem, under the tags of §4.
> 4. Knowledge soundness and completeness (with error `δ`, over a random oracle) once per tree
>    level, with no composition theorem (§6.6); the paper bound of §6.3 from the potential form (a
>    stopped supermartingale and Markov); and, until O-25 is resolved, **that the submitted `V`
>    does not recognise the deployment oracle, which the contract cannot state in the ROM**. That
>    honest proofs verify under BLAKE2s is the harness's concrete checks, not a theorem.
> 5. The badge code: what Lean's compiler emitted for `Vb`, `P` and the contract interpreter on
>    `ext`, guarded by the source rule and gate rules 3, 6–9; residual O-12. This includes the
>    core functions whose compiled code is an `extern` with a Lean reference body:
>    `Task.spawn`/`Task.get` (kernel-transparent) and the `Array`/`ByteArray` primitives; the
>    badge `verify` may be multi-threaded (V3-S2R-A6, #9 item 5).
> 6. Harness tools: `Gate.lean`, the harness order with build binding, the manifest, the axiom
>    audit, the source rule, the renderer, the sandbox.
> 7. Tested, not proved: the runner (Python `treeRoot`, the prover interface, the caps, the
>    succinctness measurement, the liveness check). Liveness runs the contract's own
>    interpreter, compiled, so no emulator is trusted.
> 8. The reference machine and the season's `T_V` calibration (§8.5).
>
> Not trusted: `Library/`, `Controls/`, the entries, the native provers. Not claimed: §6.7.

Item 4's O-25 clause is the one a cryptographer cannot accept as written, and it is why v3
stopped: it says that board T relies on a human reading the submitter's `V` for a property that
ADV-M5 showed a reader cannot see (O-25 §2).

## 11. Libraries (untrusted, kernel-checked)

The untrusted library is where a submitter's work should have been saved; at the end of v3 it
held the witness-sending argument, the paper theorem and small lemmas, while the 10,500 reusable
lines of the honest entry stayed in that entry.

### 11.1 What the core's library had (`RecursionFast/Library/`, at `6202402`)

`Oracle` (`runLog_eq_run`: a log consistent with `H` containing the run's queries answers the run,
the step from `final` to the real run), `Security` (`BoolKState`, `KState.ofBool`, `KState.zero`,
`KState.mono`, `step_of_hits`, `final_unguarded`, `step_unstopped`, `fintype_card_digest`,
`acceptAll_kstate_iff`), `PaperTheorem` (`paper`), `Completeness` (`Complete`,
`complete_withError_zero`, `failProb_eq_prob`), `Machine` (`XStmt.Runs`, one lemma per statement,
`XProg.run_of_runs`, `run_lt_mem`), `Words` (the tape format lemmas and the linear twins
`packFast`, `bytesAtF`, `decodeWitF`, `witWordsF` with `_eq` theorems), `Tree`, `Blake2s`,
`WitnessSending` (the strict verifier, its certificate, the 21-statement extractor).

### 11.2 What the honest entry showed should be library (REPORT §4 item 2; CORE-HANDOFF §2.15)

About 10,500 of the entry's 16,766 lines are protocol-independent: the word-level `BF64`/`Ext3`
with its CompPoly isomorphism (1,031 lines; it is what makes `T_V` reachable at all); the BLAKE2s
R1CS gadget against the contract's hash (4,622 lines including the leanerVM copy, Apache-2.0
provenance); the Merkle and Fiat–Shamir-on-the-log lemmas (993); the generic potential with
`muG_step` and the round-split lemma `extCount_split`, so that a submitter supplies per-position
facts rather than a supermartingale (part of 2,250 lines of potential and log forest); the
AHIV22-style proximity lemma for interleaved Reed–Solomon codes (696 with the code); the
MLE/sumcheck counting lemmas (936); the linear codec twins. Trust cost: none; the allowlist gains
a Mathlib+CompPoly closure. This was stage S4 and was not started.

### 11.3 ArkLib and VCVio: the bridge target (V3-3, O-20)

ArkLib's security definitions at the pin `7653a90` are sorry-free; the contract restates locally
for audit surface and churn (§2). The bridge is one direction, contract → ArkLib: the potential
form implies the probabilistic straight-line knowledge soundness over VCVio's lazily sampled
random oracle, by the query-by-query bound VCVio proves as `prEvent_randomOracle_le_of_bad_queries`
(in VCVio from `d606eab`, one commit past the pin `a4232d0`; the bump is O-20). Not built. What
the honest entry found in practice (E2, Lessons §6): ArkLib is not on the allowlist; its AHIV22
proximity lemma pulls a 102-module, 24.7k-line closure through VCVio and PolyFun; its Spartan,
BCS/FS, FRI, Binius and ring-switching files carry `sorry` or are definitions only; VCVio's
Merkle extractor is a different formalism from the contract's `OProg`/`Log`. The entry re-proved
the proximity lemma with ArkLib as the guide (statement unchanged, a different induction).

### 11.4 The IOP route: BCS as a library theorem (V3-10, O-19)

Agents who design an IOP and compile it with Merkle trees and Fiat–Shamir need "round-by-round
knowledge soundness of the IOP implies `KS` of the compiled argument" for their compiler.
Upstream: VCVio at the pin has Merkle extractability in the ROM; ArkLib HEAD `db7005f` has
state-restoration knowledge soundness in its `Interaction` framework; the pull-request chain
#1267–#1283 (approved, unmerged at the time) adds Fiat–Shamir security, Merkle transfer and a
bridge to the legacy `OracleReduction` framework. The organiser's theorem for one fixed compiler
(v2's `Compile.lean` shape, moved to the library) is a gluing of those once merged, restated in
the potential form. Not started. Note for the next design: a v2-shaped "agent IOP, organiser
BCS" split does **not** close O-25 (O-25 §6, MG2): an IOP verifier that sees a challenge and a
later message can check a BLAKE2s computation of that challenge, which is IOP-sound and
BLAKE2s-unsound.

### 11.5 Candidate IOPs over GF(2^64)

ArkLib PR #383 (completeness and round-by-round knowledge soundness of Binary Basefold, ring
switching and FRI-Binius, being ported in #1298–#1302; knowledge soundness via unique-decoding
proximity, characteristic 2 plus an additive-NTT basis) is the natural reference IOP for an entry
over `BF64`; whether its basis conditions accept the pentanomial modulus is unchecked (O-22).
leanerVM (`532ebb4`) plans WHIR over binary Reed–Solomon with grinding of 17 bits per level, but
WHIR, its Merkle/BCS layer and the transcript are unwritten there (E1). Clean (`42fe4b26`) is an
optional circuit frontend never on the badge path, and at the pin it is not even required; it
imports `Lean`, which the source rule bans, so any Clean asset must be copied and re-proved
inside an entry (E4).

## 12. The amendments folded in, and the open items at the end

The ledger `DESIGN-AMENDMENTS.md` recorded every change the stages made to the 2026-10-19 design.
Its content is in §4–§9 above; this section is the index by id, so that a citation in a review,
an issue or a code comment on the archived branch can be resolved without the ledger.

### 12.1 V3-S1 (the contract and its fix pass, 2026-10-19)

A1 reading order; A2 `Machine.lean` gains `clmul` from the deleted `Field.lean`; A3 `blake2sDigest`
wraps `blake2s256`; **A4 `Digest := Vector UInt8 32`** (§4); A5 tags and `enc64`; A6 chain steps
not domain-separated (open), closed by **A19 `tagChain`**; A7 the tape and output formats, the
output denotes rather than equals; A8 the tree convention; A9 no `CompleteWithError` yet (O-23);
A10 `Declared`/`CertificateR`; A11 the `ImageComputes` domain, output cap, image cap; A12 the
budget `2^40 + 2^8·(p + l)` (superseded); **A13 the accept-everything control cannot be proved as
stated** (§6.2); A14 completeness over every chain length (open), closed by **A20 `chainCap`**;
A15 the witness-sending argument is a library module; A16 harness notes for S3; A17, A25, A27
the v2 tree parked and then removed (tag `v2-archive`); A18 completeness is about `V`, `Rel`
about `Vb`; **A21 the budget is over the tape, `fuel : ℕ → ℕ`** (review M3); A22 `decodeWit` caps
child lengths (review m5); **A23 what the certificate does not exclude: `Controls/Backdoor.lean`**
(review M1); A24 `queries` takes the oracle first; A26 trusted headers rewritten.

### 12.2 V3-KS (the potential and the guard; PR #11; 2026-10-19/20)

**A1 the potential form** (§6.1); **A2 the log-length guard** and what it gives up; A3 the
library (`BoolKState`, `ofBool`, `zero`, `mono`, `step_of_hits`); A4 the controls
(`twoLucky`, `Vcol`); A5 documents outside the core; **A6 `logCap = 2^96`** (review M1; the
`V24` control is this entry's);
A7 the literal `2^256`, the paper theorem moved into the library (`Probe.paper`, review m2/m3);
**A8 the instance is `noncomputable`** (commit `05fde28`).

### 12.3 V3-S2R (the rules; 2026-10-20)

**A1 the extractor program** and its machine (§6.5), replacing the RISC-V image and the vendored
Rv64 (O-16 moot); **A2 completeness with error** (§6.4); A3 the rendered claim without the image
literal, gate rule 4 over `V`, `P`, `ext`; A4 what S3 must do (the stub, the CompPoly closure
pinned, a reference manifest, Controls out of the allowlist, liveness on the native prover's log,
a fresh directory per repetition, the kernel cap with a fixture); A5 the library's strict,
linear-time verifier (#10); **A6 design text that was false** (`Digest`; the efficient-extraction
domain; "a prover cannot flatten the tree"; the `T_V` numbers; "pays in `T_tree`"; core `extern`s;
accumulation); **A7 the proposed measuring rules awaiting a value** (§8.5); **A8 affine memory**
(review M1); **A9 queries under `2^64` bytes** (review M2).

### 12.4 The open items (O-n) at the end of v3

| Id | Item | State |
|---|---|---|
| O-6 | reference machine SKU, noise calibration, field policy, 96 GB cap | never procured; every `T_V` number is from the development VM |
| O-7 | fund a reference entry over `BF64` | overtaken: the honest entry exists (S2b) |
| O-8 | report rewrite for v3 | this document set |
| O-9 | compiled Lean field arithmetic is slow | measured (§9.2); the honest entry's word-level field is the fix, not upstreamed |
| O-12 | badge executables regenerated from kernel terms | open; required before board T opens |
| O-14 | hash menu for the oracle | open; now also a way to fit recursion (#8) |
| O-15 | organiser assets: a BLAKE2s gadget kit, a decoder program in the step language, the BCS theorem | the gadget exists in the entry (copied from leanerVM); no decoder was written |
| O-16 | ZiskAccel dead arms in the vendored machine | moot (the machine left the contract) |
| O-18 | succinctness cap as a deterministic step count | open; needs `V` as a deep program (§8.5) |
| O-19 | the BCS library theorem | not started; upstream chain unmerged |
| O-20 | VCVio bump for the ROM union-bound lemma | not done |
| O-21 | error caps and budgets: `errorCap` `2^-128` or `2^-160`; `B t`; `logCap` `2^96` or `2^58` | all three undecided |
| O-22 | Binary Basefold over `BF64`'s pentanomial basis | unchecked |
| O-23 | counted-error completeness | **resolved** (V3-S2R-A2) |
| O-24 | intake | not built (S7) |
| O-25 | uninstantiability | **the wall** (§15.1; O-25 document) |

Resolved by v3 before these: O-1, O-3, O-10, O-11 (the extractor budget is no longer a function
of a size class), O-13 (rule 4 has no `Fin`-family field), O-17 (no `IDX`), the v2 fixed-point
part of O-14 (no `fits`).

### 12.5 Small items of the design, the ledger and the issues, kept so that they are not rediscovered

- **A binary-field track** (2026-10-19 design §7.5): a policy board restricted to binary fields
  by a free-text `declared_field` and a hand review of the entry's sources; the trusted base
  unchanged. Relevant to C11: it is a review-based board.
- **Carried over from v2, never re-targeted** (#1; 2026-10-19 design §9.3, §10): the Clean
  bridge (`RecursionFastClean`, `toLayout_rel_iff`, both directions) and the characteristic-2
  balance note (O-5), v2's `Bridge/ArkLib.lean` stated against the pin's API without the ROM
  instance, and `L_chain(n)` with `check-chain.py` as library examples; all at
  `v2-archive:legacy/v2/` and `v2-archive:harness/`. O-20's "Clean patches re-verified" is moot
  (Clean left the pins).
- **Incentive rows not repeated in §8.7**: level-aware verifiers are allowed (the proof may carry
  hints, the digest does not); the field is free and priced by the machine; parallelism, memory,
  timing noise, Sybil and records are v2's §6.4 unchanged.
- **Records** (2026-10-19 design §7.7; a #1 intake item): `records.json` per board holds the
  standing entry with its contract id, hardware id, `entry_id` and the verdict's commit; the
  paired record rule applies; a later identical or copied entry never takes a record.
- **V3-S1-m11** (optional, argued not done): restricting `final` to `π.size ≤ proofCap` is a
  statement change, not a restatement.
- **V3-S2-KS-m4**: CompPoly `Data/Bytes/Bias`, VCVio `SampleableType/Basic` and ArkLib
  `OracleReduction/Prelude` each declare a `Fintype (Vector UInt8 n)` instance; admitting one is
  sound (a subsingleton) but rewriting with its card lemma against a contract goal can unfold the
  instance; entries use `fintype_card_digest`. A note for any future allowlist.
- **#5's rejected alternative** for the multi-answer problem: an extendable-output oracle
  constructor `queryN (q) (ℓ) (k : (Fin ℓ → Digest) → OProg α)` (ADV-M3), rejected because it
  changes `OProg`, the tape, `Vb` and the native prover and still needs `logCap`; and the unbuilt
  control `merkleToy` (F1 §1.2's dangling-root attack log), replaced by its collision half `Vcol`.

## 13. Issues incorporated

Eight issues were open on `scaraven/recursion.fast` when v3 stopped. #1 is the roadmap; #4 is
the O-25 tracking issue opened from the Stage S1 review; #5–#10 and the comment on #4 were filed
on 2026-10-19 by the orchestrating agent from the honest-baseline work in the submissions
repository (sources: `notes/F1-ks-feasibility.md`, `notes/ADV1-rules-review.md`, the S2a entry;
PLAN D-6). This section is their closure: for each, the finding, what was decided and
done (with the commit on `v3/contract-archive` or `main`), and what remains open and where it
went. Commits: `15e4ae5` main before PR #11; `ecdcbd5`/`c3f6380`/`05fde28` the KS amendment,
merged as `059812f`; `4b3356a` V3-S2R; `ef7349a` its review; `6202402` its fix pass and golf.

### 13.1 Issue #1: the roadmap (v3 stages, open items, intake)

**Content.** The checklist of the design's build order (S1 contract, S2 baseline, S3 harness, S4
library, S5 docs, S6 BCS theorem and reference entry, S7 intake), the open items O-6 … O-25 with
owners, the items carried over from v2, the intake items, and the pins (Lean v4.34.1, Mathlib
v4.34.1, ArkLib `7653a90`, CompPoly `572f997`, VCVio `a4232d0`, PolyFun `41d3b21`, the vendored
riscv-zkvm `Rv64` at `6810fc1`, comparator `d03acab`, nanoda `3a24072`).

**What was done.** S1 on `main` (PR #2, `069b1a6`; the v2 tree removed in PR #3, `15e4ae5`). S2
built in the submissions repository as two entries (S2a `submissions/baseline/`, S2b
`submissions/spartan-chain/`), both `HARNESS: ACCEPT`. The KS amendment (not on the roadmap) as
PR #11. A rules stage S2R (not on the roadmap) at `4b3356a` … `6202402`. S3, S4, S5, S6, S7 not
started; S5 is this document set. The vendored Rv64 and Clean left the pins (V3-S2R-A1; Clean was
never required at the pin). The issue body was stale from 2026-10-19 on (it still showed S1 "in
review"), because editing it is a GitHub write the agents were not permitted (CORE-HANDOFF §2.16).

**What remains open, and where it went.** The whole roadmap is superseded by the decision of
2026-10-22 to return to ideation. The open items are tabulated in §12.4; the constraints they
leave are §16.

### 13.2 Issue #4: O-25, ROM uninstantiability (a certified `V` may recognise the deployment oracle)

**Finding (V3-S1-M1).** `Controls/Backdoor.lean` is certified by the kernel and its deployed
verifier accepts a 32-byte magic proof of every statement: `V` asks the oracle the empty query,
computes `blake2sOracle ""` itself, and on a match accepts `magic c := c.toArray`; among all
oracle functions the match is one answer in `2^256`, so `KS` holds at `errorCap` with one query;
the honest branch is untouched, so completeness holds. Every harness check of §8.3 passes with no
proving at all. No salt helps, a keyed oracle is impossible (the recursion evaluates the oracle),
v2 had the same exposure. The issue proposed a candidate fix: `V` polymorphic in the digest type
with `DecidableEq` only, digest slots injected by the contract, structured queries, the gate
checking the type.

**The comment (ADV-M5, 2026-10-19).** Five additions, one kernel-checked: (1) a literal 32-byte
trigger computed offline has a constant closure with no `blake2sOracle`, `tagRO` or `Vb`, and a
BLAKE2s footprint identical to the honest witness-sending verifier's, so the review's proposed
closure test cannot separate them (`evidence/probes/LiteralTrigger.lean`, `backdoor_lit`,
**kernel**); (2) a "trace-check" trigger evaluates no hash at all (**paper**); (3) the rule "`V`'s local computation must not
evaluate the oracle's instantiation" also bans concatenation nodes, hard-coded verification keys
and consistency fast paths; (4) the parametric-digest fix cannot support Fiat–Shamir: any answer
bits `V` can read, `V` can compare with a local BLAKE2s, and every succinct hash-based `V` needs
challenge answers; (5) `AGENTS.md` does not state the rule.

**What was decided and done.** The user decided on 2026-10-20 that O-25 **must** be closed. A
design track ran two rounds: Candidate E (the parametric type plus a restricted challenge
interface) was broken by six kernel-probed findings (O25-M1 … M6: `idx` is a full byte
projection; `CommRing F` with `DecidableEq F` names every element of the one deployed field;
the honest verifier needs `ofBytes`; grinding exposes a value; a degree cap separates nothing;
the liveness smoke covers only exercised behaviours); the orchestrator's **post-hoc challenge
verification** attack then showed that any framework in which submission-written checks see a
challenge as a value is open; Candidate T (a contract-owned verifier template over first-order,
seed-bound data, with the invariant INV′ and the admissibility rules A1–A4) survived its review
as the only construction that removes the mechanism from submission-authored code, at the price
of reversing V3-1, V3-2 and the Q6 motivation, with the ranked board empty until the organiser
builds the entire honest recursive SNARK (O25T-M3, M4) and a template review that re-imports
the per-entry review problem at the template level (O25T-M5). The review offered a middle ground,
MG1 (an admissible menu of formats, compilers, PCSs and fields). **On 2026-10-22 the user
rejected MG1** ("this severely restricts the design space for autoresearch agents, while still
adding a huge gap for reviewing proposals, and requiring manual intervention"); the user said
nothing about T or about review-only ranking; the authors read the objection as covering T, which
is narrower (§14). Nothing was implemented; the contract at `6202402` still certifies
`Controls/Backdoor.lean`, by design, as the known-gap control (V3-S1-A23). In parallel, the
relativized-NARK exploration (`explore/relativized-nark`, `043bcb3`; O-25 §13) proposed closing
O-25 by the deployment (a relativized node clause plus an attested secret oracle, D4), with its
own adversarial review; it was not put to the user.

**What remains open, and where it went.** O-25 is the first wall (§15.1). The full record,
including the "fields as data" variant suggested after round 2 (unreviewed), the relativized
exploration (§13 there), the literature, the precise impossibility statement and the criteria a
solution must meet, is the O-25 document.

### 13.3 Issue #5: `KS` at `errorCap` is unsatisfiable for every Merkle/BCS verifier

**Finding (F1-1, F1-2; ADV-M2, ADV-M3; kernel-checked).** S1's `KState.Bounded` demanded at most
`ε·2^256` bad answers for every log of any length and every fresh query. (a) Over logs longer
than `2^128` the collision and late-preimage sets of a Merkle binding argument exceed the cap
(`collision_not_capped`). (b) The boolean form charges a `k`-answer query phase its worst
conditional per answer: a 16-query verifier with ROM error `2^-128` has no bounded state below
`2^-8` (`product16_not_capped`), and spreading never helps (`eps_ge_density`). Every escape
(semantic or length-dependent `good`, 512-bit roots, extra local checks, larger `qV`, a tighter
cap) was examined and fails (F1 §1.3, §2.2). Under the pin the only certifiable entries were the
witness-sending argument and the O-25 backdoor.

**What was decided and done.** The potential form with the guard (§6.1), decided as D-2 on
2026-10-19, built on `v3/ks-potential` (`ecdcbd5`), reviewed (V3-S2-KS: sound; M1 `logCap = 2^64`
certifies a 96-bit verifier at the 128-bit cap, fixed to `2^96` in `c3f6380`), the
`noncomputable` fix (`05fde28`, the #5 comment item 4), merged as PR #11 (`059812f`, 2026-10-22).
The honest entry's certificate rests on it: its potential pays `(2^96·(3·2^8+1)+1)/2^256` per
fresh query for collisions, label hits and state hits plus `(4/5)·2^-129` for the Ligero query
phase, and `eps_le` closes the sum under `2^-129` (kernel). Trust cost: 3 contract lines.

**What remains open.** `logCap` `2^96` or `2^58` (O-21; §6.3); a kernel control that the guard is
needed for a *potential*, not only a boolean state (`V31`, V3-S2-KS-m1; a paper argument stands
in); the `AGENTS.md` note on the `Fintype Digest` elaboration snag; the submissions pin move to
`059812f` and the re-certification of S2a against it (never done; the pin stayed at `15e4ae5`).
For a next design: the finding is general (§16, C3): any per-query counting definition without a
log-length bound and without a way to carry a partial product across answers excludes every
hash-based SNARK.

### 13.4 Issue #6: `T_V = 2 s` does not exclude witness-sending; board T rewards avoiding recursion

**Finding (ADV-M1, ADV-M4; measured).** §8.5's table: the certified trivial check takes 20.7–21.2 s
sequentially but 37–43 ms with an unrolled BLAKE2s and `Task.spawn`, kernel-transparent; a
certified entry that proves nothing wins board T. And witness-sending below level `j` saves node
proofs: the level-`j` nodes do the chain work an honest leaf would, and `2^{8−j} − 1` node proofs
replace 255; a level-7 witness-sending proof verifies in `2^21` compressions, within `verify_s`.

**What was decided and done.** The false design text was withdrawn (V3-S2R-A6: "22–29 s … margin
10×", "a prover cannot flatten the tree", "pays in `T_tree`") and the measured numbers put in its
place (`4b3356a`). A rule was proposed (V3-S2R-A7): CPU time on one pinned core, calibrated
against an interleaved organiser checker, `T_V ≤ T_triv,best/10`; and for (b) the cap at every
level or column R ranked. The trust statement names the core `extern`s (`Task.spawn`, the array
primitives).

**What remains open.** The value and the choice, which need the reference machine (O-6) and the
benchmark shape; the deterministic alternative O-18. For a next design: §16, C6 and C7.

### 13.5 Issue #7: node extraction is decoding, and the budget was sized for the proof

**Finding (F1-3, ADV-M7; paper).** `Rel`'s node clause demands `Vb c₁ π₁ = true` under concrete
BLAKE2s while the log holds random-oracle answers, so a log lookup is unprovable (the SNARK
attests that *some* preimage of a hash is accepted; the log's preimage is unrelated). The only
provable route is circuit correctness, so a node extractor must find the committed codeword in
the log and decode it: about `2^29` symbols at node size, about `2^43` RV64 steps quasi-linear,
against `B t = 2^40 + 2^8·t`, and it had to be RV64 assembly proved against the vendored machine
with single-step tooling. Leaves are fine: the witness goes in the clear and the 8-instruction
parsing image extracts it, which is what the honest entry does.

**What was decided and done.** The user's decision of 2026-10-20: the extractor is a computable
Lean function with a **proved** cost bound; measured-only bounds are rejected (a brute-force
fallback reachable only on accepted-but-undecodable proofs is never exercised by honest proofs,
so fuzzing never finds it, and knowledge collapses to soundness). Implemented as the deep
step-counting language with `Computes` and `B t = 2^48 + 2^16·t` (V3-S2R-A1, A8, A9; `4b3356a`,
`6202402`), the RISC-V machine and the vendored model removed from the trusted base.

**What remains open.** The budget's fixed term is a paper estimate (no decoder was written in the
language, F-D1); the budget value, the liveness caps and the reinterpretation of the decision as
a deep program (S2R RESULT Q2, Q4, Q13, Q15) are unconfirmed; the `Computes` domain change A9
(queries under `2^64` bytes) is an unrequested contract change argued on paper and awaiting the
user's confirmation or the alternative of a `2^61`-word tape (Q14); the interpreter's per-step
cost was never measured and `Word := UInt64` is a mechanical port if liveness needs it (Q7); the
primitive set (`clmul`, `clmulh`, `mulhu` in; no BLAKE2s compression) is unconfirmed (Q8); and
whether to keep the deleted RISC-V machine (git has it at `05fde28`) for O-18 is undecided (Q12).
For a next design: §16, C4.

### 13.6 Issue #8: honest recursion under the caps

**Finding (F1-4; ADV-M6, ADV-M8; paper, except the circuit size).** (1) With `proofCap = 1 MiB`,
BLAKE2s-only hashing, R1CS and the unique-decoding regime (V3-5 admits no proximity-gap
conjecture, so at most one bit per query and at least 128 positions), each Merkle level in the
node circuit is a BLAKE2s gadget of about `2^14` constraints (measured: leanerVM's circuit,
14,720 gates + 256 output rows per compression), the node circuit about `2^28.3` constraints, and
proof sizes at that size are WHIR-class 621–770 KiB ("yes, barely"), FRI about 1 MiB (no),
Basefold 7.95 MiB (no), Ligero/Brakedown `≥ 25 MiB` (no); the honest entry's measured Ligero leaf
at `n = 2^14`, 1,464,107 B, confirms the last row. With a plonkish/AIR BLAKE2s (`2^10`–`2^11` cells)
the node circuit is about `2^24` and every row but Ligero fits. (2) Perfect completeness over
every `H` forbids grinding, rejection sampling and challenge-dependent exceptional cases. (3)
Preprocessing SNARKs (Spartan with SPARK, Plonkish, Marlin) cannot satisfy completeness over every
`H` within `qV ≤ 2^16`: a hash-derived verification key has no opening under a random `H`, and
recomputing it inside `V` costs about `2^20` queries. (4) Hash-based accumulation is not
expressible (§7.2).

**What was decided and done.** (2) resolved by `CompleteWithError` (V3-S2R-A2). (4) the design's
claim corrected (V3-S2R-A6). (1) and (3) deferred to the user: (1) one of (i) document that
recursion closes only with WHIR-class sizes, (ii) raise `proofCap` for node proofs, (iii) an
arithmetisation-friendly hash in a menu (O-14), (iv) a named proximity-gap hypothesis (not under
V3-5); (3) an indexer in the submission (`I : OProg Key`, `V : Key → Digest → Proof → OProg Bool`,
`KS` counting `I`'s queries honestly, `Vb` using `I.run blake2sOracle` once at badge build), a
handful of trusted lines that would also remove the one legitimate reason for `V` to compare an
oracle answer with a hard-coded constant; it waited on O-25 fixing `V`'s type. The honest entry
avoided SPARK by a uniform repeated-block circuit whose matrix MLEs `V` evaluates in a closed
form (`chainMats_eq`, kernel).

**What remains open.** All four decisions. For a next design: §16, C5, C8; §17.

### 13.7 Issue #9: minor rules and hygiene (ten items)

| Item | Finding | Done | Open |
|---|---|---|---|
| 1 | completeness through a fallback branch is vacuous; liveness tests only the fallback (ADV-m1) | liveness on the native prover's proofs with its emitted log, specified (§8.3 step 8) | S3 |
| 2 | repeated runs reuse instances; a prover can cache (ADV-m3) | a fresh directory per repetition, specified | S3 |
| 3 | `AGENTS.md` misstated the contract in seven places (ADV-m4) | fixed in the submissions repository (`5cb89d8`, §15 "Known issues"); §2.1 `Digest` fixed in the design | — |
| 4 | gate rule 4 listed v2's fields `[P, cfg]` (ADV-m5) | `badgeFields = [V, P, ext]` with fixtures (V3-S2R-A3; interim `4a1a1ed`) | — |
| 5 | the trust statement should name core `extern`s (ADV-m6) | §10 item 5 | — |
| 6 | the paper theorem's domain is `min(logCap, ≈2^61)` (ADV-m7) | §6.3 | the `logCap` value |
| 7 | no `Fintype Digest` at the pin | supplied by PR #11 | — |
| 8 | ArkLib is not allowlisted; the policy (re-prove, copy, extend) is unstated | — | the user's (REPORT §4 item 7; CORE-HANDOFF §2.11 item 8); the honest entry re-proved |
| 9 | compiled field speed decides `T_V` (O-9) | measured; the word-level field exists in the entry | upstreaming (S4) |
| 10 | perfect completeness and the counted form (ADV-m2, V3-S1-m10) | superseded by `CompleteWithError` | — |

A further item that belonged here and was never filed (D-11, CORE-HANDOFF §2.7): **the second
kernel's budget is unstated**, and one ordinary field lemma (`SpartanChain.F.spread_getLsbD`,
a 64-way `interval_cases j <;> simp`) took nanoda to 52 GB and `HARNESS: REJECT` while the Lean
kernel checked it in seconds; rewritten structurally it checks in 0.76 s / 33 MB and the whole
entry in 70 s / 2.41 GB (Lessons §4.5). The proposed cap (16 GB / 30 min) and the pre-submission
check are open; for a next design, §16, C10.

### 13.8 Issue #10: the library verifier accepts malleated leaf proofs; the contract's codec is quadratic

**Finding (S2a; kernel-checked and measured).** `Library/WitnessSending.check` required
canonicity only in the node branch, so a leaf proof with one byte appended or its last byte
removed decoded to the same leaf and was accepted (`lib_leaf_appended`, `lib_leaf_truncated`):
the organiser's reference argument failed two canaries of §8.3 step 7. And the contract's
`packBytes`/`bytesAt` compile to quadratic code: 563.26 s to reject a random 1 MiB proof against
`verify_s = 60 s`.

**What was decided and done.** A strict leaf branch, the linear twins `packFast`, `bytesAtF`,
`decodeWitF`, `decodeF`, `encodeF` with `_eq` theorems, four canary controls and the header remark
that the contract's functions are specifications (V3-S2R-A5, `4b3356a`). With the linear twins,
random 1 MiB proofs are rejected in at most 0.28 s and adversarially shaped ones in at most
1.25 s (the S2a entry's final run, `logs/V3-S2/fix/check/smoke.log`; the issue quoted an earlier
run at 0.25 s and 1.19 s). The certificate was never affected.

**What remains open.** The per-level structure of the recursive node check (each level re-parses
its subtree) makes valid lopsided proofs on prover-chosen statements cost minutes (§8.7); an
offset-recursive node check without re-encoding was sketched and not done (S2R "not in this
stage", §2.12). For a next design: §16, C9.

## 14. The user's decisions

These are the fixed points a next design inherits unless the user reopens them. Q1–Q4, Q2
revisited and Q6 are from `DISCUSSION.md` (2026-10-13 to 19; there is no Q5); the rest are from
the sessions of 2026-10-20 and 22, as logged in the orchestrator's job timeline. Where a row
contains the authors' inference rather than the user's words, it says so.

| Id | Date | Decision |
|---|---|---|
| **Q1** | 2026-10-13 | The extractor is the program: mandatory for ranked records, a RISC-V image with a proved cycle bound B(k) = 2^(2k+16); an unbounded Lean extractor ("L1") is an allowed intermediate, listed and unranked. Consequence noted at the time: extraction is decoding, so entries are confined to the Johnson or unique-decoding radius, and conjecture-based parameter sets are out; CompPoly's verified Guruswami–Sudan decoder makes the Johnson regime reachable in principle. **Superseded in form** by the decision of 2026-10-20 (a Lean program of the contract's machine); the substance, a proved bound, stands. Whether the design should say so is S2R RESULT Q9. |
| **Q2** | 2026-10-13, revisited | The four-profile zkVM cost model is too complicated; a simpler model that steers towards hash chains and 2→1 recursion was proposed ("flat instructions plus one hash price"); **parked**, and resolved in v2 by measured wall time on one reference machine, which v3 keeps (V3-8). |
| **Q3** | 2026-10-13 | Score all runs on both boards, not only accepting ones: `run` must return counters with the verdict and fuel exhaustion is distinguished from rejection. (Moot once the verifier is timed rather than counted, but it is why the DoS column exists.) |
| **Q4** | 2026-10-13 | Keep the universal R1CS relation (option A); semantic relations (B′) rejected because they would put large relation and security definitions in the trusted base; the statement must be a few digests, not `nx = 2^10` elements. (The authors' observation, not a recorded rationale: v3's 25-line digest relation is a semantic relation small enough not to raise Q4's objection.) |
| **Q6** | 2026-10-15 → 19 | v3, decisions V3-1 … V3-11: the submitted object is the argument itself, no organiser compiler; one relation over digests; field-agnostic; knowledge soundness in a local counting form with Mathlib only, ArkLib the bridge target; completeness proved for the Lean `P`; the native prover measured only; the extractor as a RISC-V image with a budget (Q1 stands); whole-tree wall time at depth 8 and chain length `2^14`; ROM-only; BLAKE2s-only with a declared menu. The gripes it answered: v2 "forces every agent through one configuration of the BCS transform", cannot express accumulation, and makes a fixed field a contract rule. The two-repository model is V3-12, a separate decision of the same date. |
| 2026-10-19 (a)–(d) | S1 fix pass, **the orchestrator's decisions** (the ledger: "the orchestrator's decisions, 2026-10-19"), not the user's | (a) the accept-everything control is reworded, no definition change; (b) `chainCap`; (c) the chain is tagged; (d) the extractor budget is over the tape. Then: Backdoor.lean kept as a documented gap; O-25 opened as a user decision. |
| 2026-10-20 | the rules | **(a)** The user's first proposal (09:12): "replace the extractor as a computable Lean 4 function, we then execute the extractor on generated traces/proofs and so on, and if it runs within a reasonable amount of time (this needs to be benchmarked)". After discussion, the user chose (15:19) "the extractor as a lean 4 function and a proved cost bound". The rationale for rejecting a measured-only bound (a brute-force fallback reachable only on accepted-but-undecodable proofs is never found by fuzzing) is the orchestrator's, which the user accepted. The first preference matters for an ideation round that wants a wider design space. **(b)** Completeness may have a small error over a uniformly random oracle; the user recommended `2^-128`, with `2^-96` as the alternative (`89·2^g` against `67·2^g` grinding attempts at difficulty `2^g`); `2^-128` was implemented. **(c)** O-25 **must** be closed, on its own track, with the ideas explored by one agent and adversarially reviewed by another. Also recorded: proof size matters, Ligero is √-size, an R1′ with WHIR/Ligerito-style folding in the unique-decoding regime using BCHKS25's half-distance mutual correlated agreement in place of AHIV22's `d/3` is the route under `proofCap`; the Johnson regime comes later; grinding needs the counted completeness (CORE-HANDOFF §2.14). |
| 2026-10-22 | PR #11 merged | `059812f`: the potential-form knowledge soundness is on `main`. |
| 2026-10-22 | MG1 rejected | The user's words (09:38): "I'm not happy with MG1, this severely restricts the design space for autoresearch agents, while still adding a huge gap for reviewing proposals, and requiring manual intervention." **The authors' inference:** T, being strictly narrower, falls under the same objection; review-only ranking does not close O-25, which the user required on 2026-10-20. The user was not asked about T, review-only ranking, or the relativized exploration (§17.1, D-L). |
| 2026-10-22 | back to ideation | v3 hit a wall; the contract is archived on a branch; `main` is stripped to a skeleton; the issues are incorporated here and closed. |

Decisions the stages asked for and never received, each listed where it is used: the `T_V`
measuring rule and value and the recursion incentive (§8.5; S2R Q5); the liveness caps (§8.3
step 8; Q4); `logCap`, `errorCap` and the budget value (O-21; Q2, Q3); the kernel budget (§8.6;
Q6); the `proofCap` / hash menu / proximity-hypothesis choice and the indexer (§13.6); the ArkLib
policy (§13.7); the acceptance run and the caterpillar DoS of the honest entry (REPORT §6 Q5,
Q10); whether to adopt the organiser library as stage S4 and the interim harness pieces in S3
(REPORT §6 Q8); whether the design should say Q1 is superseded (S2R Q9); the reinterpretation of
decision (a) as a deep program (Q13). From the S2R RESULT, also unanswered: **Q1** confirm
`completenessCap = 2^-128` (recommended) over `2^-96`; **Q7** the compiled interpreter's per-step
cost was never measured, and `Word := UInt64` is a mechanical port if liveness needs it; **Q8**
the primitive set (`clmul`, `clmulh`, `mulhu` in; no BLAKE2s compression in the language); **Q10**
the GitHub writes the stage could not make (the PR #11 description, the #5 status, filing D-11 on
#9, the roadmap); **Q11** both entries must be ported before any pin move, and neither was: S2a is
certified at `15e4ae5` and `spartan-chain` at `05fde28`, both with the interim harness and the
S1/KS shape; **Q12** keep the RISC-V machine deleted (git has it at `05fde28`) or keep it for
O-18; **Q14** the `Computes` domain change A9 is an unrequested contract change argued on paper,
awaiting confirmation (§6.5).

## 15. Open problems: the walls

Each wall is stated as what is known, with its evidence, and what would have to be true of a
design that does not hit it.

### 15.1 O-25: a ROM certificate cannot see the deployment oracle, and no submission-authored verifier examined could be made safe

**Known (kernel).** `Controls/Backdoor.lean`: a certified submission whose deployed verifier
accepts a 32-byte proof of every statement. `backdoor_lit`: the trigger as an offline literal,
with no syntactic trace. `idxOf_full`, `idxOf_all_bits` (O25-M1): a width-chosen index map is a
full byte projection, so the mechanism survives inside a parametric type as soon as `V` can read
any value of an answer. `pubTau_eq_challenge`, `evil_Vb`, `postHoc_iff` (O25T-M1, M2): even under
a contract-owned template, submission data interpreted by code that applies it to a challenge,
or a submission function that reads pre-seed data, computes or branches on transcript values.
(All archived under `evidence/probes/` on `v3/contract-archive`.)

**Known (elaborated definitions and paper).** `cmpNat`, `encodeF`/`cmpF` and `pinned` (O25-M2)
are type-checked definitions at the parametric type, `pinned` exercised by an `#eval` on
`ZMod 7`, not theorems; the claim that one prover value names every element of the one deployed
field rests on a paper density bound. The Fiat–Shamir obstruction to the parametric `D` (ADV-M5.4),
O25-M3 to M6, and the salting argument (V3-S1-M1) are paper.

**Known (argument).** The post-hoc challenge verification attack: after a challenge `c₁` the
prover sends BLAKE2s wires over the earlier prefix, low-degree checks verify the wires, then
check `c₁ = Σ outbitᵢ·βⁱ`; there is no fixed point because the data comes after `c₁`. So any
framework in which a submission-written check sees a challenge as a value, next to later prover
data, can recognise the deployment (O-25 §5). Among the candidates examined, the only invariant
that closed it (INV′: every check with an oracle-derived operand is organiser code, and every
submission value reaching such a check is bound into the seed before the first answer) makes the
verifier the organiser's; no weaker invariant was found, and none is excluded by a theorem (O-25
§10.3 Q2 names an unexamined restricted composition language).

**Known (a different route, on record).** The relativized exploration (O-25 §13; D-L in §17.1)
changes the node clause so that children are judged on the game's log, which removes the premise
that the recursion circuit evaluates the oracle; the oracle can then be a secret harness service,
and O-25 closes **by the deployment** modulo PRF security (paper), with the relation alone leaving
the backdoor certified (kernel). Its costs are a trusted service, records checkable only by the
organiser until key release, and #6 (b), #7 and #8 unchanged. It keeps a submitter-written `V`
with no per-entry review and no menu; whether it meets the user's objection was not asked.

**Known (literature).** No ROM theorem can remove the residual even then: CGH98, GK03, BBHMR19
(the Kilian/Micali template this competition *is*), KRS25 (a deployed GKR argument), Fenzi26
(Spartan/Aurora variants) construct arguments that are ROM-sound and unsound under every concrete
hash; BDGJKLW13/DJKL13 show no black-box reduction to a falsifiable assumption can prove FS sound
for such protocols; BHK26 attacks the extended-FS escape (XFS). Correlation intractability is the
only positive route and needs an LWE-type hash, not BLAKE2s.

**Rejected or set aside.** The parametric `V` (broken); rule plus review (ADV-M5: review cannot
separate the backdoor from honest code; the honest entry's own node branch evaluates
`blake2sOracle` and would be flagged by any syntactic rule); the menu MG1 (the user, 2026-10-22),
and with it, by the authors' reading, the template T. What a solution must satisfy instead is
O-25 §11: no narrowing of the design space, no large human review surface, no manual
intervention; and it must be stated precisely what it guarantees against which adversary, since
"ROM-secure ⇒ BLAKE2s-secure" is false for the class.

### 15.2 Honest recursion is unproven at the caps, and every way to make room changes the trusted base

**Known (paper, one measurement).** By paper estimate (#8), under `proofCap = 1 MiB`, BLAKE2s-only
hashing, an R1CS BLAKE2s gadget of `2^14` constraints per compression (measured) and the
unique-decoding regime, the node circuit is about `2^28.3` constraints and only a WHIR-class PCS
fits `proofCap` at node size, and only just ("yes, barely", 621–770 KiB). No such PCS has a Lean
knowledge-soundness proof. Node extraction needs a `2^29`-symbol decoder that was not written
(#7). Preprocessing and accumulation are inexpressible (#8). **The honest entry measured only that
a Ligero leaf does not fit** (1,464,107 B at the ranked leaf); it showed nothing about recursion.
The routes: #8's option (i), accept that recursion closes only with WHIR-class sizes and say so,
changes no trusted base but has no Lean proof plan behind it; every other route (a hash menu, a
larger `proofCap`, a named proximity-gap hypothesis not admissible under V3-5, an
accumulation-shaped relation) changes the trusted base or the relation. Separately, ROM recursion
cannot be a theorem under v3's node clause (Barbara–Chiesa–Guan), so composition across levels
stays a heuristic however the contract is written; the relativized clause (O-25 §13) makes it a
kernel theorem at the price of §15.1's last paragraph.

### 15.3 The scoring rule measures the wrong thing, and there is no machine to calibrate it on

**Known (measured parts, paper conclusion).** Wall time of the root check rewards threads and a
fast hash: the certified verifier takes 20.9 s where a chain-only microbenchmark of the same
function, unrolled, threaded and not proved equal to `chainStep`, takes 37–43 ms, a factor of
about 500× between a certified entry and an unproved microbenchmark (§8.5); no threaded `Vb` was
built as a certified entry. Board T rewards sending witnesses below some level. The proposed
replacements (CPU time on one core, a cap per level or ranking R, a deterministic step count of a
deep verifier) were specified and not valued, because the reference machine (O-6) does not
exist; every number in this record is from a shared QEMU VM without carry-less multiply, on which
the honest entry's four-leaf smoke root verifies in 0.99–1.71 s under a 2 s cap and a WHIR-class
verifier on CompPoly's field would take an estimated 4–40 s.

### 15.4 The second kernel and the compiled toolchain are part of the rules, and they were learned by accident

**Known (measured).** A computable `Fintype` instance made every binary enumerate `2^256` at
start-up; a 64-way `interval_cases` proof took nanoda to 52 GB; `BitVec` compiles to `Nat`
bignums so CompPoly's field is 350–870× slower than a word-level twin; a function-typed digest
cost `32^n` hashes; the contract's list-based codec is quadratic; `decide +kernel` on a
117-entry transcript took 7 m 45 s and 5.3 GB against 7.5 s symbolically (Lessons §8). None of
these is a security fact, every one of them decided whether an entry could be certified or
accepted, and none was predictable from the design text. A design that fixes rules without a
real entry built against them will be wrong in the same way.

## 16. Constraints any next design must satisfy

Stated so that a proposal can be checked against each one. They are the hard-won requirements,
not preferences; the evidence is in §13 and §15.

- **C1 (knowledge is a bounded program).** "The extractor finds a witness" must be a theorem
  about a program whose every step is charged by the contract: a deep embedding with no
  function-typed field, three-address operands, memory charged, a program-size cap, a budget that
  excludes enumeration of the witness space within the domain. A shallow monad, a Lean
  continuation, an expression evaluated in one step, or a measured bound each reopens
  "knowledge = soundness" (V3-S2R-H-M1, H-M2; the user, 2026-10-20). Corollary: the extractor's
  work for a real recursive entry (decoding a committed word of about `2^29` symbols) must fit the
  budget, and the budget's derivation must be an algorithm the machine runs, with a kernel-checked
  control, not an estimate (V3-S2R-M1, M2; F-D1 remains open).
- **C2 (the ROM certificate must say what it does not say).** Whatever the model, the trust
  statement must name the one deployed oracle as a point the theorem cannot see, and the design
  must not rely on review of submitter code for a property review cannot see (ADV-M5). If the
  design keeps the ROM and a submitter-written verifier, it must state which adversary class the
  residual is for; if it closes O-25, it must do so without violating C11.
- **C3 (a knowledge-soundness definition must be satisfiable by a Merkle/BCS verifier).** Before
  any entry is attempted, a kernel-checked positive control for a two-answer challenge and for a
  collision-charging verifier must exist (`twoLucky`, `Vcol`), and a negative control that the
  log-length value is load-bearing (`V24`). A per-query bound over unbounded logs, or a per-answer
  boolean charge, is unsatisfiable (#5).
- **C4 (extraction must be provable from what the log holds).** The relation's recursion clause
  must be such that an extractor can obtain child witnesses from the log of a *random* oracle:
  with a concrete-hash `Vb` in the clause, only decoding works and lookup is unprovable (#7; a
  paper argument, F1 §3.1–§3.2, not kernel-checked). A design that wants cheap extraction must
  change the clause, not the budget; the relativized clause (O-25 §13) changes it and finds that
  a decoding extractor is still what a bounded node circuit admits (T1 Thm 2.2, paper).
- **C5 (the caps must admit at least one honest recursive entry, by paper sizing before the
  stage opens).** `proofCap`, the hash, the arithmetisation, the provable proximity regime and the
  extraction budget must be sized together against a named PCS with a Lean proof plan. At v3's
  values only a WHIR-class PCS fits, "yes, barely", by paper estimate, and none has a Lean proof
  (#8).
- **C6 (succinctness is not wall time).** An admission cap on the verifier must be a CPU-time or
  step-count measure with a published calibration against the best linear verifier the organiser
  can write, or a proved step count; the order is: set the measuring rule, then the benchmark
  shape (the rule may change it), then calibrate the value on the reference machine (#6 (a); §8.5).
  Whether CPU time is the right measure is itself unvalidated (H-m10: it does not remove SIMD).
- **C7 (the score must price recursion or forbid flattening).** Knowledge soundness does not
  enforce recursion; a rule at every level, or a ranked latency column, must (#6 (b)).
- **C8 (completeness must allow error, and the deployment point must be checked concretely).**
  `CompleteWithError` at `2^-128` or `2^-96` over a lazily sampled oracle, with the root, sample,
  smoke and liveness checks under the deployed hash as the only guarantee that honest proofs
  verify there; liveness must run on the native prover's proofs with an emitted log, not only on
  the Lean `P` (V3-S2R-H-M4, #9 item 1).
- **C9 (every executed function on the badge path must be linear-time and strict on the
  benchmark's shapes, and the DoS column must include valid adversarial shapes).** The
  organiser's own reference verifier failed its own canaries and its own DoS cap (#10); lopsided
  valid proofs took 275 s (§8.7).
- **C10 (the toolchain is part of the rules).** Per-kernel budgets for the comparator, measured
  on the reference machine and testable by a submitter before intake; a rulebook note on what
  makes the second kernel blow up (`interval_cases`/`decide` over concrete words) and on what makes
  compiled Lean start-up blow up (computable closed terms, function-typed data); the organiser's
  field, codec and hash on the badge path at word-level speed (§15.4).
- **C11 (the design space stays open).** From the user's rejection of MG1 ("this severely
  restricts the design space for autoresearch agents, while still adding a huge gap for reviewing
  proposals, and requiring manual intervention"): no fixed menu of verifier templates, no human
  review of each proposal as the security mechanism, no manual step in the path from a submission
  to a verdict. The last sentence is **the authors' reading, to be confirmed by the user**: a rule
  may restrict *what the verifier is given* or *how the oracle is deployed*, not *which proof
  system it may be*. Note that C12's "no field" (V3-1) and the "fields as data" direction D-F pull
  against each other; that is a choice for the user, not settled.
- **C12 (the trusted base stays readable).** 500 code lines, Lean core and Mathlib only, no field,
  every definition with a positive and a negative control, a proof never changes the statement it
  proves, three axioms, no code-changing attributes, no elaboration-time code (comments included).
  Every one of these was load-bearing at least once in v3.
- **C13 (a reference machine exists before any cap is valued).** Every measured rule of v3 is a
  placeholder for that reason.
- **C14 (the pin discipline).** Entries are certified only against a core commit that is on the
  remote and pinned in its own commit; the honest entry spent three days certified against an
  unmerged branch (§9.4).
- **C15 (every transcript seed binds the statement).** The one proved positive result for this
  construction family (Fenzi26: deriving the challenges from the generated statement reduces
  soundness to the non-generated relation) is a hard rule, not defence in depth; the honest entry
  seeds with `0x10 ‖ s ‖ enc64 n ‖ h` and T binds `c ‖ csDigest ‖ paramsDigest ‖ x` (O-25 §9.2,
  §11 criterion 9). A canary that the seed includes the statement belongs in the harness.

## 17. Design space for the next iteration

The directions on record, each with what it keeps, what it costs, and the constraint it is most
likely to break. None is chosen here; the user chooses. Directions marked **new, unreviewed**
had no adversarial review when written; the rest cite their source, and a review is named where
one exists (D-A … D-D and D-L have adversarial reviews; D-E … D-K come from memos, issues and
handoffs). After the table, one line per row says which constraint of §16 it breaks.

### 17.1 On record

| Direction | What it is | Known pros | Known cons | Source |
|---|---|---|---|---|
| **D-A. v3 with rule + review + public challenge period for O-25** | keep the submitter-written `V`; a semantic rule in `AGENTS.md` ("no branch of `V` may accept because an oracle answer agrees with a value `V` did not obtain from the oracle or the proof"), a `NOTES.md` disclosure of every answer comparison, mandatory intake review, a challenge period in which anyone may exhibit a magic proof the record's `Vb` accepts (an executable refutation) | nothing in the trusted base changes; full design space; the challenge period is the one check that evaluates behaviour at the deployment oracle | the direct backdoor is one line and review-invisible (ADV-M5.1); a challenge-channel backdoor's magic proof is known to its author and may be hard for the public to find; it is the trust model of every deployed SNARK plus an incentive, no more; the user asked for O-25 to be closed | #4 comment; F2 §9.2, §10.3, §12.4 option (ii); O-25 §2 |
| **D-B. Candidate T (contract-owned verifier template, data-only entries)** | the trusted base owns the transcript, the sumcheck/zerocheck checks and the PCS/Merkle/proximity checks; an entry is a first-order constraint system, parameters, a prover and an extractor; INV′, A1–A4; templates by core PR with a reference spec, `impl = spec`, a proposer embargo | closes the submission-authored CGH mechanism by construction, no meta-theorem; one template reviewed once against an enumerable checklist; the organiser can ship the recursion gadget | reverses V3-1, V3-2 and Q6; narrower than v2; the ranked board is empty until the organiser builds a WHIR-class template and a self-verifying node design; the template review re-imports the review problem; about 100–130 contract lines plus 0.5–0.9k template lines trusted for non-recognition; **rejected by implication** (the user rejected MG1, of which T is the narrowest form; the authors' inference, §14) | F2 round 2; `F2-o25-review-r2.md`; O-25 §6 |
| **D-C. MG1 (admissible menu)** | T with a menu: constraint format (uniform R1CS, CCS, AIR, Plonkish with bounded-degree gates), compiler (Spartan-like, HyperPlonk-like, STARK-AIR), PCS (Ligero, WHIR, Basefold, FRI), field (`GF(2^64)`/`EF`, Goldilocks², BabyBear⁴), each satisfying A1–A4 | restores format, PCS, field and compiler choice | still excludes new IOPs and PCSs, verifier optimisation, accumulation; new items by core PR with review; **rejected by the user** (2026-10-22) | `F2-o25-review-r2.md` §5; O-25 §6.4, §8 |
| **D-D. Tiered: ranked T/MG1 plus an unranked free-form research track** | the research track keeps D-A's `V` with rule, review and challenge; promoted designs enter as templates | keeps a place where a new proof system is first built; unranked by type, not policy | inherits D-B/D-C's rejection for the ranked board; a research-track verifier can still win recognition | F2 R2.5, R2.9; review §5 |
| **D-E. v2-style: agent IOP, organiser BCS** | the agent designs the interactive oracle proof; the organiser's fixed compiler makes it non-interactive | the agent keeps the IOP; the compiler's ROM theorem is proved once | does **not** close O-25 (MG2: the IOP verifier sees a challenge and later messages); forces one BCS configuration (the Q6 gripe); accumulation inexpressible | `F2-o25-review-r2.md` §5 (MG2); design §5.4 of 2026-10-19 |
| **D-F. "Fields as data"** | fields given as `(p, f)` plus proofs, a contract-owned encoding, submission arithmetic proved extensionally equal to the specification; Ligero is field-generic, folding PCSs are family-specific | widens T/MG1's field menu without a per-field template | **unreviewed**; does not by itself address the post-hoc attack or the narrowing the user rejected | O-25 §7 |
| **D-G. Arithmetised random oracle (ARO) for recursion** | change the oracle model to one that gives a non-black-box view, as in PCD from AROs (Chen–Chiesa–Gur–O'Connor–Spooner 2023) | the literature's principled answer to the recursion heuristic | a new trusted oracle abstraction and a larger design change; not a fix for the acceptance backdoor | F2 §13.2 |
| **D-H. Standard-model FS via correlation intractability** | a CI hash under an LWE-type assumption in the trusted base | the only known route to *proving* the FS part | abandons BLAKE2s-only and ROM-only; results are for proofs, not the Micali/Kilian argument template; large trusted base; out of scope by V3-5 | F2 §8, §13.3 |
| **D-I. External VRF challenges** | challenges from a VRF service whose key the prover never sees (Ghosal et al. 2026) | a keyed oracle that works because it is external | leaves the ROM; needs a trusted service; the recursion circuit would need the VRF | F2 §13.2 |
| **D-J. An indexer in the submission** | `I : OProg Key`, `V : Key → …`; `KS` counts `I`'s queries honestly; `Vb` uses `I.run blake2sOracle` once at badge build | unblocks preprocessing SNARKs; removes the one legitimate reason for `V` to compare an answer with a hard-coded constant, which sharpens any O-25 review | orthogonal to O-25's closure; waits on `V`'s type | #8 (3); ADV-M6; CORE-HANDOFF §2.9b |
| **D-K. Relation and cap changes for recursion** | one or more of: an arithmetisation-friendly hash in a menu, a larger `proofCap` for node proofs, a named proximity-gap hypothesis, an accumulation-shaped node clause, fewer and longer leaves | makes an honest recursive entry possible under C5 | each changes the trusted base or the relation; the hypothesis route breaks V3-5 | #8; CORE-HANDOFF §2.9a, §2.9c, §2.14 |
| **D-L. Relativized node clause plus an attested secret oracle (D4; variants W5 and D4+)** | the node clause says "children accepted by `V` on the same log as the game" (`RelL`), so nobody arithmetises the oracle; the harness serves a keyed-BLAKE2s oracle with a fresh key per run and attests the list of answers a child used (`certify`/`attest`, recursive); `final` lets the extractor output a witness **or a BLAKE2s collision as data**; completeness in context form; W5 attests only the ≈ 500 Fiat–Shamir answers and keeps Merkle trees public; D4+ routes the leaf chain through the oracle | O-25 closed **by the deployment** (the relation alone leaves the backdoor certified, kernel; the secret oracle closes it modulo PRF security, paper) and the liveness mirror with it; whole-tree composition a kernel theorem (`compose`, `paper_tree`); an agent-written `V` that may compute anything on answers; no per-entry review, no menu; about 50 trusted lines (estimate); D4+ closes #6 (a) by the certified caps (paper) | a trusted harness service, the first runtime component whose bug is accept-all; records certify the *attested* deployment and are checkable only by the organiser, online, until the key is released after freeze (a designated-verifier window; key reuse reinstates CGH); a knowledge clause whose content rests entirely on `Computes` (`acceptAll_choice`); the succinct node's soundness is a paper obligation (W2 §A.4, the same as #7); #6 (b), #7 and #8 unchanged; in the pure ROM without attestation the requirement is vacuous or non-compressing (kernel + paper); service traffic `≈ 10^8` calls per tree all-oracle (W5: `≈ 2.5·10^5`, at the price of an unfalsifiable extractability heuristic); leaves V3-5's "ROM only" | `origin/explore/relativized-nark`, head `043bcb3`: `docs/explore/REPORT.md` §1, §5, §7, §9; `docs/reviews/EXPLORE-report-review.md` (M1–M6, m1–m21, applied); O-25 §13 |

**Which constraint each row breaks (§16).** D-A: C2 (relies on review for a property review
cannot see). D-B, D-C, D-D: C11. D-E: C2 (does not close O-25) and the Q6 gripe. D-F: unreviewed;
pulls against C12's "no field". D-G: C12 (a new trusted oracle abstraction) and scope. D-H: V3-5
and C12. D-I: V3-5 (leaves the ROM) and C4's recursion (the circuit would need the VRF). D-J:
none on its own; orthogonal to O-25. D-K: C12 or V3-5 or the relation, by option. D-L: V3-5
(leaves the pure ROM for a trusted service), C13-type trust in a runtime component, and whether
"checkable only by the organiser until key release" is "manual intervention" in the user's
sense (C11) was not asked.

### 17.2 New directions (unreviewed; the author's, 2026-10-22)

These were written for this record without an adversarial review, a probe or a sizing. They are
listed because they aim at C11 directly. Two of them overlap the relativized exploration, which
was not known to the author when they were written: N3 overlaps D-L's D2/D4 (a harness-sampled
keyed oracle), and N5 overlaps D-L's D1 (rank leaves, keep recursion unranked); D-L's review
applies to both and is the better-examined form.

- **N1. Verify at the deployment point, not in the ROM: a kernel-checked concrete run.** Instead
  of asking the certificate to speak about BLAKE2s, make the one deployment-point check the
  harness does (the smoke tree under `blake2sOracle`) a kernel theorem per entry, for a fixed
  public instance set sampled after freeze, so that "`Vb` accepts the honest proof under BLAKE2s"
  and "`Vb` rejects these canaries under BLAKE2s" are kernel facts rather than measurements. Pro:
  removes the liveness mirror from the trust statement; no narrowing. Con: it says nothing about
  false statements, so it does not touch the acceptance backdoor at all; kernel evaluation of
  BLAKE2s costs about 2.4 s per compression and the honest entry's transcript KAT took 68.6 s for
  one leaf, so a tree would be out of reach without a faster kernel path.
- **N2. Score the verifier's *oracle* work only.** Separate `V` into the oracle-facing part (a
  deep program over an oracle primitive, step-counted by the contract, in the spirit of O-18) and
  a free Lean part that may only consume opaque results of the first. The step count then prices
  succinctness (C6) deterministically and the free part cannot see answers (R1 of F2 §2). Con:
  this is Candidate E's `D`-half again; every honest Fiat–Shamir verifier needs the challenge as a
  value in the free part, and O25-M1/M2 reopen. It would have to be combined with something that
  closes the challenge channel, which nothing on record does without C11's cost.
- **N3. A two-oracle certificate with a hidden-instance game instead of a parametricity
  argument.** Require `KS` and completeness for an oracle family indexed by a secret the harness
  samples after freeze (a keyed BLAKE2s, `H_k(q) = BLAKE2s(tagRO ‖ k ‖ q)`), *and* forbid the
  recursion circuit from knowing `k` by changing the node clause so that a node verifies children
  under a *different*, public, per-level derivation of the key that the circuit can compute but
  the outer verifier does not accept as its own. Pro: the S1 review's "no salting fixes it"
  argument rests on the prover needing `k`; separating the key the circuit evaluates from the key
  the outer `Vb` runs under might break that. Con: this is a guess; the review's two-query
  counting argument may adapt; recursion across levels needs the same oracle on both sides of
  `Rel`, which this changes; it probably moves the backdoor to the derivation function. **Overlaps
  D-L** (D2/D4), where the same idea is worked out with the relativized clause and an attestation
  service, and where the exploration finds that a secret key alone, with v3's concrete-BLAKE2s
  recursion, does not work and that the pure-ROM relativized form does not compress.
- **N4. Accept the ROM residual explicitly and price it: a public bounty on magic proofs funded
  by the leaderboard.** A design choice, not a mechanism: every ranked record posts a stake that
  is forfeited to whoever exhibits a proof the record's `Vb` accepts for a statement with no
  witness (the harness can decide "no witness" for the benchmark's own leaves, whose starts it
  holds). Pro: meets C11, no trusted base change, makes D-A's challenge period incentivised in a
  way the v3 record only asserted. Con: not a security argument; a challenge-channel backdoor's
  author is the only one who knows the magic proof.
- **N5. Drop recursion from the ranked relation for a season.** Rank leaf throughput over many
  independent chains at a size where a Ligero- or WHIR-class leaf fits `proofCap` (the honest entry
  fits up to `n = 4,096`), keep the node clause for an unranked recursion board. Pro: an honest
  entry exists today; C5 holds; O-25's payoff shrinks to a leaf board. Con: the competition's point
  was recursion; O-25 is unchanged in kind. **Overlaps D-L's D1** (leaves timed, recursion never
  run), whose review found that at `n = 2^14` a witness-sending leaf check beats any SNARK leaf
  check and that the winner would be a chain prover with any verifier (A1 M10).

### 17.3 How to evaluate a candidate

Against C1–C14 (§16), one line each; then the three questions the record shows matter most:
(i) write the backdoor for it (`Backdoor.lean` shape, the literal trigger, the post-hoc attack) and
say precisely which check stops it and why that check is organiser code; (ii) size one honest
recursive entry against its caps on paper, naming the PCS and its Lean proof plan; (iii) state
what the reference machine must be and what the measuring rule is before any value is set.

## 18. Record

- **The contract.** `scaraven/recursion.fast`, branch `v3/contract-archive`, head `f4de3b8`
  (contract state `6202402`; `c198bc3` and `f4de3b8` add `evidence/`):
  `RecursionFast/Contract/*.lean` (the text quoted in §4–§6), `RecursionFast/Library/`,
  `RecursionFast/Controls/` (including `Backdoor.lean`, `Potential.lean`, `LogScan.lean`,
  `Completeness.lean`), `scripts/` (`Gate.lean`, `source-rule.py`, `AxiomAudit.lean`,
  `olean-manifest.py`, `loc.py`, `ci.sh`, `tools.env`), `docs/DESIGN-v3.md` (patched by S2R),
  `docs/DESIGN-AMENDMENTS.md`, `docs/stages/V3-S1-RESULT.md`, `V3-S2-KS-RESULT.md`,
  `V3-S2R-RESULT.md`, `docs/reviews/V3-S1-review.md`, `V3-S1-golf.md`, `V3-S2-KS-review.md`,
  `V3-S2R-handoff-review.md`, `V3-S2R-review.md`, `V3-S2R-golf.md`, `docs/reference/`; and
  `evidence/` (`README.md` the index; `probes/`: `LiteralTrigger`, `CountingForm`, `TaskRfl`,
  `Shallow`, `Review`, `P1_interface`, `P2_hatches`, `T1_pub_sees` with their logs, and the
  throughput logs `fastchain.log`, `refchain.log`, `build.log`; `interim-harness/`: the two interim
  harness series as `git format-patch` files).
- **The relativized exploration.** `scaraven/recursion.fast`, branch `explore/relativized-nark`,
  head `043bcb3` (not merged, not archived elsewhere): `docs/explore/BRIEF.md`, `REPORT.md`,
  `notes/` (T1, W1, W2, A1–A3, C1, L1, P1–P4), `probes/`, `docs/reviews/EXPLORE-report-review.md`,
  `RecursionFast/Explore/` (21 modules).
- **The entries and the honest-baseline record.** `scaraven/recursion.fast-submissions`:
  `submissions/baseline/`, `submissions/spartan-chain/`, `AGENTS.md`, `docs/design/` (the
  2026-10-19 design, v2, v0.3, `DISCUSSION.md`, the v2 ledger, the workspace plan),
  `docs/baseline/BASELINE-TASK.md` and `v2-example/`, `docs/core/` (the v2 handover, the harness
  README, the v2 stage and review records), `docs/report/` (the v1.0 report that §2 cites),
  `docs/research/` (R1–R8 and the A1–A8 reviews, including R4 ArkLib and R7 the literature that
  F1's WHIR sizing cites), `docs/snark-baseline/` (`PLAN.md` D-1 … D-12 with no D-7, `REPORT.md`,
  `CORE-HANDOFF.md`, `BLUEPRINT-R1.md` with its own D-7 … D-11, `IMPLEMENTERS.md`, `notes/` E1–E4,
  F1, F2, ADV1, `reports/`, `issues/` I1–I7, the drafts of #5–#10 and the #4 comment),
  `docs/reviews/` (`BLUEPRINT-R1-review.md`, `BLUEPRINT-R1-S9-review.md`, `V3-S2a-review.md`,
  `V3-S2a-golf.md`, `V3-S2b-midreview.md`, `V3-S2b-review.md`, `V3-S2b-golf.md`,
  `V3-S2-KS-review.md`, `F2-o25-review.md`, `F2-o25-review-r2.md`, `V3-ideation-docs-review.md`,
  `V3-ideation-docs-fixes.md`), `docs/stages/V3-S2a-RESULT.md`, `V3-S2b-RESULT.md`.
- **The v2 tree.** The core's tag `v2-archive` (the 2→1 wall-time design, `Compile.lean`, the
  RISC-V machine, the v2 harness, 143 amendments S1-A1 … S9-A44).
- **Logs.** Local to the development VM under `logs/` of each repository; the lessons document
  names them (Lessons §9), and says which probes were copied into `evidence/`.
- **Kernel probes** cited by id: archived in `evidence/probes/` on `v3/contract-archive`
  (`CountingForm`, `LiteralTrigger`, `TaskRfl`, `Shallow`, `Review`, `P1_interface`, `P2_hatches`,
  `T1_pub_sees`); still local only: `logs/ks-review-probes/` (`PaperTheorem.lean`, adopted into the
  library; `Truncated.lean`, `Redundant.lean`, `Snag.lean`), `logs/s2b-review-probes/`,
  `logs/s2b-final-review-probes/`, `logs/adv-probes/RefChain.lean`, `FastChain.lean` (their logs
  are archived).

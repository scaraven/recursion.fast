# Relativized recursion with an attested oracle: a design proposal for recursion.fast

Status: **proposal, not in force** (2026-10-22). `docs/DESIGN-v3.md` stays authoritative until the
user adopts this document, whole or decision by decision (§12.2). Nothing here is implemented.

**Provenance.** This document compiles the exploration on branch `explore/relativized-nark`
(2026-10-20 to 2026-10-22, head `043bcb3`): the final report [REPORT], its adversarial review and
fix pass [REVIEW], the prompt review [PROMPT], twelve notes and 21 Lean probe modules. The branch
will not be merged, so this document is self-contained and cites it by URL (§13). Where a note
disagrees with the report as fixed by its review, the report wins, and an attack note wins over the
design note it attacks (§9). This document's own adversarial review and fix pass are [DREVIEW].

**Base.** The rules rewrite (`v3/rules-handoff`, stage V3-S2R): potential-form `KState`;
`CompleteWithError` with `δ ≤ 2^-128` over a lazily sampled oracle; a step-counted `XProg` extractor
with `Computes`, `B t = 2^48 + 2^16·t`, `outCap = 2^24` words, and queries shorter than `2^64` bytes
(V3-S2R-A9); 292 contract code lines of 500. `v3 §n` cites its `DESIGN-v3.md` (`main`'s predates it).

**What it would change in v3.** Decisions V3-4 (completeness moves into the game), V3-5 (a trusted
harness capability beyond the ROM), V3-6 (keyed BLAKE2s behind a service replaces public BLAKE2s),
V3-7 (the relation is parameterised by `V` reading the log, not by `Vb`) and, with R3 only, V3-8
(`T_V` becomes a liveness cap); sections v3 §2.1, §2.2 (`qV`, under R3), §3.1, §3.2, §3.4, §4.2–4.5,
§5.3, §5.4, §6.3, §6.5, §6.7, §8, §11, §12. Issue #4 (O-25) closes at R2 and #6(a) at the optional
R3, by a paper argument; #6(b), #7 and #8 stay open.

**Reading.** A bare `§n` is this document's; §4 is normative for a later contract stage, §5–§6 are
optional, §12 holds the open items and the user's decisions. **Evidence tags**, as in the report:
**kernel** (a probe theorem on `propext`, `Classical.choice`, `Quot.sound` only, §13), **paper**,
**measured** (a log), **estimate**. Most probes are toys; §13.1 gives every theorem's scope.

| Term | Meaning |
|---|---|
| query log `L`, `runLog L` | the oracle's answers so far; running `V` "on the log" answers its queries from `L`, `none` if one is missing |
| potential `μ` | a submitter-chosen map from logs to `[0, ∞)`: `0` on the empty log, rising by at most `ε` on average per fresh answer; below `1` every accepted proof is extractable. The bound `(Q + qV)·ε` is Markov's inequality on it |
| `E`, `Computes`; decoding; escape | the extractor's specification, computed by a step-bounded `XProg` within `B t`; a decoding extractor returns the child proofs committed in a node proof, as any bounded node circuit forces (issue #7); an escape is an extractor output other than a witness, a BLAKE2s collision or (W5 only) a late preimage |
| board T, `T_V`, `qV`, `proofCap` | v3's ranked whole-tree wall-time board; the root verifier's time cap; the certified bound on verifier calls (`≤ 2^16`); the proof-size cap (1 MiB) |
| shapes; `h_V` | ranked `r = 8, n = 2^14` (256 leaves, 255 nodes, `2^22` chain steps); long `r = 4, n = 2^20`. `h_V`: 64-byte compressions one verification feeds the oracle, 25.9k spartan-chain, 9.2k leanVM-class, 5–12k WHIR-class ([C1] §2.1, estimate) |
| spartan-chain; Flock, WHIR, leanVM | the certified honest leaf SNARK of the submissions repository (Spartan + Ligero over GF(2^64)): 5,156 queries at `n = 2^14` and 7,774 at `2^20`, a 1,464,107-byte proof and 7.4–8.0 s to prove at `2^14` (**measured**; [A3] m5). Flock (ePrint 2026/1329) is a binary-field prover for BLAKE-family hashes, timed with a fixed verifier by snark.fast's Flock Challenge; WHIR is a hash-based polynomial commitment; leanVM a zkVM using Flock for BLAKE2s |
| #6(a), #6(b) | (a) the trivial witness-sending root passes `T_V`; (b) board T does not reward recursion over proving a subtree flat |
| D1–D4, W4, W5, D4+ | priced recursion; pure-ROM tree; signed oracle; attested oracle (§3–§4); published log (§4.10); channel split (§5); oracle-chain leaf (§6) |

---

## 1. Objective and the one-line pitch

**One line.** Keep v3's relation but judge a node's children by `V` reading the knowledge game's own
query log, not by `V` on public BLAKE2s. Nothing then arithmetises the oracle, so the harness can
serve it as a secret keyed-BLAKE2s function and vouch for the list of answers each child proof used;
the parent circuit hashes that attested list where a pure-ROM parent would re-ask every answer.

**What changes.** O-25 and its liveness mirror close by the deployment (paper, §4.9; the relation
alone does not close O-25, **kernel** `Backdoor.backdoor`). Composition across levels becomes a
theorem, kernel for any attested knowledge state and paper only for the succinct node's (§4.6). PRF
security of keyed BLAKE2s and constructive collision resistance replace "BLAKE2s is a random oracle".
Optionally (R3), #6(a) closes by the certified caps (paper, §6). The cost: a trusted service whose
bug would be accept-all, about 53 trusted lines, a designated-verifier window until key release, and
records that certify the attested deployment (§10, §12.2).

**What does not change.** `Rel`, `Wit`, the concrete leaf chain under R1–R2; board T, column R, DoS;
the potential form and `step`; the `Computes`-bounded extractor and budget; `proofCap`, `errorCap =
completenessCap = 2^-128`, `qV ≤ 2^16` (R1–R2; `2^13` under R3); comparator → gate → badge; issues
#6(b), #7, #8. A real-world recursion from a winner still rests on the usual heuristic (CGH, §2).

### 1.1 Decisions (proposed)

| Id | Decision | Why, in one line |
|---|---|---|
| RR-1 | The node clause reads child acceptance from the game's log: `Rel (accL S.V L)` replaces `Rel S.Vb`; `Rel`, `Wit`, the leaf clause unchanged (§4.1). | `final` re-applies to extracted children on the same log; no part of the relation evaluates the oracle. |
| RR-2 | The oracle is a harness service: BLAKE2s in keyed mode, key fresh per timed run, held by a separate process (§4.8). | CGH needs a public seed; with a secret key the ROM bound holds at deployment up to `Adv_PRF` (§4.9). |
| RR-3 | The service certifies lists of answers and earlier attested hashes (recursively) and answers `attest`; a node verifier makes two `attest` calls, or one when the node prover certifies `[att h₁, att h₂]`, and `qV` counts them (§4.2, §4.8). | In the pure ROM a parent must re-ask (§3.2); attestation replaces it. A flat variant is linear in the tree. |
| RR-4 | List hash: BLAKE2s under `tagList = 0x41` of a prefix-free encoding; `Valid` carries the service's caps (queries ≤ `2^20` bytes, ≤ `2^16` items, ≤ `2^24` bytes) (§4.2, §4.3). | Unbounded, distinct lists share one preimage (`hashList_not_coll`); uncapped, a collision output cannot fit `outCap`. |
| RR-5 | `KState` gains a deterministic `cert` law; `final` lets `E` return a witness or a BLAKE2s collision as data, under `Computes` (§4.4). | A collision proposition is pigeonhole-true; even the output form needs `Computes` (`acceptAll_choice`). |
| RR-6 | Completeness over honest contexts: `δ` bounds each honest prover run inside an honestly built tree (§4.5). | `CompleteWithError` takes the relation outside the game; an unrestricted context can search for a failing statement. |
| RR-7 | Delete `Submission.Vb`, `blake2sOracle`, the v3 §6.7 recognition rule and the intake review of `V` for recognition (§4.7, §11). | No instantiated verifier; no instantiation for `V` to recognise. |
| RR-8 | The service: own uid, the prover's cpuset and CPU cgroup, spinning batched shared-memory rings, caps; a refused call aborts as a reject; it never verifies a proof (§4.8). | Outside the cgroup it is a free co-processor; a futex round trip costs 82×; a refused call returning a value is a symbol the model lacks. |
| RR-9 | W4: publish the certified-list log; release the key after the record is frozen (§4.10). | Third-party verification; post-release proofs are never scored. |
| RR-10 | Do not adopt D1 or D2 (§3.1–§3.3). | In the pure ROM the requirement constrains nothing or makes recursion unrankable; the charge is gameable. |
| RR-11 | W5, the channel split, as optional stage R4, only if the user accepts its heuristic (§5). | Exact in-circuit costs and about 1/1000 of the traffic, for one unfalsifiable heuristic. |
| RR-12 | D4+, the oracle-chain leaf, as optional stage R3 with `qV ≤ 2^13`, `proofCap < 64·n` and a `chain` call (§6). | Closes #6(a) by the certified caps (paper); retires the CPU-time `T_V` rule. |
| RR-13 | #6(b) by the benchmark shape or an explicit flattening policy, not by the relation (§7.2). | No theorem studied forces recursion below the memory limit; at the long shape recursion costs about 1.17× flat. |

Six decisions are the user's, RU-1 … RU-6 (§12.2).

---

## 2. The problem

**Why O-25 exists.** v3's node clause is `c = nodeStmt c₁ c₂ ∧ Vb c₁ π₁ = true ∧ Vb c₂ π₂ = true`,
`Vb` being `V` run with `blake2sOracle q = BLAKE2s(tagRO ‖ q)`, so a node proves `V`'s BLAKE2s calls
in-circuit and the oracle must be public. A verifier can then compute it, compare with an oracle
answer and on a match accept a magic proof, a `2^-256` event over oracle functions that the counting
definition cannot see: CGH uninstantiability. `Controls/Backdoor.lean` on `main` certifies such a `V`
(**kernel**); it passes every check of v3 §6.3, so v3 relies on a rule and review (v3 §5.4, §6.7), and
its mirror, rejecting honest proofs exactly under BLAKE2s, is certified too. The submissions
repository's F2 memo (`docs/snark-baseline/notes/F2-o25-uninstantiability.md`) concluded *"the only
way to make the instantiation unknowable is to make it external, which recursion forbids."*

**The user's idea** removes that premise: if the node clause runs the children **under the same
oracle as the security game**, no circuit for the oracle is needed, so it may be external and secret.
Resolved from the prompt ([PROMPT]): the leaf stays concrete BLAKE2s (§3.4); "a million hash chains"
is a shape parameter; "compressing" means less root-verifier work than witness-sending (witnesses are
48 bytes a leaf); and the oracle's deployment, which the prompt omits, decides.

**The impossibility result.** Barbara–Chiesa–Guan (ePrint 2024/728, TCC 2025) prove
`DTIME^O[t] ⊄ NARG^O[vq = o(t)]` and `NTIME^O[t] ⊄ NARG^O[as = o(t)]`, also for interactive and
computationally sound arguments: separations for specific hard relations. They **do not apply
verbatim**: if `V` is complete for every oracle, the node relation's language is the oracle-free set
of honest tree digests, modulo BLAKE2s cycles ([T1] Prop. 1.4, paper). **Knowledge brings the
obstacle back** by the paper's flipping technique: a verifier that does not ask a query a child's
validity depends on cannot see that answer flipped, yet the extracted child is then invalid on the log
([T1] §2.5; §3.2). Relativized SNARKs exist in the signed random oracle model (SROM, Chiesa–Tromer
2010: "a trusted Internet service"), which the paper's §1.2 names with the LDROM and AROM; D4 is the
SROM with an online check for signatures ([L1]). The technique fails in D4 at both steps ([T1] §6.1,
paper): a flipped list cannot be certified, and one flipped point changes `attest` on every list.

---

## 3. Design space, and why the alternatives were rejected

### 3.1 D1, priced recursion that is never run

D1 certifies relativized knowledge soundness, times leaves over many chains and charges `t_hash` per
verifier oracle call ([A1], [C1]). The clause is dead weight (§3.3) and the charge gameable in every
self-measured form: `T_leaf/n` is ≈ 0 for witness-sending leaves, the slope in `n` is 0 or negative
under padding or sleeping, a constant per call falls 20-fold with one 512 KB query (≈ 260 calls, not
5,156), and a constant per compression is a certificate quantity needing no run. Local work goes
unpriced (spartan-chain's verifier alone does about `3.1·10^7` field multiplications), and the charge
captures 93–99.6% of an R1CS-of-bits recursion step, 69–75% for FRI-based ones, about 10% for leanVM,
under 1% with a non-native field (C1, estimate). A million chains take 89 days at spartan-chain speed;
per-proof statistics measure 8–41% of a tree's work (C1 §6, estimate). With a public oracle O-25 is
unchanged (**kernel**, `Backdoor.backdoor`). The winner is a chain prover with any verifier (A1 M10).

### 3.2 D2, the relativized tree in the pure ROM, and the re-ask law

D2 is v3's tree under the relativized relation with a secret service; the service closes O-25 and
composition becomes a theorem (paper; A1 §5, m10), at the price of the **re-ask law**:

- **Kernel** ([P1], [P4]; scopes in §13.1). A *lazy* parent, judging children against supplied answers
  without asking, has no knowledge state for the natural extractor at any error, and every extractor
  of one outputs a `Collides` witness, a BLAKE2s collision for a leaf `c₁` (`lazy_no_kstate`,
  `lazy_extractor_collides`); re-asking is sound and asks at most the `|Q|` carried queries
  (`deferState`, `queries_defer`); a decoding extractor forces the parent to read every query a
  committed child reads while the log without it stays below potential 1 (`reask`, `flip_reask`).
- **Paper** ([T1] Thm 2.2). Decoding extractors are the only kind a bounded node circuit admits
  (#7); the parent re-asks each child query its validity depends on, failing to with probability at
  most `(Q + qV)·ε` per query; spot-checking saves nothing at fixed error (T1 Prop. 2.4). For the
  paper's own hard language, L1 derives from its Thm 4.1 that a verifier at error `2^-128` may skip at
  most a `2^-63` fraction of the queries.

**Consequences** (estimate; [C1] row 4, [T1] §3). The ranked deferral root re-asks `511·h_V` =
2.6–13.2 M compressions with an 80–850 MB proof, 0.6–3.2× witness-sending's `2^22` hashes, and
concatenating 256 leaf SNARKs (1.3–6.6 M compressions plus 256 checks) dominates it; at the long shape
deferral takes 35–90 ms, 9–22× better, compressing but not succinct; relativized IVC never
compresses. **The unit decides** (A1 M3, report review M6): in *queries* the ranked root compresses
about 3× (`n = 2^14` against 5,156; compressing exactly when `n > qV_leaf`), in 64-byte
*compressions*, the unit an honest in-circuit cost and an unriggable charge must use, it does not;
they agree at `chainCap`, about 200×. Under v3's caps D2 cannot run beyond `r = 2`: its root breaks
`qV ≤ 2^16` by 40× and `proofCap` by 250× (A1 M2).

### 3.3 The relativized requirement constrains nothing

**Kernel**: witness-sending is relativized knowledge-sound at potential 0, error 0, 0 queries
(`ws_ksRel`); concatenation inherits the leaf verifier's potential and error (`concatState`); and the
lift (`lift`, T1 Thm 4.1) makes *any* knowledge-sound `V₀` for the oracle-free statement "this digest
is the runner's `treeRoot` over these starts", starts in the clear, relativized knowledge-sound with
`V₀`'s own potential, error and query bound, never running itself on a sub-proof. With a succinct flat
SNARK the root is succinct and nothing recurses (the Lean `V₀` is non-succinct; a succinct one is
paper). The library format limits the lift to `2^14` leaves (`lift_runner_ws`, `d ≤ 14`; `d ≤ 13`
once the halves must fit, paper), a cap-free one to none (`lift_free`). Its completeness is paper and
holds for children whose clear statement is true: an entry under §4.5's honest contexts, not under a
clause over every accepted child (P4, report review M3); witness-sending and concatenation are
perfectly complete (`concatV_node_run`). So relativized knowledge soundness is not amenability to
recursion (A1 m1), and D2's charge prices what v3 already pays in `T_tree` ([T1] §0).

### 3.4 Other directions

- **D3, signed oracle.** D4 with hash-based signatures verified in-circuit: +145 (XMSS) to +1,059
  (WOTS+ worst case) compressions per child, 0.5–12% of the node, and a trusted signature
  specification of 150–300 lines with the signing-oracle model (C1 §4.2, W1 §4, estimate). D4 with W4
  dominates it unless proofs must be verifiable offline *during* the evaluation.
- **A digest-parametric `V`** (F2, issue #4, v3 §12 O-25) cannot support Fiat–Shamir without a
  challenge interface, and its typed-interface form is broken (the submissions repository's
  `docs/reviews/F2-o25-review.md`, O25-M1–M3); unnecessary here.
- **Salts, time-released keys** ([W1] §10): a salt the prover knows rides in the proof (F2 §6); a
  released key protects only earlier proofs. Both reduce to RR-2's secret key.
- **Harness-served LDROM/AROM** ([W1] §8): unservable at digest-sized domains, practically a public
  hash plus its arithmetisation (v3 with CGH open). **Scoring-only fixes** are gameable (A1 M3, M10);
  standard-model challenges violate V3-5.
- **A leaf over the oracle**, `x = O^n(w)`: in the pure ROM its verifier needs about `n` queries
  ([T1] §4.4, paper). Attestation removes that objection (§6).

---

## 4. The design: relativized relation plus attested oracle (D4)

Normative for stages R1–R2 (§11): [W2] §A as corrected by [W2] §B, the attack notes, the report
review and [DREVIEW] (§9). Lean blocks give the shape of the contract text; the stage fixes names.

### 4.1 Relation

```lean
/-- `V`'s verdict on the log `L` under the proof-size cap: v3's `Vb` with the log for BLAKE2s. -/
def accL (V : Digest → Proof → OProg Bool) (L : Log) (c : Digest) (π : Proof) : Bool :=
  π.size ≤ proofCap && ((V c π).runLog L == some true)
/-- The relation of a submission on a log: v3's `Rel` with `accL S.V L` as its verifier. -/
def Submission.RelL (S : Submission) (L : Log) : Digest → Wit → Prop := Rel (accL S.V L)
```

A leaf's witness is a chain start, as in v3 (concrete tagged BLAKE2s); a node's is two child digests
and proofs that `V` accepts **reading the same log as the game**, within `proofCap`. **Why.** `final`
applied to a root gives children accepted on the same log at the same potential, so it applies again
(§4.6), and the relation never evaluates the oracle. v3's form cannot compose: `V3.v3_no_compose`
(**kernel**) exhibits, on a potential-0 log, a node proof that v3's certified backdoor verifier
accepts but whose children its certified extractor does not open, being accepted under BLAKE2s, not
on the log. Knowledge soundness becomes a fixed-point property of `V` ([T1] §1.3), and completeness
moves into the game (§4.5). P1's `RelL` and P2's `RelA` lack only the `proofCap` conjunct. Alone it
does not close O-25: `Backdoor.backdoor` (**kernel**) is relativized knowledge-sound at `errorCap`
with one query and accepts a 32-byte magic proof of every statement under `blake2sOracle`.

### 4.2 Oracle programs, events and logs

```lean
inductive Item | ans (q : ByteArray) (a : Digest) | att (h : Digest)      -- answer; attested hash
inductive Ev   | ans (q : ByteArray) (a : Digest) | cert (xs : List Item) -- fresh answer; certification
abbrev Log := List Ev
inductive OProg (α : Type)
  | ret (a : α) | query (q : ByteArray) (k : Digest → OProg α)
  | attest (h : Digest) (k : Bool → OProg α) | certify (xs : List Item) (k : Bool → OProg α)
def Log.answer   (L : Log) (q : ByteArray) : Option Digest  -- the first `ans q _` of `L`
def Log.attested (L : Log) (h : Digest) : Bool              -- some `cert xs ∈ L` has `listHash xs = h`
def queryCap : ℕ := 2^20      def listItemCap : ℕ := 2^16      def listByteCap : ℕ := 2^24
def Valid (L : Log) (xs : List Item) : Prop :=    -- the service accepts `xs` on `L`
  xs.length ≤ listItemCap ∧ (encList xs).length ≤ listByteCap ∧ ∀ x ∈ xs, x.OK L
--   OK (ans q a) := q.size ≤ queryCap ∧ L.answer q = some a;   OK (att h) := L.attested h
def WF (L : Log) : Prop  -- every `cert xs` of `L` is `Valid` on its prefix
def OProg.runLog (L : Log) : OProg α → Option α
  | ret a       => some a
  | query q k   => (L.answer q).bind fun a => (k a).runLog L
  | attest h k  => (k (L.attested h)).runLog L
  | certify _ _ => none
def OProg.calls (H : ByteArray → Digest) (A : Digest → Bool) : OProg α → ℕ  -- queries and attests
```

**Semantics, and why.**

- **`attest` answers `false` on a miss**, as the service does. Harmless ([W2] m3): any adversary
  can make an attestation answer `false` (ask a random `h`), so a branch accepting on `false` adds
  nothing a certified `V` can use; a `V` accepting on `false` alone accepts on the empty log for every
  statement, which is the accept-all obligation `Computes` with a real extractor cannot meet.
- **A verifier's `certify` reads `none`**, so a certifying `V` is never accepted; the honest prover
  certifies, as game moves (§4.5). **`runLog` reads the final log** (v3 §4.2). **`Valid` needs answers
  already in the log** (an item the service evaluates on the fly is "query, then certify").
  **`calls` counts `attest`**, so `qV` bounds it.
- **`Valid` carries the service's caps** ([DREVIEW] M2), so certified lists of a `WF` log are bounded,
  collision outputs fit `outCap` (§4.4) and the model certifies exactly what the service does;
  `queryCap` implies V3-S2R-A9's `2^64` bound. A direct query above `2^20` bytes is refused only at
  deployment, as a reject ([W2] m1).
- **A child's in-circuit run against its carried list is Library**, with P2's **lookup semantics**
  (`runItems`): a query takes the first `ans q _` item; `attest h` succeeds only if `att h` is an item,
  else `none`, never `false`, which could be `true` on the log. So `runItems_valid` (**kernel**)
  holds for every program: a verdict read from a list valid on `L` is the verdict read from `L`. W2's
  trace semantics agrees on valid lists whenever it gives a verdict (paper, P2 deviation 3).
- **Monotonicity holds for clean runs** (bounded queries, every attestation `true`;
  `runLog_append_of_clean`, **kernel**); a run that branched on a `false` attestation may change
  verdict once the hash is certified. Definitions: `Attested/Model.lean`; controls:
  `Attested/Controls.lean` (§13.1).

### 4.3 The list encoding

```
encItem (ans q a) = 0x00 ‖ enc64 |q| ‖ q ‖ a        (41 + |q| bytes)
encItem (att h)   = 0x01 ‖ h                         (33 bytes)
listHash xs       = BLAKE2s-256 (tagList ‖ concat (map encItem xs)),   tagList = 0x41
```

`tagList` is a fifth first byte, distinct from `tagChain = 0x43`, `tagLeaf = 0x4C`, `tagNode = 0x4E`
and `tagRO = 0x52`; the item codes are prefix-free. **Why a bound** (**kernel**): `enc64` writes a
length's low 64 bits, so an answer to a `2^64`-byte query re-parses as other items (`encList_not_inj`)
and two distinct lists share a `hashList` with the **same preimage** (`hashList_not_coll`), no BLAKE2s
collision; on bounded lists the encoding is injective (`Item.enc_append_inj`, `encList_inj`), and
`IsColl x y := Bounded x ∧ Bounded y ∧ x ≠ y ∧ hashList x = hashList y` is two distinct byte strings
with one digest (`IsColl.blake2s`). `Valid`'s `queryCap` puts certified lists in that range, and the
carried list is bounded by `V`'s circuit, which enforces the same caps (the probe's `attV` checks
`Bounded`), as V3-S2R-A9 does for `Computes`. **No menu**: the list hash stands for a real recursion's
oracle hashes in-circuit, so the contract fixes BLAKE2s ([W2] m6); no concrete preimage meets `PRF_k`.

### 4.4 Knowledge soundness

```lean
inductive Out | wit (w : Wit) | coll (x y : List UInt8)   -- a witness, or two strings with one digest
def Sound (R : Digest → Wit → Prop) (c : Digest) : Out → Prop
  | .wit w    => R c w
  | .coll x y => x ≠ y ∧ blake2s256 x = blake2s256 y
structure KState (R : Log → Digest → Wit → Prop) (V : Digest → Proof → OProg Bool)
    (E : Digest → Proof → Log → Option Out) (ε : ℝ≥0) where
  μ     : Log → ℝ≥0
  empty : μ [] = 0
  step  : ∀ L q, L.length < logCap → μ L < 1 → L.answer q = none →
            ∑ a : Digest, μ (L ++ [.ans q a]) ≤ (μ L + ε) * 2 ^ 256
  cert  : ∀ L xs, L.length < logCap → Valid L xs → μ (L ++ [.cert xs]) ≤ μ L
  final : ∀ L c π, WF L → L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
            ∃ o, E c π L = some o ∧ Sound (R L) c o
def KS (R) (V) (E) (ε : ℝ≥0) (qV : ℕ) : Prop :=
  Nonempty (KState R V E ε) ∧ ∀ H A c π, (V c π).calls H A ≤ qV
```

`step` is v3's. `cert` is deterministic, so a certification may not raise the potential; an honest
potential ignores `cert` events (P1 states lift with `μ ∘ ansLog`, `KStateA.ofRel`, **kernel**).
`final` is v3's with the log-dependent relation and `Sound`; `WF L` in it costs nothing
(`KStateA.gμ_*`, **kernel**). `Out.coll` holds byte strings because tree collisions also involve
65-byte node and 41-byte leaf preimages and cross tags (§4.6); a list collision is two encodings of at
most `1 + 2^24` bytes, about `2^22` words, inside `outCap` (§4.2). Without §4.3's bound a list mismatch
can have equal bytes and `.coll` fails `x ≠ y` ([W2] M1).

**Why the collision must be an output of the `Computes`-bounded extractor** (**kernel**, [P2]): as a
proposition, "a collision exists" is pigeonhole-true (`exists_isColl`), so such a `final` holds for
every verifier (`final_prop_vacuous`); as an output alone it is still not enough, since accept-all
with a `Classical.choose` extractor is knowledge-sound at error 0 with no call (`acceptAll_choice`),
where v3 needed an open BLAKE2s fact (`acceptAll_kstate_iff`). So the content rests on `Computes`: a
constant `coll x y` extractor certifies accept-all exactly when `IsColl x y` (`acceptAll_iff`), which
nobody can exhibit; liveness checks the two strings of any `.coll` output ([A2] M3).

**An honest node's `final`** (paper, [W2] §A.4): the node SNARK's lemma decodes from `L` (issue #7) the
child proofs and lists `xsᵢ'` with `listHash xsᵢ' = hᵢ` and accepting runs; `attest hᵢ = true` gives
`cert xsᵢ ∈ L` with that hash; equal lists give `accL V L cᵢ πᵢ` (by `Valid` and lifting), unequal
ones a `.coll`. **Kernel scope** (report review M2): `attState`, `calls_node`, `att_W1` give one
`attest` call and the child's potential and error for a probe node with children and list **in the
clear**; a succinct node is the paper obligation. The `coll` branch never fires on a concrete log.

### 4.5 Completeness over honest contexts

```lean
/-- "Run `ctx`; if its result is in the relation on the log so far, run the honest prover and the
verifier" fails: steps as `failProb`; at `ret (c, w)` on `L`, `if R L c w then failProb (…) L else 0`,
with `… = (P c w).bind (V c)`. -/
noncomputable def failCtx (R : Log → Digest → Wit → Prop) (P) (V) : OProg (Digest × Wit) → Log → ℝ≥0
-- `failProb` gains:  attest h k   ↦ failProb (k (L.attested h)) L
--   certify xs k ↦ if Valid L xs then failProb (k true) (L ++ [.cert xs]) else failProb (k false) L
/-- The honest contexts of `P`: a leaf witness, or two honest contexts, `P` on each result, and the
node statement of the two proofs. -/
inductive Honest (P : Digest → Wit → OProg Proof) : OProg (Digest × Wit) → Prop
  | leaf (s : Digest) (n : ℕ) : n ≤ chainCap → Honest P (.ret (leafStmt (chainEnd s n) n, .leaf s n))
  | node (x y : OProg (Digest × Wit)) : Honest P x → Honest P y →
      Honest P (x.bind fun (c₁, w₁) => y.bind fun (c₂, w₂) => (P c₁ w₁).bind fun π₁ =>
        (P c₂ w₂).bind fun π₂ => .ret (nodeStmt c₁ c₂, .node c₁ c₂ π₁ π₂))
def CompleteWithError (R) (P) (V) (δ : ℝ≥0) : Prop :=
  ∀ ctx, Honest P ctx → failCtx R P V ctx [] ≤ δ
```

**Why the game.** The rules worktree's `∀ c w, R c w → failProb ((P c w).bind (V c)) [] ≤ δ` takes
`R c w` outside the lazily sampled game, meaningless for a log-dependent relation ([A1] m2); an
arbitrary starting log is unsatisfiable for every Fiat–Shamir design, and from the empty log the node
clause is empty ([W2] M10). [W2] §A.5's context form, a program producing the statement and witness
against the same oracle, repairs both.

**Why honest contexts** ([DREVIEW] M1, its fix (a)). An unrestricted context can run `P` itself on
many candidate statements (repeated queries are answered from the record) and return one where the
real run fails: for a design failing with probability `δ' > 0` per statement, as a grinding prover
does, `N` candidates fail with probability about `min(1, N·δ')`, so only `δ' = 0` would qualify,
against V3-S2R-A2's purpose. An honest context has no choice to make: its leaves are fixed witnesses
and its shape is the honest tree prover's, as run by the harness's `tree` mode and column R's node
mode. **`δ` bounds each honest prover run**, since `failCtx` counts only the last run of a context
whose children are in the relation, as `completenessCap` does in V3-S2R; a 511-run tree fails with
probability at most `511·δ ≤ 2^-119` (A1 m8). **Given up**: completeness for node witnesses whose
accepted children `P` did not produce, which only the lift's caveat used (§3.3). **Rejected**: fix
(b), a per-query charge `∀ ctx nq, DepthLE ctx nq → failCtx … ≤ (nq + 1)·δ`, which changes the cap's
meaning and asks every submitter for an adaptive completeness proof. Cost: about ten trusted lines for
`failCtx` ([W2] §A.5), six for `Honest`; under R3 the leaf constructor first queries the chain.
**Evidence**: `attV_complete` (**kernel**, one node) with `runLog_append_of_clean` is the inductive
step of the Library lemma R1 writes (RO-3); no probe proves it for a whole tree.

### 4.6 Composition and the error bound

```lean
def treeExtract : Digest → Proof → Log → List Digest → Option (List Digest ⊕ List UInt8 × List UInt8)
-- WF L → μ L < 1 → root accepted on L → the walk returns the starts, with
-- ∀ i, cs[i] = leafStmt (chainEnd starts[i] n) n, or a pair x ≠ y with one BLAKE2s digest
```

**Meaning** ([W2] §A.6, Library). A computable walk over the harness's tree `cs`, so it terminates (a
cyclic extracted proof needs a BLAKE2s fixed point and surfaces as a collision against `cs`). At a
harness node the extracted children equal the harness's or yield the two 65-byte preimages; at a
harness leaf `.leaf s n'` has `chainEnd s n' = h* ∧ n' = n` or yields a leaf-tag collision; an
extracted node at a harness leaf is a cross-tag collision. The walk *returns* the pair; "… or a
collision exists" would be pigeonhole-trivial ([W2] M5). **Error.** By the paper theorem with `cert`
moves, the root is accepted while `μ L ≥ 1` with probability at most `Q·ε`, `Q` counting every fresh
query of the evaluation; for the ranked tree `Q ≈ 2^26–2^28` (estimate), inside `logCap = 2^96` and
the efficient-extraction domain of about `2^61` entries, so at `ε = 2^-128` the bound is about
`2^-100`, **with no factor per level**. v3 §5.4's first item leaves the unclaimed list; v3 §5.3's "it
does not enforce recursion" stays (§7.2). **Hidden conditions** ([T1] §5.2): an explicit depth (the
harness's tree), and a `nodeStmt`/`leafStmt` collision giving *a* witness, which `treeExtract` turns
into a returned collision. The tape is the whole evaluation's log, tens of gigabytes at ranked size
(71 GB of queries for spartan-chain's leaves alone, C1 §5.3, estimate); the liveness smoke at
`r = 1, n = 16` stays small ([W2] M6).

**Evidence** (§13.1). P1's `compose`, `compose_flat`, `paper_tree` (no `cert` events) and P2's
`compose_all`, `compose_blake2s`, `Paper.paper`, `Paper.paper_tree` (every depth from one well-formed
log or a returned `IsColl` pair; at most `nq·ε` for `nq` queries and `nc` certifications,
`nq + nc ≤ logCap`) are **kernel** for every attested knowledge state; P2 does not port
`compose_flat`. This is CGSY24's Thm 5.1 (Chiesa–Guan–Samocha–Yogev) in the counting form.

### 4.7 Submission and Certificate

```lean
structure Submission where
  V    : Digest → Proof → OProg Bool        -- queries and attests; a `certify` makes it reject
  P    : Digest → Wit → OProg Proof         -- queries and certifies
  E    : Digest → Proof → Log → Option Out  -- was `Option Wit`
  ext  : XProg
  ε    : ℝ≥0
  δ    : ℝ≥0                                -- per honest prover run (§4.5)
  qV   : ℕ                                  -- bounds `query` and `attest` calls
  fuel : ℕ → ℕ
structure Certificate (S : Submission) : Prop where
  secure   : KS S.RelL S.V S.E S.ε S.qV
  complete : CompleteWithError S.RelL S.P S.V S.δ   -- honest contexts
  computes : Computes S.ext S.E S.fuel              -- `decodeOut`; tape over `Ev`
  cap      : S.ε ≤ errorCap ∧ S.δ ≤ completenessCap ∧ S.qV ≤ 2^16 ∧   -- `2^13` under R3 (§6.3)
             (∀ t, S.fuel t ≤ B t) ∧ S.ext.body.size ≤ progCap
-- deleted: `Submission.Vb`, `blake2sOracle`; `tagRO` is no longer a relation constant
```

There is no instantiated verifier: the harness runs `V` against the service. `Computes` keeps its
shape with `decodeOut`; `extractorInput` serialises `Ev` logs, with V3-S2R-A9's domain condition over
the queries of `ans` events and certified items. A node proof carries the SNARK proof and the two
attested hashes, about +64 B ([W2] m5). The honest node prover certifies each child's list from
answers it holds and proves in-circuit that the child is accepted reading it and that it hashes to
`hᵢ`; `V` attests (RR-3) and verifies the SNARK. The witness-sending baseline is re-certified with no
calls and `μ := 0` (`ws_ksa`, **kernel**). Deleted with `Vb`: the v3 §6.7 rule, the intake review for
recognition, the need for F2's typed interface. **Trusted delta** ([W2] §A.8, estimate, from 288; now
292): `Oracle.lean` +31 (items, events, constructors, `answer`, `attested`, `Valid` and three caps,
`encItem`, `listHash`), `Relation.lean` +1, `Security.lean` +16 (`cert`, `Out`, `Sound`, `failCtx`),
`Extractor.lean` +6, `Certificate.lean` ±0: **+53, to about 345 of 500**, plus a few lines each for
`WF` and `Honest` (this document's additions to W2's count).

### 4.8 The harness service

**State per timed run** (one `PROVER tree` with its root, sample, canary and root-step checks): `k`,
32 bytes from the runner's `os.urandom`, never written, destroyed at reset; `S`, a hash set of
attested digests, initially empty. Both are reset before every repeat. The caps are `Valid`'s.

| Call | The service does | Returns | Cap per run |
|---|---|---|---|
| `query(q)` | `PRF_k(q)`: BLAKE2s-256 in **keyed mode**, key block cached | the answer | `queryCap`; no count cap |
| `certify(xs)` | refuse unless `xs` meets `listItemCap`, `listByteCap`, `queryCap`; `ans q a`: check `a = PRF_k(q)`; `att h`: check `h ∈ S`; if all pass, add `listHash xs` to `S`; atomic | a bit | `≤ 2^20` calls |
| `attest(h)` | `h ∈ S` | a bit | counted in `qV` |

- **Keyed mode, not `BLAKE2s(k ‖ q)`**: the parameter block makes `PRF_k` and public BLAKE2s differ on
  every input; concatenation invites length-extension mistakes and, under W5, makes each secret answer
  a public-channel value at release ([A1] m6, [A2] m11, report review m8).
- **Recursive certification is forced** ([W2] §A.1): a child's `V` attests its children's lists, so its
  list holds `att` items someone must check. Flat, only the root can, attesting all `2^(r+1) − 1`
  hashes (16,352 B and 511 calls at `r = 8`); recursive, it makes RR-3's two calls or one.
- **It never verifies a proof**: a `certify(c, π)` running `V` would make the node proof two hashes and
  the organiser the prover of record ([W2] M9). `certify` returns a bit, not a digest, recomputes the
  PRF and keeps no table.
- **Lifecycle** ([W2] M2). Fresh `k` and `S` per run stop repeat 2 from submitting repeat 1's hashes;
  the root, sample, canary and column-R checks run against the **same** state as the tree, before the
  reset. Nothing persists across evaluations or submitters; the key is never logged.
- **Isolation** ([W2] M3). A prover holding `k` could carry it for a two-point check of `PRF_k`,
  certifiable by counting (F2 §6), so `k` lives in a process the sandbox cannot read: own uid, no
  ptrace, seccomp, no shared memory beyond the rings; `attest` timing reveals only membership (m4).
- **Placement** ([W2] M4). Outside the prover's cgroup the service is a free co-processor of
  `2^33`–`2^35` compressions per tree, so its workers run on the prover's cpuset and CPU cgroup
  (memory in a separate small cgroup), as does `certify`'s 4.7–14.5 M-compression re-evaluation (C1).

**Transport.** With the key hidden, every prover oracle call, Merkle hashes included, is IPC. On the
32-vCPU VM with 65-byte calls (C1 §5.2, **measured**) a futex round trip per call costs 82× in-process
(37 µs), a spinning one 2.3×, 256 per spinning round trip 1.22×, at 10–12.5 M calls/s machine-wide
(overheads in §7.3). The fix is a double-buffered ring per prover thread, flushes of at least `2^10`
calls and a SIMD multi-buffer BLAKE2s (up to 5× on hashing-bound rows), and beyond D4, W5.

**Failure semantics** ([W2] M8, M11). The service is the first runtime component whose bug would be
accept-all (one wrong answer certified, an `attest` true for an uncertified hash, a reset forgetting
`S`, a key reused after a crash, a `certify`/`attest` race), so it is a small program (about 300–400
lines of Rust, estimate) with the Lean `Valid`, `listHash`, `attested` as specification and test
vectors, `certify` atomic, no persistence, and a watchdog that kills the run on a crash. **A refused
call aborts the verification as a reject**, never returning a value `V` can branch on. **A PRF, not
a random table** (C1 §5.3, estimate): a table needs 71 GB of queries for the leaves alone (17–69 GB
with fingerprints), against the VM's 62 GB. Liveness reads the service's authentic log ([W2] m7); the
badge `verify` gains a service client (trusted badge code).

### 4.9 The deployment argument

**The hybrid** (paper, [W2] §A.7, [L1] §11). The theorem averages over a random function; deployment
uses `PRF_k`, `k` secret from the prover, from `V`'s author (`V` is frozen first) and from `V`. The bad
event, "the root is accepted and `treeExtract` returns neither the starts nor a collision", is decided
by a polynomial-time tester with oracle access (`E` is step-bounded; `Sound` costs `2^20` hashes for a
leaf, a run of `V` on the log for a node, two hashes for a collision), so `Pr_deploy[bad] ≤
Pr_random[bad] + Adv^PRF(D)`, `D` running the whole evaluation. CGH needs a public seed (CGH §4):
under a secret key, recognising the oracle distinguishes `PRF_k` from random. **Fine print**
(report review m15): (1) `D` runs the evaluation and the extractor within `B t`, polynomial: about
`2^58` steps at ranked size (a `2^33`-word tape, 511 extractions) and at most about `2^28` queries,
far below any keyed-BLAKE2s margin; (2) the steps to a random function and randomised adversaries are
on paper, as in v3; (3) the service is assumed correct (tested, not proved); (4) the deployed
whole-tree bound is about `2^-100` at `ε = 2^-128`, since `Q` counts every query of the evaluation.

**The other channels.** The attest channel needs no assumption: `S` and `Log.attested` agree by
construction. The collision channel is BLAKE2s collision resistance, v3's item 4, now also for list
hashes and *constructive*: one fixed unkeyed function's collision resistance has no challenger, and
handing over the pair gives it content (report review m9). **What it kills** (paper, [W2] M11, [W1]
§11.2): every F2 disguise compares an oracle answer with a value `V` holds about the instantiation,
and none exists before `k` is sampled; the public-hash Fiat–Shamir counterexamples (Goldwasser–Kalai,
BBHMR19, KRS25, Fenzi 2026) do not apply to a secret PRF; the liveness mirror closes by the same
reduction. **What it does not give** ([T1] §6.3, report review m18): a NARG (the root check is online
and stateful, so proofs are not transferable until key release); records certify the attested
deployment. **Assumed**: PRF security of keyed BLAKE2s; constructive collision resistance of
BLAKE2s-256; the service implements §4.8; instance and key freshness; the paper steps of (2).

### 4.10 W4: published log and key release

(Paper, [W1] §6, [A2] m8, m10, [A1] M9.) **Publish** a per-evaluation, never global, append-only log
of certified list hashes (under W5, of closed sessions' hashes). **Read**: the root check may read a
`Published h` predicate, of `attested`'s shape, from that file instead of calling `attest`.
**Release** `k` after the record is frozen, so anyone recomputes every list and re-runs the root check
offline (under D4+ the record carries `(starts, k, treeRoot, proof)`, §6.4). **Rules**: magic proofs
carrying `k` exist only after release, so post-release proofs are not evidence in the challenge
period or DoS column, and challenges run against the service or on the frozen record; until release
the competition is designated-verifier and the record states its release date; the next evaluation's
key is independent (a reused key is a published oracle); no answer is published before release. W4
buys D3's third-party verifiability at D4's cost ([W2] m8); the theorem is unchanged.

---

## 5. Optional stage R4: W5, the channel split

**Conclusion first.** W5 attests only the about 500 Fiat–Shamir answers per proof and hashes Merkle
trees with public BLAKE2s: the node pays a real recursion step plus 0.5–2% (estimate), service traffic
drops about a thousandfold, and every hashing trick of a real recursion is rewarded. The price is an
unfalsifiable extractability heuristic, weaker than v3's random-oracle heuristic and not exploitable
by `V`, and a second escape. Adopted only with RU-1's consent.

### 5.1 The model

Of spartan-chain's 5,156 queries about 4,700 are Merkle-path hashes, needing only *binding*, and
400–500 are Fiat–Shamir squeezes, needing *unpredictability* ([W1] §7): only the latter go secret.

```lean
inductive Entry | sec (q : List UInt8) (a : Digest) | pub (m : List UInt8) (a : Digest)
def pubConsistent (L : List Entry) : Prop := ∀ m a, Entry.pub m a ∈ L → a = blake2sDigest m
-- `TProg`: programs with `sec q` and `pub m` calls; `runLog` answers both from the log, else `none`
inductive Esc                -- two logged inputs with one output; `a` used in entry `j`, produced later
  | col (m m' : List UInt8) (a : Digest) | late (j : ℕ) (m : List UInt8) (a : Digest)
structure KState2 (R) (V) (E : Digest → Pf → List Entry → Option (W ⊕ Esc)) (ε : ℝ≥0) where
  μ       : List Entry → ℝ≥0
  empty   : μ [] = 0
  step    : ∀ L q, pubConsistent L → secCount L < logCap → μ L < 1 → q ∉ secQueries L →
              ∑ a : Digest, μ (L ++ [.sec q a]) ≤ (μ L + ε) * 2 ^ 256
  pubStep : ∀ L m a, pubConsistent (L ++ [.pub m a]) → μ (L ++ [.pub m a]) ≤ μ L
  final   : ∀ L c π, pubConsistent L → secCount L ≤ logCap → μ L < 1 →
              (V c π).runLog L = some true → ∃ o, E c π L = some o ∧ SoundW R c L o
```

This is P3's model (`TwoChannel/Model.lean`) for mode `colLate`, the mode argument dropped and P3's
`Valid mode R c L o` written `SoundW` to keep it apart from §4.2's `Valid`. In the contract the escapes
become constructive outputs (§4.4, [A2] M3), child challenge lists are certified with `att` items as
in D4, and `logCap` and `qV` count `sec` entries only ([A2] m2; about 500, a cap of `2^12` would do).

### 5.2 Three breaks of the first model, and their fixes

[A2] (paper) found [W1]'s first model broken in three places; [P3] (kernel, §5.3) confirmed each fix.
(1) **The stripped log** (A2 M1): a `V` that hashes privately still accepts the honest log minus its
`pub` entries, leaving nothing to decode; fix: `V` *queries* the public channel, answered from the
log. (2) **Late preimages** (A2 M2): an adversary squeezes on a root it merely wrote down and logs the
paths afterwards, free on a deterministic channel; fix: the late-preimage escape (P3), or an ordering
hypothesis (A2's `pubOrdered`). (3) **The collision clause** (A2 M3) must be D4's constructive output,
since the tree theorem's collisions are not in the log. **An honest prover may hash late** (A2
postscript, report review m14), as column R's node mode recomputing child statements does, so
relation-tagged preimages (`tagChain`, `tagLeaf`, `tagNode`) are exempt from the ordering condition,
or a liveness rule rejects escape outputs on honest proofs.

### 5.3 Kernel results for the corrected model, and their scope

`TwoChannel/` ([P3]), a two-leaf Merkle toy with one squeeze. `pubStep` holds **with equality** for
any potential pricing secret answers against the prior log (`ofHist_pub`, `merkleState_pubStep`).
Break (1): the private-hashing verifier has no knowledge state for the natural extractor at any
`ε < 1` (`pure_no_kstate`), and every other extractor inverts the Merkle root map from a squeeze-only
log (`pure_extractor_inverts`). Break (2): "witness or collision" has none for the natural extractor
at any `ε < 1`, for two good leaves with distinct hashes, neither equal to the root (`col_no_kstate`),
and every other extractor inverts BLAKE2s (`col_extractor_inverts`). With the late
escape `merkleState` certifies the toy at `ε = 1/2`, tight for the natural extractor
(`merkle_eps_ge`); honest proofs are extracted, not escaped, unless a leaf hash equals the root
(`honest_extracts`; `honest_extracts_blake2s` for two concrete leaves). The public-channel backdoor has
no state for its natural extractor at any error (`bd_no_kstate`) and every extractor inverts the root
map (`bd_extractor_inverts`); on the secret channel it *is* certified at `errorCap` (`bdSecW_kstate`).
**Not built**: the two-channel paper theorem (paper: `PaperTheorem` rerun with `pubStep` as a
zero-cost step), composition, child-list attestation, multi-squeeze verifiers (WHIR-class openings
need `Controls/Potential.lean`'s product-form potential).

### 5.4 Discipline, assumptions, and why the gap does not reopen CGH

- **Challenges are bit-slices of secret answers** ([A2] m6): seed expansion by local BLAKE2s
  (`pos_i = BLAKE2s(a ‖ i)`) needs an unprovable bound in `step`; an honest `V` takes about 13 answers
  for 190 positions and about 100 for field challenges, lists of 100–150 items.
- **Session hygiene** ([A2] M5). Grinding, retries and 32 threads fill a raw session with `2^g` times
  the final transcript, so the prover replays the final transcript in a fresh session and closes that
  one; certification stays recursive. Commitments are full finalised BLAKE2s off the relation tags;
  truncated labels and compression-only trees are uncertifiable (m1).
- **Assumptions.** PRF security, constructive collision resistance, and an **extractability
  heuristic**: whoever outputs a BLAKE2s digest knows a preimage. Its formal version, preimage
  awareness (Dodis–Ristenpart–Shrimpton 2009), is relative to an ideal compression function, and
  Bitansky–Canetti–Paneth–Rosen (STOC 2014), assuming indistinguishability obfuscation, rule out
  extractable one-way functions with arbitrary auxiliary input: it is not falsifiable ([A2] M4). It is
  strictly weaker than v3's "BLAKE2s is a random oracle", dropping the unpredictability CGH attacks;
  D4 all-oracle needs none, its service log *being* the trace. The bound becomes `(Q_sec + qV)·ε +
  Adv_PRF + Pr[E outputs a collision] + Pr[the trace has a late preimage]`, the last term the
  heuristic, tested on the native prover's emitted log at liveness size. The escape is idealised (P3):
  a non-uniform adversary hard-coding one pair `(y, BLAKE2s y)` triggers it at no cost; it cannot forge
  a commitment to unknown data, but the bound gains a term only the heuristic controls.
- **No CGH** ([A2] §1.4, paper). The backdoor needs model and deployment to disagree about an answer
  `V` sees: on the public channel they agree by construction, and on the secret one `V` cannot
  predict. A certified `V` accepting below potential 1 means the logged leaves decode to a witness for
  a *fresh* statement, so exploiting the gap means breaking the SNARK's soundness under `PRF_k`.

**Cost** (§7.3). Trusted base +80–120 lines over v3's contract, D4's shared machinery included
([A2] §7, estimate): about 372–412 of 500 from today's 292. A2 found no strategy that games W5
without gaming D4 and v3 identically.

---

## 6. Optional stage R3: D4+, the oracle-chain leaf

**Conclusion first.** Attestation removes the reason the leaf stayed concrete (§3.4). With the leaf
chain computed through the oracle and certified, no root verifier can recompute the chain digests, so
#6(a) closes by the certified caps (paper, [A3] §3; no Lean theorem) and `T_V` becomes a loose
liveness cap. #6(b) does not close.

### 6.1 The leaf clause

```lean
def chainO (L : Log) (s : Digest) : ℕ → Option Digest          -- the chain read from the log
  | 0     => some s
  | i + 1 => (chainO L s i).bind fun d => L.answer (chainQuery d)   -- `chainQuery d = tagChain ‖ d`
-- leaf clause:  c, .leaf s n  ↦  n ≤ chainCap ∧ ∃ h, chainO L s n = some h ∧ c = leafStmt h n
```

The clause is `Option`-valued on purpose ([A3] §1): a leaf whose chain is not in the log is not in the
relation, so `V` must reject it, which it learns only through `attest`. The honest leaf prover
queries the chain (`n` fresh queries; §4.5's leaf constructor does so first), certifies the `n`-item
list and proves in-circuit that it hashes to `h`, chains from `s` to `h_end` in `n` steps, and that
`c = leafStmt h_end n`; `V` attests `h` and checks the SNARK; `E` decodes the list (issue #7, now at
leaves). The runner builds the instance through the service, never holding `k`. Soundness is
`attState`'s argument with `n` lookups; the kernel work is a `chainO`-from-`Valid` lemma (estimate).

### 6.2 What it closes, and what it does not

**#6(a), by the certified caps** (paper, [A3] §3, report review m16). A root verifier sees at most
`proofCap` bytes and `qV` answers and attestation bits, and chain digests are PRF outputs, so it
recovers at most `(proofCap + 32·qV)/32 ≈ 2^15 + qV` of the `2^22` digests (about `2^-7`, a margin of
about `2^7`); the rest needs a SNARK, raw transcript buying at most about `2^15` local compressions
(about 5 ms, estimate). `T_V` only stops a merely slow verifier, at seconds; the CPU-time rule, its
calibration and the step-count upgrade (O-18) become unnecessary. **Not #6(b)** (paper, [A3] M1):
T1's flat lift survives as "proof of parent", one flat SNARK over a level-`j` subtree's attested
lists accepted as the proof of *every* statement below it, straight-line, complete and within every
cap; flattening to `j ≈ 3–4` stays 2.3–7.5× cheaper than full recursion at the ranked shape
(estimate) and invisible to a per-level `T_V`.

### 6.3 Parameter conditions

(Paper and estimate, [A3] M2, m5.) A level-`j` statement has three witness-sending forms: re-query the
`2^j` chains (`2^j·n` queries), carry each compact transcript (`32(n+1)` bytes, one `attest`), or a
hybrid. At `n = 2^14` one compact list is 524,320 B and two 1,048,640 B, 64 bytes over `proofCap`; at
[W2] §D's `qV ≤ n` a hybrid node exists at level 1 (one chain re-queried, the sibling's list carried),
at the contract's `2^16` at level 2.
**Fix: `qV ≤ 2^13`** (`2^12` under W5), which excludes the hybrid everywhere and fits spartan-chain at
the ranked shape (5,156 queries) and at the long shape (7,774 at `n = 2^20`, **measured**, A3 m5),
leaving 418 for attests there. The certificate has one `qV` for every `n ≤ chainCap`, so a `V` whose
only leaf branch re-queries the chain is incomplete for `n > qV` (A3 m5): leaves are SNARKs or compact
lists, never re-queried, and a list leaf is harmless, its hashing moving into the level-1 circuit. The
shape invariant is **`proofCap < 64·n_bench`**: raising `proofCap` for node proofs, as issue #8
wishes (2 MiB admits the compact form at level 1, 4 MiB at level 2), reopens the hybrid unless
`n_bench` rises with it.

### 6.4 Engineering and the record

- **The `chain` call** ([A3] M3). Each step's query is the previous answer: `n` dependent round trips,
  17 ms (spinning) to 0.61 s (futex) per `2^14` leaf, 1.09 s to 39 s per `2^20` leaf (**measured**
  round trips, estimated products). `chain(s, n)` runs the steps in-process (0.25 µs a step: 4 ms per
  `2^14` chain, about 30 ms per ranked tree over 24 threads), is `n` queries in the model, is charged
  to the prover's cgroup, and builds the runner's instance before the clock.
- **Key-dependent instances** ([A3] M4). `treeRoot` depends on `k`, so without W4 nobody can later
  check it is a tree of chains (§4.10). Repeat rule (RU-6): A3 recommends fresh `k` and starts per
  repeat, `S` reset either way.
- **Leaf cost** ([A3] m1, m2, estimate): a 74-byte chain item streamed through one BLAKE2s gives
  `1.16·n` compressions, not W2's `1.6·n`; a compact list `0x42 ‖ s ‖ d₁ ‖ … ‖ d_n` gives `0.5·n`. The
  leaf now proves a BLAKE2s transcript of a PRF chain.
- **Nested lists** ([A3] m4): a long-shape leaf list (`2^20` items, 77.6 MB generic, 33.6 MB compact)
  exceeds `Valid`'s caps; 16 recursively certified sublists of `2^16` fit. Length separates a 32-byte
  squeeze input from a 33-byte chain query (m7). Under W5 the chain is on the secret channel: `2^22`
  calls per ranked tree, 17× W5's traffic, about 0.4 s of batched service time (m6).

**Contract and library** ([A3] §5): about +6 trusted lines (estimate) for `chainO`, the `Option`
clause, the encoding and `Honest`'s chain leaf; the `chainO`-from-`Valid` lemma, `treeExtract`'s leaf
case; controls: a list leaf extracted, an uncertified chain rejected, two compact lists over
`proofCap`. D4+ needs its own attack pass ([W2] §D).

---

## 7. Benchmark and scoring under the design

### 7.1 What stays, and `T_V`

Board T (whole-tree makespan over fresh leaves), column R and the DoS column stay; each of the three
timed repeats gets a fresh key and `S` (under D4+ fresh starts too). **Without D4+** the CPU-time rule
of #6 (V3-S2R-A7's proposal) still separates the trivial root (37–43 ms threaded, 0.19–0.69 s on one
core, **measured**/estimate) from a real recursive root (8–30 ms with carry-less multiply, estimate;
0.5 s on the development VM): about 2–2.5× each side at the ranked shape, about 5× at the long shape
(C1 §2.3, estimate). It counts the service's PRF time for the verifier's about `10^4` queries (about
1.5 ms, §4.8's placement) and is calibrated on the reference machine. **With D4+** it is a liveness cap.

### 7.2 #6(b) and the shape

Flattening to `j ≈ 3–4` is certifiable under every design studied (§6.2, [W2] M7). Recursion costs
2.5–12.6× the work of proving the same compressions flat at the ranked shape, about 1.17× at the long
shape, where a node costs 0.18 leaf units and flattening to `j = 2` saves under 15% (C1 §2.2, A3 M1,
estimate); spartan-chain's 3.95 GB per `2^14`-step leaf scales to about 1 TB at level 8, so memory
holds `j ≤ 4` under the 96 GB cgroup. Recommendation (RR-13, RU-4): fewer, longer leaves, or an open
statement that flattening below `j ≈ 4` is allowed. The long shape keeps D4+'s invariant, needs nested
certification (§6.4) and leaves the baseline leaf 418 queries under `qV ≤ 2^13` (§6.3).

### 7.3 Costs

| Quantity | Value | Tag, source |
|---|---|---|
| D4 node in-circuit vs real public-hash recursion | 1.09× for a spartan-chain child (28.3k vs 25.9k compressions); 0.79–1.56× per query type | estimate, C1 §4.1 |
| W5 node; D3 per child; D4+ leaf | +0.5% (the child's 25.5k Merkle and absorb compressions plus a 476-item list), +0.1% bit-sliced; +145 to +1,059 compressions (0.5–12%); 1.16× v3's chain (0.5× compact) | estimate, A2 §6, C1 §4.2, A3 m1 |
| proof size | about +64 B per node | W2 m5 |
| D4 traffic | 262,614 calls and 278 MB per spartan-chain leaf, 6.7·10^7–2.7·10^8 calls per tree; +0.3–1.2% of leaf time (spartan-chain, Merkle phase 0.1 s of 7.7 s), +30–110% (Flock-class, naive service) | estimate from **measured**, C1 §5 |
| W5 traffic | about 2.5·10^5 calls per tree; latency of about 476 sequential round trips per leaf, 1.4% (spinning, about 1 µs) to 52% (futex) of a 34 ms Flock-class leaf, 13% at worst bit-sliced; spinning ring, one thread | estimate, A2 m9 |
| `certify` re-evaluation; root's online calls | 4.7–14.5 M compressions per tree (0.07–0.22 s); 3–12 ms batched, about 400 sequential Fiat–Shamir calls 0.4 ms spinning or 15 ms on futexes | estimate, C1 §4.3, §5.4 |

---

## 8. Incentive analysis

Under D4 (R1–R2) unless a row says otherwise; ranked shape.

| Strategy | Certifiable? | What stops it | Evidence |
|---|---|---|---|
| Witness-sending (no proving) | yes, `μ := 0`, no service | without D4+ only the CPU-time `T_V` rule (#6(a)); with D4+ `qV` and `proofCap` (`2^22` queries or 128 MB) | kernel `ws_ksRel`, `ws_ksa`; paper A3 |
| Concatenation of leaf SNARKs | yes | `qV = 256 · 5,156 > 2^16` and `proofCap`, as in v3 | kernel `concatState` |
| Flat lift, starts in the clear | yes, at `V₀`'s error and queries | library format: `proofCap` on children (`≤ 2^14` leaves); with D4+ excluded above level 1–2 | kernel `lift`, `lift_runner_ws`; paper A3 |
| Proof of parent; flattening below `j` | yes, within every cap | nothing in the theorem; memory (`j ≈ 3–4`) and the shape (§7.2) | paper A3 M1; estimate |
| Honest recursion | yes, composable; two `attest` calls per node, or one | the intended winner; loses to flattening at `r = 8`, about ties at the long shape | kernel `attState` (children in the clear); paper |
| Backdoor and every F2 disguise; liveness mirror | yes, in the model | no value about `PRF_k` to compare with: fires with probability at most `Adv_PRF + 2^-256` per comparison; the mirror harms only its author | kernel `Backdoor.backdoor`; paper W2 M11, W1 §7.3 |
| Key in the proof; `V` accepting on `attest` alone or on an unattested hash; a certifying `V` | two-point check certifiable; only via accept-all; no | `k` in a process the prover never reads; `Computes` with a real extractor; `certify` reads `none` | paper W2 M3, m3; §4.2 |
| Grinding | yes: `δ` per honest prover run (§4.5) | prover time; tries are independent batched queries; W5 replays the final transcript | paper A1 m8, A2 m7 |
| Replay across repeats, evaluations or submitters; key reuse, published answers, post-release magic proofs | —; yes, after release | fresh `k`, `S` and starts, checks before the reset, a per-evaluation log; independent keys, nothing published before release, post-release proofs not evidence | paper W2 M2, A1 M9, A2 m8, m10 |
| W5: Merkle hashing through `sec`; challenges through `pub`; seed expansion | yes (harmless, slower); no; not in practice | `final` on every ordered log; `step` unprovable for BLAKE2s expansion | paper A2 §6, m4, m6 |
| D4+: hybrid witness-sending at level 1–2; log-scanning extractor | at `qV ≤ n` or `2^16`; no | `qV ≤ 2^13` and `proofCap < 64·n`; `final` ranges over logs where no child proof was made | paper A3 M2, §4 |

Deferral and lazy parents (§3.2), collision laundering (§4.4), the service as co-processor or
time-burner (§4.8), session mixing (harmless: the service hashes only what it returned in a session,
[W1] §6) and precomputation (fresh starts; under D4+ a key not yet sampled, [A3] m8) are covered where
cited. On board T, D4 alone changes no incentive, only what a record certifies ([W2] M7).

---

## 9. Problems found and their fixes

| Id | Problem | Fix | Evidence | Where |
|---|---|---|---|---|
| A1 M1, M2 | relativized `KS` met at node error 0; re-ask every descendant query | none inside `KS`; leave the pure ROM: attestation | kernel `ws_ksRel`, `concatState`, `reask`; paper | §3.2, §3.3, RR-3 |
| A1 M3–M7, M10 | gameable charge; wrong statistic; no separating cap; a chain-prover winner | no charge; list hash in-circuit; board T; the shape | paper; estimate | §3.1, §7 |
| A1 M8, M9 | public oracle; key reuse, designated-verifier records, RPC in the clock | secret service; fresh keys; W4; rings | kernel `Backdoor.backdoor`; paper | §4.8–§4.10 |
| A1 m2, m6; W2 M10; A2 m11 | `CompleteWithError` ill-typed; arbitrary starting log; `BLAKE2s(k ‖ q)` | context form; keyed mode | paper | §4.5, §4.8 |
| W2 M1, M2 | encoding ambiguity; replay through service state | prefix-free codes, bound in `Valid`, bounded `IsColl`; fresh `k`, `S`, checks before reset | kernel `encList_inj`, `hashList_not_coll`; paper | §4.3, §4.8 |
| W2 M3, M4 | key hidden, so all traffic is IPC; whose cores | separate process; prover's cgroup; rings; W5 | **measured** C1 §5.2 | §4.8, §5 |
| W2 M5, M6, M7 | vacuous collision disjunct, deposit service; #7 plus a list comparison; #6 unchanged | output under `Computes`, `treeExtract` returns the pair; paper obligation; CPU rule, D4+, shape | kernel `final_prop_vacuous`, `acceptAll_choice`; paper; estimate | §4.4, §4.6, §7 |
| W2 M8, M9, M11 | accept-all-class runtime; no verification; refused calls | Lean test vectors; atomic `certify`; watchdog; abort as reject | paper | §4.8 |
| A2 M1, M2 | stripped log; late preimages | `V` queries `pub`; late escape, tag exemption | kernel `pure_no_kstate`, `col_no_kstate`, `merkleState` (natural extractor, `ε < 1`) | §5.2, §5.3 |
| A2 M3, M4 | in-log collision; heuristic called falsifiable | constructive output; say so; D4 fallback | paper (DRS09, BCPR14) | §5.2, §5.4 |
| A2 M5; post. | no `att` items or sessions; honest late hashing | D4's lists; clean replay; tag exemption | paper | §5.2, §5.4 |
| A3 M1 | proof of parent | do not claim #6(b); the shape | paper; estimate | §6.2, §7.2 |
| A3 M2 | `qV ≤ n` admits a level-1 hybrid | `qV ≤ 2^13`; `proofCap < 64·n` | paper; estimate | §6.3 |
| A3 M3, M4, m1, m4 | dependent round trips; key-dependent instances; leaf at 1.16×, not 1.6×; long-shape lists | `chain(s, n)`; W4, fresh `k` and starts; stated; nested lists | **measured** round trips; estimate | §6.4 |
| A3 m5 | one `qV` for every `n`; 7,774 queries at `n = 2^20` | leaves never re-queried; 418-query margin stated | **measured** (A3 m5) | §6.3, §12.2 |
| T1 | `KS` ≠ amenability; no-state-for-every-extractor needs a BLAKE2s fact; hidden conditions; `attest` no uniform query; not a NARG; oracle leaf hopeless in the pure ROM | lift; natural-extractor and `Collides` forms; `treeExtract`; `cert` law; W4; concrete leaf under R1–R2, attested chain under R3 | kernel `lift`, `kstate_of_leaf_surjective`; paper | §3, §4.2, §4.6, §4.9, §6 |
| P2 | trace semantics breaks lifting | lookup semantics, `none` | kernel `runItems_valid` | §4.2 |
| Report review | overclaims, scope, completeness, audit count, units, keyed mode, CR, fine print, D4+ wording, what records certify, line base | as fixed | kernel; paper | §3, §4, §6.2, §10, §13 |
| DREVIEW M1, M2 | unrestricted contexts; uncapped `Valid` | honest contexts; the service caps in `Valid` | paper | §4.5, §4.2 |

---

## 10. Trust statement

**A ranked record means**: the kernel accepted `Certificate` (§4.7) for the rendered challenge, and
the run, against a fresh service state, measured the times with every checked proof verifying. Its
reader trusts v3 §8's items, changed as follows:

> 2. The contract: about 345 code lines (estimate), no theorem, three standard axioms, now with the
>    oracle's events, `Valid` and its caps, the list encoding, the `cert` law and honest contexts.
> 4. BLAKE2s = RFC 7693 and its constructive collision resistance (statement tree and list hashes),
>    and **keyed BLAKE2s is a PRF** against the whole evaluation, replacing "BLAKE2s instantiates the
>    random oracle". Under W5, add §5.4's extractability heuristic.
> 5. Knowledge soundness of the **whole tree** from one log (§4.6), the paper bound with `cert` moves,
>    the paper steps to a random function, and the PRF hybrid (§4.9); v3's composition and O-25
>    clauses are gone. Completeness over honest contexts, `δ` per prover run.
> 6. The badge code, now `V` with its service client, `P` and the contract interpreter.
> 8. Tested, not proved: the runner and **the oracle service** (the first runtime component whose bug
>    would be accept-all), tested against the Lean `Valid`, `listHash`, `attested`; its key lifecycle
>    and placement. Liveness reads the service's own log.
> 9. The reference machine and, without D4+, the `T_V` calibration.
> 10. **New**: the key schedule and release (W4): independent keys, released only after the record is
>     frozen, the release date in the record; until then the organiser is the only verifier.
>
> Items 1, 3 and 7 are unchanged. Not claimed: the native prover's correctness; `E` beyond its budget
> and domain; that a public-hash deployment of a winning design is sound (CGH plus the impossibility
> result); that board T rewards recursion below the memory level (#6(b)).

**Trusted lines** (estimates over 292): D4 +53 (about 345 of 500, plus `WF` and `Honest`), D4+ +6, W5
+80–120 over v3 including D4's shared machinery; and a trusted runtime service of 300–400 Rust lines.

---

## 11. Build order

Stages follow `CLAUDE.md`'s protocol: implement, then adversarial review and golf in parallel, then
the fix pass; the orchestrator records agreed changes in `docs/DESIGN-AMENDMENTS.md` and commits.
Every new trusted definition gets positive and negative controls; `scripts/loc.py` stays under 500.

| Stage | Contract | Harness | Library and controls | Closes |
|---|---|---|---|---|
| **R1** relation | §4.2–§4.5 and §4.7: events, `attest`/`certify`, `Valid` with its caps, `WF`, the encoding, the `cert` law, `Out`/`Sound`, `failCtx`, `Honest`, `decodeOut`, `accL`, `RelL`; `Submission.Vb` deleted, since `OProg.run` has no `attest` case | an interim in-process stub service: `query` by public `blake2sOracle`, `certify`/`attest` from a local set with `Valid`'s checks; O-25 stays open | the paper theorem with `cert` moves; `treeExtract`; lifting; node completeness ⇒ completeness over honest contexts (RO-3); the baseline re-certified (submissions repository); controls: encoding injective and the unbounded counterexample, `Valid`/`WF` both ways including an over-cap list, the `attest`-alone verifier failing with a real extractor, `acceptAll_choice` as a known control, the ported backdoor still certified | the composition heuristic (v3 §5.4 item 1) |
| **R2** deployment | delete `blake2sOracle`, `tagRO` as a relation constant | the keyed, isolated service replacing the stub, with test vectors; the badge client; the lifecycle (start, place, reset per repeat, checks before reset); liveness from the service log; W4; the v3 §6.7 rule and recognition review removed; §4.9 written up | the service's test vectors against the Lean definitions | O-25, the liveness mirror, "BLAKE2s is a random oracle" |
| **R3** D4+ (optional) | `chainO`, the `Option` leaf, `Honest`'s chain leaf, the chain encoding; `qV ≤ 2^13`; `proofCap < 64·n` stated | `chain(s, n)`; the repeat rule; nested lists | `chainO`-from-`Valid`; the leaf case; §6.4's controls; an attack pass | #6(a) by the certified caps (paper); the CPU-time `T_V` rule |
| **R4** W5 (optional, RU-1) | two-channel log; `pub` queries from the log; `pubStep`; constructive escapes with the tag exemption; `logCap`, `qV` over `sec` | sessions with clean replay; a spinning ring; trace checks at liveness size | the two-channel paper theorem; the multi-squeeze potential; the backdoor and private-hashing negatives | traffic (about 1/1000); in-circuit fidelity |

R1 precedes R2; R3 and R4 follow R2 and are compatible ([A3] m6). R1 alone changes the theorem only.

---

## 12. Open items and the user's decisions

### 12.1 Open items

| Id | Item | Status |
|---|---|---|
| RO-1 | **The succinct node** ([W2] §A.4, #7): that a SNARK node decoding `(πᵢ, xsᵢ)` from its committed witness satisfies `final`, decoding from the whole log with a list scan and comparison inside `2^16·t` | paper; kernel only with children in the clear |
| RO-2, RO-4 | Adaptive contexts in completeness; collision outputs against `outCap` | resolved: honest contexts (§4.5) and the service caps in `Valid` (§4.2), [DREVIEW] M1, M2 |
| RO-3 | **Node completeness ⇒ completeness over honest contexts**: one node is proved (`attV_complete`); the induction is the submitter's route to the certificate | Library, R1 |
| RO-5 | `logCap = 2^96` against the efficient-extraction domain of about `2^61` entries (V3-S2R); the ranked `Q ≈ 2^26–2^28` is inside both | open in v3 (O-21) |
| RO-6 | #6(b) (RU-4); #8, proof sizes, with D4+'s invariant constraining any raise of `proofCap` | open in v3 |
| RO-7 | W5's unbuilt parts: the two-channel paper theorem, composition, sessions with `att` items, multi-squeeze verifiers | R4 |
| RO-8, RO-9 | Measurements: leanVM's recursion verify on the reference machine before fixing `T_V`, and a double-buffered SIMD service (C1 §7). Later options: D3 if offline verification *during* an evaluation is wanted; an accumulation-shaped node relation after W5 ([W1] §9), which v3 as built does not express (V3-S2R-A6) | to measure; not proposed |

### 12.2 The user's decisions

- **RU-1 (V3-5).** A trusted service, PRF security of keyed BLAKE2s (falsifiable), constructive
  collision resistance; W5 adds §5.4's heuristic. Declining keeps v3 with O-25 open (or F2's template
  route); declining only W5 keeps D4 all-oracle.
- **RU-2.** The designated-verifier window until key release; declining it means D3 (+0.5–12% per
  child in-circuit, +150–300 trusted lines). **RU-3.** "A witness, or a collision computed by the
  extractor" (W5: or a late preimage) as the clause, exactly as strong as `Computes`.
- **RU-4.** The long shape `r = 4, n = 2^20`, or an explicit statement that flattening below `j ≈ 4`
  is allowed.
- **RU-5.** Records certify the attested deployment; a real-world recursion from a winner still rests
  on the usual heuristic. **RU-6.** Whether to run R3 and R4; under R3 the repeat rule (A3: fresh `k`
  and starts per repeat) and the chain encoding (generic 1.16× or compact 0.5×).
- **RU-4 with RU-6.** The long shape and R3 together put the baseline leaf at 7,774 of `2^13` calls,
  418 to spare, 5% under the cap (§6.3): leaves must stay SNARK-shaped and query-lean, and a heavier
  leaf would need the cap re-examined at that shape, which the exploration did not do.

---

## 13. Evidence index

Links point at branch `explore/relativized-nark` of `scaraven/recursion.fast`; the F2 memo and its
review are in the submissions repository (§2, §3.4), not on that branch.

### 13.1 Lean probes

Untrusted; `timeout 900 lake build RecursionFastExplore`; namespaces `RecursionFast.Explore.<Dir>`.

| Theorems | File | Shows | Scope |
|---|---|---|---|
| `RelL`, `KStateRel`, `runLog_of_agrees` | [Relativized/Defs.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Relativized/Defs.lean) | the relativized relation and state; the paper theorem carries over | no `proofCap` conjunct |
| `compose`, `compose_flat`, `paper_tree`, `V3.v3_no_compose` | [Relativized/Compose.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Relativized/Compose.lean) | whole tree from one log, one bound; v3 does not compose | no `cert` events; `v3_no_compose` for the control's own extractor |
| `ws_ksRel`, `concatState`, `concatV_node_run`; `Backdoor.backdoor` | [Relativized/Concat.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Relativized/Concat.lean), [Relativized/Backdoor.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Relativized/Backdoor.lean) | witness-sending and concatenation meet the requirement; the backdoor is relativized-sound at `errorCap`, 32-byte magic proof | abstract codec for concatenation |
| `lazy_no_kstate`, `lazy_extractor_collides`, `kstate_of_leaf_surjective`, `deferState`, `queries_defer` | [Relativized/Lazy.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Relativized/Lazy.lean) | a trusting parent is unsound; a re-asking one is sound with at most `\|Q\|` queries | natural extractor, any `ε`; `Collides` form for every extractor |
| `encList_inj`, `runItems_valid`, `toA_runLog`; `KStateA`, `exists_isColl`, `KStateA.ofRel`, `gμ_*` | [Attested/Model.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Attested/Model.lean), [Attested/KState.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Attested/KState.lean) | the encoding is injective on bounded lists; lifting; the attested state; `WF` in `final` costs nothing | — |
| `attState`, `calls_node`, `att_W1`, `attV_complete`, `runLog_append_of_clean` | [Attested/Escape.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Attested/Escape.lean) | one `attest` per node (on the concatenated list); node completeness | children and list in the clear; one node |
| `compose_all`, `compose_blake2s`; `Paper.paper`, `Paper.paper_tree` | [Attested/Compose.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Attested/Compose.lean), [Attested/Paper.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Attested/Paper.lean) | the tree, or a named collision; certifications are free (`nq·ε`) | every `KStateA`; no flat witness; lazy sampling |
| `acceptAll_choice`, `acceptAll_iff`, `final_prop_vacuous`, `hashList_not_coll`, `encList_not_inj`, `wrong_not_wf`, `unasked_not_wf`, `shadowed_not_wf`, `unattested_not_wf` | [Attested/Controls.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Attested/Controls.lean) | the collision clause needs `Computes` and bounded lists; ill-formed logs | — |
| `KState2`, `ofHist_pub`, `blake2s_collides` | [TwoChannel/Model.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/TwoChannel/Model.lean) | the two-channel laws; `pubStep` with equality | — |
| `merkleState`, `merkle_eps_ge`, `honest_extracts(_blake2s)`, `col_no_kstate`, `col_extractor_inverts`, `pure_no_kstate`, `pure_extractor_inverts` | [TwoChannel/Merkle.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/TwoChannel/Merkle.lean) | the corrected laws hold; collisions alone and private hashing fail | two-leaf toy; natural extractor, `ε < 1` (`*_no_kstate`); every extractor (`*_inverts`) |
| `bd_no_kstate`, `bd_extractor_inverts`, `bdSecW_kstate` | [TwoChannel/Backdoor.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/TwoChannel/Backdoor.lean) | uncertifiable on the public channel, certified on the secret one | natural extractor, any `ε` (`bd_no_kstate`); every extractor (`bd_extractor_inverts`); a positive at `errorCap` (`bdSecW_kstate`) |
| `lift`, `liftState_μ`, `flatState`; `lift_free`; `lift_runner_ws`; `reask`, `flip_reask` | [Lift/Basic.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Lift/Basic.lean), [Lift/WS.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Lift/WS.lean), [Lift/Tree.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Lift/Tree.lean), [Lift/Deferral.lean](https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/RecursionFast/Explore/Lift/Deferral.lean) | any flat argument meets the requirement with its own error and queries; a decoding extractor forces re-asking | non-succinct `V₀` only; `d ≤ 14` with the library format (`d ≤ 13` with the halves, paper); `reask`'s hypothesis on the erased log |

### 13.2 Measurements and the axiom audit

Service measurements (1.22×, 2.3×, 82×, 10.3–12.5 M calls/s): [svc.log][m-svc],
[svc-multi.log][m-svcmulti]; C1's arithmetic: [arith.log][m-arithlog]; the probe library's 43.5 s
cold rebuild on the 32-vCPU VM: [explore-cold-build.log][m-cold]; spartan-chain, issue #6 and Flock
inputs: [C1] §1. The 69 declarations in [Audit.lean][m-audit], every Lean name this document cites,
depend only on `propext`, `Classical.choice`, `Quot.sound` ([audit-orchestrator.log][m-auditlog]).
A source scan finds no `sorry`, `native_decide`, `implemented_by`, `extern` or `csimp`. The library
is 21 modules, 3,008 code lines (5,196 in all).

[REPORT]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/REPORT.md
[REVIEW]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/reviews/EXPLORE-report-review.md
[DREVIEW]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/reviews/DESIGN-relativized-recursion-review.md
[PROMPT]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/00-prompt-review.md
[L1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/L1-literature.md
[T1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/T1-impossibility.md
[A1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/A1-attacks-D1-D2.md
[A2]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/A2-attacks-W5.md
[A3]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/A3-attacks-D4plus.md
[C1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/C1-cost.md
[W1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/W1-workarounds.md
[W2]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/W2-attested-oracle.md
[P1]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/P1-lean-probes.md
[P2]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/P2-attested-lean.md
[P3]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/P3-two-channel-lean.md
[P4]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/notes/P4-lift-lean.md
[m-svc]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/probes/c1-cost/svc.log
[m-svcmulti]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/probes/c1-cost/svc-multi.log
[m-arithlog]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/probes/c1-cost/arith.log
[m-cold]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/probes/audit/explore-cold-build.log
[m-audit]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/probes/audit/Audit.lean
[m-auditlog]: https://github.com/scaraven/recursion.fast/blob/explore/relativized-nark/docs/explore/probes/audit/audit-orchestrator.log

<!-- Copied from CambridgePQ/recursion.fast/design/DESIGN-v2-chips-walltime.md (2026-10-14). This copy is the one this repository implements; keep the two in sync. -->
# recursion.fast v2: chips + CCS relation, verifier-as-circuit recursion, wall-time scoring

Status: **design in force for the v2 contract** (user decisions of 2026-10-14; this file supersedes
`DESIGN.md` wherever the two disagree). Written for the agent that builds the v2 contract, harness
and baseline. Read `CLAUDE.md` first, then this file, then `contract-v03/RESULT.md` for the
harness that carries over.

What changed against the report (v1.0) and `DESIGN.md` v0.3, in one paragraph: the relation is
no longer a flat R1CS but a *structured* constraint system (chips, each a uniform CCS row gadget,
connected by buses); the verifier is no longer a RISC-V image with proved cycle counters but a
Lean IOP verifier whose compiled form is *executed and timed* on one reference machine; recursion
is no longer the typed accumulation track (T2) but *verifier-as-circuit*: the agent supplies the
layout `C_V` of their own compiled verifier and proves it correct, and the headline score is the
measured wall time of one 2→1 recursion step. The RISC-V machine remains only as the extractor's
cost model (Q1). Binary fields, the bounded extractor (Q1) and the universal relation (Q4-A) stay.

Decision IDs used below: `V2-x` (new), `Q-n` (`DISCUSSION.md`), `A-n`/`D-n` (reviews, design notes).

---

## 1. Objective and the one-line pitch

Agents submit a hash-based SNARK (prover, verifier, extractor, security proofs in Lean 4) for a
universal structured relation over GF(2^64), plus the arithmetisation of their own verifier.
Ranked by **the wall time of one 2→1 recursion step** on the organiser's machine. Security is
kernel-checked; cost is measured. The design space is the whole of "how to build a fast recursive
hash-based SNARK over a binary field": chips, buses, lookups, hash choice, commitment layout,
query patterns, folding, prover engineering.

Non-goals: zero knowledge; a proved cost model for the verifier; proving the native prover
correct; a composition theorem across recursion levels (ROM heuristic, §6.6).

---

## 2. Relation (trusted): chips + CCS + bus

### 2.1 Definition

Field: `K = GF(2^64) = GF(2)[x]/(x^64+x^4+x^3+x+1)` (`Contract/Field.lean`, unchanged);
challenges from `E = K[y]/(y^3+y+1)`. Never prime fields (user requirement).

The relation is `Layout.rel k x w`, the draft of 2026-10-14 (typechecked against the contract's
Mathlib, 52 code lines; the final file is `Contract/Layout.lean`, estimate ≤ 90 lines with caps):

```lean
/-- CCS row gadget (Setty–Thaler–Wahby 2023): Σ_i c_i · ∘_{j ∈ S_i} (M_j z) = 0, row by row. -/
structure Gadget (K : Type) (width : ℕ) where
  cons : ℕ
  t : ℕ
  M : Fin t → Matrix (Fin cons) (Fin width) K
  q : ℕ
  S : Fin q → Finset (Fin t)
  c : Fin q → K

def Gadget.holds (g : Gadget K width) (z : Fin width → K) : Prop :=
  ∀ r, ∑ i, g.c i * ∏ j ∈ g.S i, (g.M j).mulVec z r = 0

/-- A row takes part in the port iff its `sel` cell is `1`; the message is the tuple `msg`. -/
structure Port where
  bus : ℕ
  send : Bool
  sel : ℕ
  msg : List ℕ

inductive BusKind | eq | sub   -- interaction (sent = received) / lookup (received ⊆ sent)

/-- A chip: `cols` columns, one gadget seeing row `r` and row `r+1` (cyclic), its ports. -/
structure Chip (K : Type) where
  cols : ℕ
  gadget : Gadget K (cols + cols)
  ports : List Port
  fixed : Option (Table K)      -- v2 addition: a preprocessed table (part of the index)

/-- The index: the chips, the kind of each bus, which chip holds the public input. -/
structure Layout (K : Type) where
  chips : List (Chip K)
  bus : ℕ → BusKind
  pub : ℕ

structure Table (K : Type) where   -- the witness: one table per chip
  rows : ℕ
  cell : ℕ → ℕ → K

def view (C : Chip K) (T : Table K) (r : ℕ) : Fin (C.cols + C.cols) → K :=
  fun i => if (i : ℕ) < C.cols then T.cell r i else T.cell ((r + 1) % T.rows) (i - C.cols)

def Table.msgs (T : Table K) (p : Port) : Multiset (List K) :=
  ((range T.rows).filter fun r => T.cell r p.sel = 1).val.map fun r => p.msg.map (T.cell r)

def traffic (L : Layout K) (w : List (Table K)) (b : ℕ) (send : Bool) : Multiset (List K) :=
  ((L.chips.zip w).map fun ct =>
    ((ct.1.ports.filter fun p => p.bus == b && p.send == send).map ct.2.msgs).sum).sum

def Layout.rel (L : Layout K) (k : ℕ) (x : List K) (w : List (Table K)) : Prop :=
  w.length = L.chips.length ∧
  (∀ ct ∈ L.chips.zip w, ct.1.fixed.all (· = ct.2)) ∧                                  -- fixed tables
  (∀ ct ∈ L.chips.zip w, ∀ r < ct.2.rows, ct.1.gadget.holds (view ct.1 ct.2 r)) ∧   -- CCS, every row
  (∀ b, match L.bus b with
    | .eq  => traffic L w b true = traffic L w b false                               -- interaction
    | .sub => ∀ m ∈ traffic L w b false, m ∈ traffic L w b true) ∧                   -- lookup
  (w[L.pub]?.map fun T => (List.range T.rows).map (T.cell · 0)) = some x ∧           -- public chip = x
  ((L.chips.zip w).map fun ct => ct.2.rows * ct.1.cols).sum ≤ 2 ^ k                  -- size class
```

Reading guide for the builder:

- The **index** is `Layout`: gadgets, ports, bus kinds, fixed tables. Its size does not depend on
  row counts (except fixed tables, capped), so a universal verifier can read it in full. The
  sparse-matrix evaluation argument that the flat-R1CS design forced (Q4) is gone.
- The **witness** is the list of tables; the prover chooses each chip's height, as in a zkVM.
- The **bus** is a deterministic multiset predicate, counted in ℕ. LogUp/permutation challenges
  belong to the agent's proof system. The balance is *not* a field sum (see §9.2: in
  characteristic 2 a field-sum balance is meaningless).
- R1CS is the special case "one chip, one row, no ports"; a flat AIR is "one chip, `rows` rows,
  no ports"; a multi-chip zkVM is the general case. All three are admissible.
- Multiplicities: a row contributes one message when `sel = 1`. Multiplicity `m > 1` is `m`
  rows or `m` ports; it is not a cell value (a cell value is a field element, and `2 = 0`).

### 2.2 Admission caps (`Layout.Admissible`, pass/fail, trusted)

| Quantity | Cap (default) | Why |
|---|---|---|
| class `k` | `20 ≤ k ≤ 28` | leaf benchmark fits at `k ≥ 24` (§7.2); `C_V` must fit (§5.2) |
| cells `Σ rows·cols` | `≤ 2^k` | the class |
| chips | `≤ 2^8` | index reading cost |
| ports per chip | `≤ 2^4`; message length `≤ 2^4` | index reading cost |
| gadget | `t ≤ 2^6`, `cons ≤ 2^8`, `q ≤ 2^8`, `∣S_i∣ ≤ 8` (degree ≤ 8) | index reading cost; degree bound for the agent's proof system |
| buses | `≤ 2^8` | index reading cost |
| fixed tables | `Σ cells ≤ 2^(k−4)` | the verifier commits to them once (holographic) |
| statement `nx` | exactly `32` K-elements = 8 digests of 32 bytes | Q4: a few digests; FS absorption cost is fixed |

The sum of these bounds is what makes "the verifier reads the index" cheap and index-independent;
agents cannot blow up the index to hide work (the index is committed in `VK`, §3.2).

### 2.3 Controls (`Controls/Layout.lean`, CI)

Positive: a one-chip one-row layout satisfies `rel` iff the v0.3 `R1CS` does (`R1CS_iff_layout`);
a two-chip layout with one `.eq` bus; a `.sub` lookup against a fixed table; a chip with a
transition gadget (Fibonacci). Negative: one swapped message breaks the `.eq` bus; one value
outside the fixed table breaks `.sub`; no public chip ⇒ `rel` false for every `x`; a gadget no row
satisfies; cells `> 2^k`. The accept-all / reject-all controls of v0.3 (`Controls/Negative.lean`)
carry over unchanged.

---

## 3. Protocol model and what the agent submits

### 3.1 Proved object: a holographic public-coin IOP (carried over from v0.3)

`Contract/Shapes.lean` (round shapes, oracles, transcripts) and `Contract/Security.lean`
(`PerfectComplete`, `Extractor`, `KSF`, `KSF.Bad`, `RbrKS`, `SecureWith`, `errorCap = 2^-128`)
are reused **verbatim**. `Contract/Protocol.lean` changes `Index sz` to `Layout K` and `rel sz` to
`relK k`:

```lean
/-- Admissible layouts of class k with their statements and witnesses. -/
def relK (k : ℕ) : Set ((Layout K × Stmt) × List (Table K)) :=
  {p | p.1.1.Admissible k ∧ p.1.1.rel k p.1.2 p.2}

structure Protocol (k : ℕ) where
  n : ℕ;  n_le : n ≤ roundCap                       -- 2^14
  shape : Fin n → Round
  vkLen : ℕ;  vkLen_le : vkLen ≤ vkCap                -- 2^10 K-elements
  VK : Layout K → (Fin vkLen → K)                     -- computable
  idxShape : OShape
  IDX : Layout K → OVal idxShape                       -- computable
  prover : Strategy shape (Layout K × Stmt) (List (Table K)) Unit Unit   -- Lean spec, may be noncomputable
  verify : (Fin vkLen → K) → Stmt → OVal idxShape → FullTranscript shape → Bool   -- computable (v2: it is executed)
  WitMid : Fin (n + 1) → Type
  extractor : ExtractorImage shape (Layout K × Stmt) (List (Table K)) WitMid k   -- Q1, §6.3
  ε : ChallengeIdx shape → ℝ≥0

def Protocol.Secure (P : Protocol k) : Prop :=
  SecureWith (relK k) Set.univ P.prover P.specVerifier P.extractor.toExtractor P.ε
```

`Stmt := Fin 32 → K`. The verifier reads the layout only through `VK L` and the index oracle
`IDX L` (holography), as in v0.3.

### 3.2 Executed objects: the compiled argument

The IOP is compiled to a non-interactive argument by the **organiser's** transform
`compile : Cfg → Protocol k → NARG`, a Lean function (`Contract/Compile.lean`, estimate 400
lines; trusted by review, §8):

- BCS: each prover round's oracles are Merkle-committed with `cfg.hash` at arity `cfg.arity`;
  the index oracle `IDX L` is committed once by the indexer and its root is part of `VK`;
  a QUERY becomes a leaf plus an authentication path in the proof.
- Fiat–Shamir: challenges are squeezed from a sponge over `cfg.hash`, domain-separated,
  absorbing `VK ‖ x` first, then each round's root.
- `NARG cfg P : VKBytes → Stmt → Tape → Bool`, deterministic, total; the proof format (tape) is
  defined here and capped at 1 MiB (`tapeCap`, carried over).

`Cfg` is a menu, chosen by the agent: `hash ∈ {blake2s, sha256, keccak256, blake3}` (only
functions with a Lean spec in the repository; blake2s is the required first one), `arity ∈
{2, 4, 8, 16}`, leaf packing (K-elements per leaf, from the declared `OShape.logLeaf`), query
batching on/off. No grinding (the proved `ε` is the IOP's; a nonce buys nothing here).

The **executed verifier** is `NARG cfg P` compiled by the Lean compiler (`lake exe verify`,
organiser `Main.lean` importing the agent's module, built in the gate tree). There is no second
verifier artefact and no `Agrees` theorem in v2: the thing timed is the thing proved, up to the
Lean compiler and `compile` (§8).

The **executed prover** is the agent's native program (any language; built from source in the
sandbox with the pinned toolchains). It is *not proved*. It must: read `(L, VK, x, w)` from
files, write a tape that `NARG cfg P` accepts, and do so for every benchmark instance within
budget. The **executed indexer** is the Lean-compiled `VK`/`IDX` (untimed, §7.4); a native
indexer may be used by the prover but the resulting `VK` bytes must be identical.

### 3.3 Submission contents

| Item | Form | Checked by |
|---|---|---|
| `P : Protocol k`, `cfg : Cfg` | Lean | gate (computable `VK`, `IDX`, `verify`, extractor image; `--computable` rule updated) |
| `secure : P.Secure` | Lean theorem | comparator (two kernels), axiom audit |
| leaf entry (board L, optional) | nothing extra | benchmark runner |
| recursion entry (board R): `C_V`, `decode`, `rec_sound`, `rec_complete` (§5.3) | Lean | comparator, gate |
| native prover (+ optional indexer) | source + build script | sandbox build, benchmark runner |
| claim JSON (`k`, `cfg`, cells of `C_V`, declared budgets) | rendered into the challenge stub (v0.3 renderer) | comparator (`submission = rendered`) |

---

## 4. Security definitions (trusted)

All statements are the v0.3 ones over the new relation; nothing here is new except the extractor
image (Q1) and the recursion entry (§5).

1. **Perfect completeness** (`PerfectComplete (relK k) Set.univ P.prover P.specVerifier`): for
   every admissible layout, statement and satisfying witness, and *every* challenge vector, the
   Lean prover's transcript is accepted.
2. **Round-by-round knowledge soundness** (`RbrKS`): a knowledge state function `KSF` for the
   named extractor with per-round errors `ε c ≤ 2^-128`, in counting form
   (`#bad ≤ ε · #challenges`). Worst case per prefix; no probability measure in the trusted base.
3. **Bounded extractor** (Q1, decided 2026-10-13): the extractor is a RISC-V image run on the
   vendored Rv64 with fuel `B(k) = 2^(2k+16)` cycles per call; `extractMid` is *defined* as
   "decode the image's output, default witness on fuel exhaustion", so the `KSF.next`/`full` laws
   force the bound exactly where extraction must succeed. This is what makes "knowledge" mean
   something for the hash-chain leaves (preimage-hard: accept-all would need a provable preimage
   finder within `B(k)`) and what gives recursion its `N · t_E` bound. Open organiser item: the
   serialisation and size bound of the agent-chosen `WitMid m` types (Q1 contract change).
4. **Rejecting runs** (Q3): v2 has no proved cost counters, so the all-runs bound becomes
   *totality*: `verify` is a total Lean function and `compile` is total, so every tape
   terminates; the measured verification time on random tapes is an unranked DoS column (§7.5).
5. **Why the relation is hard where it must be** (Q4): the leaf benchmark is "hash chain with
   private start" (§7.2), preimage-hard, so (2)+(3) are non-vacuous; the recursion relation is
   deterministic given the proofs (§5), so there soundness carries the content and (3) supplies
   the proofs to the next level's argument.

The ArkLib bridge (`Bridge/ArkLib.lean`, one-directional `RbrKS.toArk`) carries over unchanged
and stays untrusted.

---

## 5. Recursion: verifier-as-circuit (replaces track T2)

### 5.1 Statement format (trusted, `Contract/Recursion.lean`)

`Stmt = 8 digests`, `d0..d7`, each 4 K-elements = 32 bytes.

| Kind | `d0` | `d1` | `d2` | `d3..d7` |
|---|---|---|---|---|
| leaf (hash chain, §7.2) | `y` (chain end) | `n` (chain length, one element) | 0 | 0 |
| node | `D(VK C_V)` | `D(VK L_chain)` | `Blake2s(x₁ ‖ x₂)` | 0 |

`D` = Blake2s-256 of the VK bytes. A node's statement commits to both verification keys and to
its two children's statements; the organiser checks at the root that `d0 = D(VK C_V)` and
`d1 = D(VK L_chain)` for the submitted protocol and the benchmark layout, and recomputes the
statement tree over the leaf statements.

### 5.2 The recursion layout and the fixed point

The agent supplies `C_V : Layout K` whose satisfiability means "the compiled verifier accepts two
children". Its witness (`NodeWitness`) holds `x₁, π₁, x₂, π₂`, the child tags `t₁, t₂ ∈ {leaf,
node}`, and the two VKs as cells. The organiser's specification of what `C_V` must enforce:

```lean
/-- What a node proves: both children verify under the right key, keys match the digests,
and the statement is the aggregate. (Trusted, ≈ 40 lines.) -/
def aggOK (cfg : Cfg) (P : Protocol k) (x' : Stmt) (nw : NodeWitness) : Bool :=
  D nw.vkC = x'.d0 && D nw.vkL = x'.d1 && x'.d2 = blake2s (nw.x₁ ++ nw.x₂) &&
  child cfg P nw.vkC nw.vkL x' nw.t₁ nw.x₁ nw.π₁ && child cfg P nw.vkC nw.vkL x' nw.t₂ nw.x₂ nw.π₂

def child cfg P vkC vkL x' tag x π : Bool :=
  match tag with
  | .node => x.d0 = x'.d0 && x.d1 = x'.d1 && NARG cfg P vkC x π
  | .leaf => NARG cfg P vkL x π
```

**Fixed point (V2-1).** `C_V.Admissible k ∧ C_V.cells ≤ 2^k` for the *same* `k` at which `P` is
secure. The trivial verifier (check every constraint; linear in the index) has no fixed point, so
it is excluded from board R without a proof-size cap. Smaller `C_V` is the whole game.

**VK cycle.** `VK C_V` depends on `C_V`, which verifies proofs under `VK C_V`. The cycle is broken
the standard way: the VK enters `C_V` as *witness cells* checked against the public digest `d0`;
nothing inside `C_V` depends on the value of `VK C_V`.

### 5.3 The agent's circuit-correctness theorems

```lean
structure RecursionEntry (P : Protocol k) (cfg : Cfg) where
  C : Layout K
  fits : C.Admissible k                                   -- includes cells ≤ 2^k
  decode : List (Table K) → NodeWitness                   -- computable: reads the node witness out of the tables
  sound : ∀ x' w, C.rel k x' w → aggOK cfg P x' (decode w) = true
  complete : ∀ x' nw, aggOK cfg P x' nw = true → ∃ w, C.rel k x' w ∧ decode w = nw
```

`sound` is the load-bearing one: any satisfying assignment of `C_V` contains two accepted child
proofs, and `decode` names them (no existential), so the extractor chain is explicit:
root proof → (KS of `P` on `C_V`) tables → (`decode`) child proofs → … → leaf proofs → (KS of `P`
on `L_chain`) chain preimages. `complete` keeps the honest path inhabited.

The theorem is about `aggOK`, which calls `NARG cfg P`, i.e. Merkle verification, Fiat–Shamir
and the IOP verifier's arithmetic all have to be arithmetised and proved. This is the heaviest
obligation in v2 and the reason for the Clean frontend (§9).

### 5.4 What is *not* claimed

No theorem composes levels. `sound` and `Secure` are per level; the step "NARG accepted ⇒ the
prover knew a witness" is the BCS/Fiat–Shamir transformation in the random-oracle model, applied
with the hash instantiated inside `C_V`. This is the same heuristic every deployed recursive SNARK
relies on and the open problem leanerVM documents. The report's §8.4 wording stands.

---

## 6. Scoring: wall time on the reference machine

### 6.1 Principle (Q2, resolved 2026-10-14)

Measured wall time on **one organiser-run reference machine**, accepted with its known
weaknesses (one-machine overfitting; noise) because it prices the whole design, prover included,
and needs no cost model to audit. The proved objects (`Secure`, `RecursionEntry`) do not depend
on any price, so a change of machine never invalidates a record, only re-ranks it.

### 6.2 Boards

| Board | Score (lower is better) | Ranked? |
|---|---|---|
| **R** recursion | `S_rec` = median over node steps with two *node* children (tree levels ≥ 2) of: prover wall time on `C_V` (inputs: two child proofs) **+** `NARG` wall time on the output proof | **headline** |
| **W** wrap | `S_wrap` = the same over level-1 steps (two *leaf* children) | published, unranked (shows how recursion-friendly the leaf proofs are) |
| **L** leaf | `S_leaf` = median over benchmark chains of: prover wall time on `L_chain(n)` **+** `NARG` wall time on the proof; **proof size ≤ 2^17 bytes** | ranked, secondary |
| DoS column | `NARG` wall time on 1,000 random tapes, max | published, unranked |

Why these: on R the prover is timed *because* the fixed point excludes the trivial protocol, so
prover time is honest (it is the recursion cost); on L the proof-size cap plays that role, since a
leaf has no fixed point (proof = witness is 32 MiB at `k = 22`, the cap is 128 KiB). The verifier
is timed on both so that work cannot be shifted into it for free.

### 6.3 Benchmark run (one evaluation)

1. **Instances.** `N = 64` chains, fresh random secret starts `s_i` per evaluation, length
   `n = 2^10` for the recursion tree; the leaf board additionally uses `n ∈ {2^8, 2^12}` (16
   chains each). Secrets are never written to the sandbox the verifier runs in.
2. **Indexing** (untimed, budget 1 h total): Lean-compiled `VK`/`IDX` on `L_chain(n)` and `C_V`.
3. **Leaves**: the native prover on each chain (budget 120 s each, 48 GB). Every proof must
   verify.
4. **Tree**: 32 wrap steps, then 16 + 8 + 4 + 2 + 1 = 31 node steps. Each step is a fresh
   process in a fresh working directory, inputs on local disk (warm page cache allowed), all cores
   available, no network, no GPU, budget 600 s. Every output must verify.
5. **Root**: organiser checks `d0, d1` and the statement tree; `NARG` on the root proof
   (budget 60 s).
6. **Repeat** the whole run 3 times; `S_rec`, `S_wrap`, `S_leaf` are medians of per-run medians.

Any failure anywhere (a proof that does not verify, a timeout, a crash, memory above 48 GB)
rejects the evaluation; there is no partial credit.

### 6.4 Measurement policy

- Reference machine: x86-64, ≥ 32 cores, 64 GB, NVMe, idle during evaluation; exact SKU, kernel,
  glibc, Rust/gcc/Lean versions published per season in `harness/reference-machine.md`.
- Timed region: process start to output file closed, `perf stat`-style wall clock from the
  runner. Builds and indexing are outside it.
- Record rule: a new record must beat the standing one by **≥ 3 %** (above the measured noise).
- Re-runs: all standing records are re-measured each season and whenever the machine changes;
  the scoreboard shows the hardware id next to every number. A record is never invalidated by a
  re-run, only re-ranked.
- Prover nondeterminism: allowed (randomised algorithms), but every instance must succeed.
  Variance is the agent's problem: medians over 31 steps × 3 runs.

### 6.5 Caps (pass/fail, never scored)

| Cap | Default |
|---|---|
| `lake build` of the submission on the reference machine | ≤ 1 h, ≤ 48 GB |
| harness (comparator + nanoda + gate + axiom audit) | ≤ 2 h |
| tape (proof) | ≤ 1 MiB (R, W); ≤ 128 KiB (L) |
| VK | ≤ 2^10 K-elements |
| rounds | ≤ 2^14 |
| extractor fuel | `2^(2k+16)` cycles per call |
| indexing | ≤ 1 h total |
| leaf proving | ≤ 120 s per chain |
| a recursion step | ≤ 600 s |
| whole evaluation | ≤ 6 h |

Build time is a cap, not a score term (the earlier regulariser idea): it measures proof
engineering, not design, and has no exchange rate against seconds of proving.

### 6.6 Incentive analysis (every channel we could think of, and what closes it)

| Gaming channel | Closed by |
|---|---|
| trivial protocol (proof = witness) | R: fixed point (§5.2); L: proof-size cap |
| accept-all / accept-most verifier | `RbrKS` + bounded extractor on a preimage-hard leaf relation (§4) |
| verifier special-cases `C_V` | allowed and intended (that *is* recursion efficiency); `Secure` quantifies over all admissible layouts, so the special case must still be sound |
| overfit to benchmark inputs | secrets fresh per evaluation; leaf proofs are inputs to R, not a score; the only "input" to R the agent controls is `C_V`, which they are supposed to optimise |
| precomputation outside the timed region | fresh process per step, no persistent state; indexing is untimed but bounded and digest-checked; fixed tables capped |
| move work verifier ↔ prover | both timed on every board |
| move work into the leaf proofs ("pre-digested" proofs that make nodes cheap) | leaf budget + 1 MiB tape + `C_V` must read them within `2^k` cells; allowed within those bounds, and legitimate |
| lucky runs / noise | medians of medians, 3 % record margin, isolated machine |
| one-machine overfitting | accepted; seasonal re-runs, hardware id, SKU published |
| huge index / VK to hide work | admission caps (§2.2), `vkCap` |
| prover-chosen table heights | counted in cells ≤ `2^k` |
| exotic hash with no Lean spec | `Cfg` menu; adding a hash is an organiser PR with a Lean spec |
| nondeterministic prover that sometimes fails | every instance must succeed |
| parallelism | wall time on a fixed core count; multi-threaded provers are expected |
| rejecting-run DoS | totality (§4.4) + published DoS column |
| extractor exhausts fuel on honest inputs | caught by the `KSF.next`/`full` laws (Q1) |
| `compile` tampering | organiser code, fixed; the gate's trust-by-hash covers it |
| proof engineering tricks to pass build caps | caps are generous; not scored |
| Lean-compiled verifier is slow | same for every entry; verifier time is a small share of `S_rec`; the agent chooses `cfg` to keep it small |

---

## 7. Benchmark and baseline

### 7.1 Why hash chains with a private start

`R_chain(y, n; s) := Blake2s^n(s) = y`, `s ∈ {0,1}^256` private. Hard (preimage), cheap to
state, one parameter `n` for scaling, and representative of the application (hash-based
signatures, Merkle paths). "Public start" is rejected: witness-free, so knowledge is vacuous.

### 7.2 The leaf layout `L_chain(n)`

Generated by `harness/gen-chain-layout.py` as a `Layout` JSON rendered into Lean by the v0.3
renderer: a Blake2s chip (one row per compression round or per G-function, agent-independent),
an 8-bit limb table chip for additions mod 2^32 with a `.sub` bus (XOR is free over `K`), a
chain chip with a `.eq` bus linking compression `i`'s output to `i+1`'s input, and the public
chip holding `(y, n)`. Cell count measured at generation; `n` is chosen so that `n = 2^12` fits
class 24 (defaults `n ∈ {2^8, 2^10, 2^12}`; adjust after measuring).

Fidelity is **tested, not proved**: the generator is differentially tested against a reference
Blake2s on random `(s, n)` (satisfying witness found ⇔ `y = Blake2s^n(s)`), and a mutated
layout (one constraint dropped) must admit a wrong witness. The security theorems quantify over
all layouts, so a benchmark bug affects only the benchmark's meaning, never soundness. Upgrade
path: produce `L_chain` from leanerVM's Clean Blake2s table through `toLayout` (§9.3), which
turns fidelity into a theorem.

### 7.3 Baseline (phase 1, < 1 h to check)

`P_triv`: one prover round sends the tables as oracles; the verifier queries every cell and
decides `rel` directly; `ε = 0`; the extractor image copies the tables out of the transcript
(well within `B(k)`). `Secure` is the v0.3 toy proof over the new relation. It is a valid **L**
entry only if it meets the 128 KiB cap, which it does not at the benchmark sizes, so the baseline
is **listed, unranked**, exactly like Q1's L1 level. It has no `RecursionEntry` (no fixed point).

There is **no recursion baseline**. The first ranked R entry needs a real SNARK (FRI/STIR/WHIR-
style over `K`, or a binary-field sumcheck design) *and* its verifier as a layout *and* the
circuit theorems. This is the main feasibility risk of v2 and is accepted: the gap is "write a
known verifier as a circuit with a verified gadget library", not "build a zkVM" (the RISC-V
variant's problem). Phase 2 may fund a reference entry; it is not required to open the boards.

### 7.4 What the organiser runs per submission (harness order, carried over: A6-G0)

1. Comparator first in a fresh sandboxed tree (default kernel + nanoda), manifest checked.
2. Gate in a second fresh tree, build bound byte-for-byte to the comparator's (A7-M3), trust by
   `.olean` hash; `--computable` on `VK`, `IDX`, `verify`, `decode`, the extractor image.
3. Badge path: build `lake exe verify`; index; benchmark run (§6.3) under the sandbox with the
   agent's native prover; publish numbers.

---

## 8. Trusted base (what a human must read)

| File | Lines (est.) | Status |
|---|---:|---|
| `Contract/Field.lean` | 36 | unchanged |
| `Contract/Layout.lean` (§2) | ≤ 90 | **new**, replaces `R1CS.lean` (36) |
| `Contract/Shapes.lean` | 50 | unchanged |
| `Contract/Security.lean` | 55 | unchanged |
| `Contract/Protocol.lean` | ≈ 30 | `Index` → `Layout` |
| `Contract/Extractor.lean` (Q1 image, fuel, `toExtractor`, `WitMid` serialisation) | ≈ 60 | **new** |
| `Contract/Machine.lean` | ≈ 120 | **trimmed**: plain Rv64 run with fuel; counters, timer, harts, `Acct` deleted |
| `Contract/Recursion.lean` (§5.1–5.3) | ≈ 70 | **new** |
| `Contract/Certificate.lean` (leaf/recursion entries, rendered claim) | ≈ 60 | rewritten |
| `Contract/Compile.lean` (§3.2) | ≈ 400 | **new; trusted by review** (deployment security is heuristic anyway; it is in the cone of `aggOK`) |
| `Contract/Hash/Blake2s.lean` | ≈ 150 | **new**; required by `aggOK`, `D`, and `cfg.hash = blake2s` (reuse an existing verified Lean spec if one is found; leanerVM has a BLAKE2s table but check for a pure spec) |
| vendored Rv64 | ≈ 930 reached | unchanged, now serves only the extractor |
| **deleted** | | `Cost.lean` 72, `Timer.lean` 22, `Accumulation.lean` 77, `QProg.lean` 21, `Agrees.lean` 18, most of `Machine.lean` |

Total ≈ 1,000 lines of contract Lean plus the vendored machine, against v0.3's 795 + 930. The
trust is reshaped rather than shrunk: less "cost accounting", more "protocol compilation". The
budget of 850 for `Contract/` excluding `Compile.lean` and the hash spec still holds.

Everything else is untrusted and kernel-checked: `Library/` (padding, dense equivalence, field
facts, `FiniteField K` instance, Clean bridge), `Bridge/`, `Controls/`, the benchmark generator,
the runner.

---

## 9. Clean as the circuit frontend (untrusted)

Findings from the pinned checkout (`42fe4b26`, 2026-09-29, in leanerVM's `.lake`; builds on
Lean v4.34.1 with Mathlib v4.34.1 there, although its own `lean-toolchain` says v4.33.1).

### 9.1 What it gives

- `Clean.Air.FlatEnsemble`: table ensembles with channels; `Ensemble.Statement ens x :=
  ∃ w, constraints on every row ∧ channels balance` — the chips + bus relation.
- `FormalCircuit` / `GeneralFormalCircuit`: per-gadget soundness and completeness, subcircuits,
  loops, proof automation (`circuit_norm`, `circuit_proof_start`), `Vm.lean`'s pull/push
  state-chaining theorem.
- Field-generic core: `[FiniteField F]` is Clean's own class, documented to admit `GF(2^n)`;
  only `ZMod p` instances ship.
- Hygiene: the only `sorry`s are in a tactic test file.
- Precedent: leanerVM uses Clean ensembles over a binary field with a BLAKE2s table
  (`LeanerVM/Arithmetization/Tables/Blake2s.lean`) and translates components to computable
  CompPoly polynomial tables (`LeanerVM/Protocol/ToClean/*`, no `sorry`).

### 9.2 The characteristic-2 catch

Clean's `BalancedInteractions` is a sum of multiplicities **in the field** with the side condition
`length < ringChar F`. In characteristic 2 that admits at most one interaction per channel, and
"pushed twice, never pulled" balances as `2 = 0`. The bus-composition theorems carry
`ringChar F ≠ 2` (11 occurrences in `Air/Balance.lean`, `Air/Vm.lean`). leanerVM hit this
(their finding C2) and defines balance as a `List.Perm` counted in ℕ while using Clean's tables
and constraints unchanged. Our `Layout.rel` does the same with `Multiset`.

### 9.3 Decision (V2-2)

- Clean is **never in the trusted base** (the cone of `Ensemble.Statement` is 37 modules,
  15.4k lines) and the contract never mentions it.
- `Layout` is **Clean-shaped by construction**: one row-gadget per Clean component (a Clean
  `assert` of degree `d` is one CCS term with `∣S_i∣ = d`), one port per channel interaction
  (`mult = ±1` ⇒ send/receive), `Lookup`/`StaticLookupChannel` ⇒ a `.sub` bus against a fixed
  table, `ProverData` tables ⇒ fixed tables, multiset balance in ℕ.
- Organiser deliverables in `Library/Clean/` (untrusted): (1) `FiniteField K` instance;
  (2) `toLayout : Ensemble K PublicIO → Layout K` with
  `(toLayout ens).rel k x w ↔ ens.StatementPerm x` where `StatementPerm` is `Statement` with the
  ℕ-multiset balance (template: leanerVM's `ToClean`); (3) binary-field hash gadgets, starting
  from leanerVM's BLAKE2s table; (4) the characteristic-safe balance, with an upstream PR to
  Clean (multiplicity in ℤ or a direction bit) as the long-term route.
- Agents may bypass Clean and hand-write `C_V` with their own `sound`/`complete` proofs.

Risks: Clean API churn (module system, 4.33→4.34 branch), no written documentation, unmeasured
build time of the 37-module cone against our pins (leanerVM proves the pin combination builds;
the time must be measured before Clean goes into CI).

---

## 10. What carries over from `contract-v03/` and what does not

| v0.3 component | v2 |
|---|---|
| `Field.lean`, `Shapes.lean`, `Security.lean` | unchanged |
| `R1CS.lean` (`SpMat`, `Index`, padding) | replaced by `Layout.lean`; R1CS becomes a Library special case (`R1CS_iff_layout`) |
| `Protocol.lean` | `Index sz` → `Layout K`; `verify` must be computable |
| `Machine.lean`, `Timer.lean`, `Cost.lean`, `Agrees.lean`, `QProg.lean` | counters, timer, harts, cost profiles, score functions, `Agrees`: deleted; plain `run` with fuel kept for the extractor |
| `Accumulation.lean` (T2) | deleted; recursion is §5 |
| `Certificate.lean`, challenge stubs, `render-challenge.py` | kept; new stubs `L.lean.in`, `R.lean.in` |
| `scripts/Gate.lean`, `AxiomAudit.lean`, `harness.sh`, `ci.sh`, manifest, sandbox, comparator, nanoda | kept; `--computable` set updated; badge path = benchmark runner |
| `Library/` (`RbrSound`, `Transfer`, `Field`, `Image`, `Pad`) | `RbrSound`, `Transfer`, `Field` kept; `Image`, `Timer`, `Seq`, `V02` deleted; `Pad` rewritten for `Layout` |
| `Bridge/ArkLib.lean` | kept |
| `Controls/` | `Toy`, `Negative`, `FieldSpec`, `Hit` kept; `MachineSmoke`, `Harts`, `Accumulation` deleted; `Layout`, `Recursion`, `Compile` controls added |
| `submissions/baseline-v03` | migrated to `P_triv` over `Layout` (§7.3); image, emulator, counters dropped |

---

## 11. Build order for the organiser (P0 first)

1. `Contract/Layout.lean` + `Controls/Layout.lean` + `Library/R1CS_iff_layout`; line count ≤ 90.
2. `Protocol.lean` over `Layout`; migrate the toy protocol and `Controls/Negative.lean`.
3. `Contract/Hash/Blake2s.lean` (spec, tested against a reference on known vectors).
4. `Contract/Compile.lean` (BCS + FS, `Cfg` menu) + controls: honest compiled toy accepted; one
   flipped bit in a path, a root, or a challenge rejected; tape cap enforced.
5. `Contract/Extractor.lean` (Q1) + `Machine.lean` trim; negative control: brute force exceeds
   `B(k)`.
6. `Contract/Recursion.lean` (`Stmt` digests, `aggOK`, `RecursionEntry`) + controls: a hand-made
   two-leaf node with the toy protocol; a layout that ignores `π₂` cannot satisfy `sound`.
7. Harness: gate `--computable` update; `lake exe verify`; benchmark runner (`gen-chain-layout.py`,
   differential test, tree runner, timing policy, reference-machine doc).
8. Baseline `P_triv`, rendered L stub, full CI under 1 h.
9. `Library/Clean/`: `FiniteField K`, `toLayout` + lemma, BLAKE2s gadget port, char-2 balance;
   measure Clean's build time first.
10. Adversarial reviews (incentives, definitions, feasibility) before opening the boards; the
    report's §6–§12 are rewritten from this file afterwards.

---

## 12. Open items

| Id | Item | Owner |
|---|---|---|
| O-1 | `WitMid` serialisation and size bound for the extractor image (Q1) | contract |
| O-2 | Blake2s Lean spec: find/verify an existing one or write it | contract |
| O-3 | Exact `L_chain` gadget design and measured cell counts per `n`; fix `k_min` | harness |
| O-4 | Clean build time against the v4.34.1 pins; `toLayout` prototype on one component | library |
| O-5 | Characteristic-2 balance upstream to Clean | library / external |
| O-6 | Reference machine SKU and toolchain pins; noise measurement to justify the 3 % margin | organiser |
| O-7 | Whether to fund a reference R entry (phase 2) | user |
| O-8 | Report rewrite (§6–§12, Appendix A regenerated from the v2 sources) | report |

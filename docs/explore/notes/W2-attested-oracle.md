# W2. D4, the attested oracle: a precise design, and the attack on it

Designer-adversary note, 2026-10-20, for `docs/explore/BRIEF.md` §3 (D4). Evidence tags: **kernel**
(Lean, file and name), **paper** (argument), **measured** (log), **estimate**. Sibling notes are cited
by name (A1 attacks on D1/D2, C1 cost, P1 Lean probes, W1 workarounds, where D4 is "W3"); their numbers
carry their own tags. Contract line numbers refer to this worktree's `RecursionFast/Contract/*.lean`;
`CompleteWithError`, `failProb` and `Computes` to the rules worktree.

## Summary

1. **D4 is sound and formalisable, and it is the smallest change to v3 that turns three heuristics into
   theorems.** With the node clause read from the log, `Rel` and `Wit` are *unchanged*: only the
   `Vb` argument changes from "`V` under BLAKE2s" to "`V` under the log". Composition across the tree
   is then a Lean theorem on one log (P1 `compose`, `paper_tree`: **kernel**), O-25 closes modulo PRF
   security of the service's keyed BLAKE2s (**paper**, §A.7: every F2 disguise needs a value correlated
   with the oracle that `V` did not get through a query, and there is none), and "honest proofs verify
   at deployment" closes by the same reduction. The intake rule on `V` and the typed interface of F2
   both become unnecessary: `V` may compute anything it likes on answers.
2. **The one new assumption is constructive.** The list hash is concrete BLAKE2s, so `final` must
   let the extractor return *either* a witness *or* a BLAKE2s collision. The disjunct is non-vacuous
   only because the collision is an **output of the budgeted extractor program** (`Computes`): the bare
   proposition "a collision exists" is provable in Lean by pigeonhole
   (`Finite.exists_ne_map_eq_of_infinite`) and would make `final` trivial (M5).
3. **Recursive attestation is forced, not optional** (§A.1): a child's verifier itself calls `attest`,
   so its certified list must contain attest answers, which only a recursive `certify` can check. The
   flat variant carries every hash of the subtree to the root (16 KiB, 511 calls at `r = 8`), linear
   in the tree like witness-sending.
4. **Trusted-base delta ≈ +50 contract lines** (to ≈ 340 of 500), plus a trusted service process of a
   few hundred lines that is the first *runtime* component whose bug is accept-all (M8). Harness work:
   the service, a batched shared-memory client in the badge `verify`, key and state lifecycle per
   timed run, CPU placement.
5. **What D4 does not fix.** Issue #7 (node extraction decodes) is unchanged, and D4 adds a list
   comparison to it (M6). Issue #6 is untouched on both halves: the witness-sending argument needs no
   service and still passes `T_V` at 37–43 ms threaded (**measured**), and witness-sending below level
   `j` needs no attestation at all, so flattening still halves the work (M7). A `T_V` or CPU rule
   remains necessary, and D4 gives it no extra margin.
6. **The engineering defect is the all-oracle commitment channel** (M3, M4): the key must be unknown
   to the prover (else it rides in the proof and the two-query recognition of F2 §6 is certified), so
   every Merkle hash of every proof is an IPC call, 6.7·10^7–2.7·10^8 per tree, at 0.3–0.6× in-process
   speed on a naive service (C1 §5 **measured**): noise for spartan-chain, 1.3–2× for a Flock-class
   prover. The fix is W1's W5 (public BLAKE2s for commitments, secret oracle for challenges), which
   keeps D4's attestation and theorem shape and cuts service traffic by ≈ 10^3.
7. **An option D4 uniquely enables** (§D): make the *leaf* chain an oracle chain too. Then a
   witness-sending verifier needs `n` oracle calls per leaf, and the certified bound `qV ≤ n` excludes
   witness-sending above the leaf and the trivial root *by the theorem*, not by a measurement. Cost:
   a leaf decoder in `E`, 1.6× leaf circuit (**estimate**). Not in the minimal version.
8. **Verdict.** Adopt D4's *contract* (log-relative `Rel`, recursive `certify`/`attest`, constructive
   collision output, context-form completeness) as a stage; deploy it with W5's channel split and
   W4's published log rather than online attestation if the engineering budget allows; keep #6's CPU
   rule. Do not expect D4 to change what wins on board T; expect it to make the record mean something.

---

## A. The design, made precise

### A.1 The service

State per **timed run** (one `PROVER tree` invocation and its root, sample, canary and root-step
checks; reset, with a fresh key, before every repeat of §6.3 step 9):

- `k`: 32 random bytes from the runner's `os.urandom`, never written anywhere, destroyed at reset;
- `S`: a hash set of attested 32-byte digests, initially empty.

API (one shared-memory ring per client thread; a request is a tagged frame, a response a fixed frame;
`B` requests per flush; the runner publishes the socket path into the sandbox):

| Call | Service does | Returns | Cap (deployment, per run) |
|---|---|---|---|
| `query(q)` | `a := PRF_k(q) = BLAKE2s-256(k ‖ q)` with the key block's state cached | `a` | `|q| ≤ 2^20`; no count cap (the prover's own time pays) |
| `certify(xs)` | for each item: `ans q a` → check `a = PRF_k(q)`; `att h` → check `h ∈ S`; if all pass, `S += listHash xs` | `true`/`false` | `|xs| ≤ 2^16` items, `enc xs ≤ 2^24` B, ≤ 2^20 calls |
| `attest(h)` | `h ∈ S` | bit | counted in `qV` |

`certify` is stateless on the oracle side (it recomputes the PRF; it keeps no table, C1 §5.3), so an
item whose `q` was never queried is simply evaluated now; in the model that is "query, then check"
(A.2). The service never runs `V` (M9) and never returns anything a prover cannot compute itself except
the PRF values and one bit.

**Flat or recursive.** Recursive (`att` items) is primary, because it is forced: a level-`k` node's
proof shows that `V` accepts the level-`(k−1)` child reading a list; that child's `V` makes `attest`
calls of its own (for the level-`(k−2)` lists), so the list must contain `att h` entries, and someone
must check them. In the flat variant nobody can but the root, so every list carries its subtree's
attested hashes upward and the root attests all `2^{r+1} − 1` of them: 16,352 B and 511 calls at
`r = 8` (C1 §4.2), linear in the tree, i.e. witness-sending's growth with 32 B per leaf instead of 40.
Recursive: the root proof carries two digests and the root verifier makes two `attest` calls (or one,
if the root prover certifies `[att h₁, att h₂]`; immaterial). The service's check of an `att` item is a
set lookup; no closure is ever expanded.

**Encoding** (`tagList = 0x41`, a fifth first byte, distinct from `0x43`, `0x4C`, `0x4E`, `0x52`):

```
encItem (ans q a) = 0x00 ‖ enc64 |q| ‖ q ‖ a        (41 + |q| bytes)
encItem (att h)   = 0x01 ‖ h                         (33 bytes)
listHash xs       = BLAKE2s-256 (tagList ‖ concat (map encItem xs))
```

Prefix-free item codes, so `concat ∘ map encItem` is injective on lists whose queries are shorter than
`2^64` bytes (a control theorem `encItems_injective`, to be kernel-checked; the bound is in `Valid`,
m1). No list preimage can equal a chain, leaf, node or oracle preimage (first byte). The oracle input
`k ‖ q` is BLAKE2s's business, not the relation's: with a secret key there is no cross-protocol
relation between `PRF_k` and the four concrete uses, which is the whole point.

### A.2 The model (`Contract/Oracle.lean`, replacing `Log` and extending `OProg`)

```lean
/-- An item of a certified list: an oracle answer, or an earlier attested list's hash. -/
inductive Item | ans (q : ByteArray) (a : Digest) | att (h : Digest)
/-- An event of the service's log: a fresh oracle answer, or an accepted certification. -/
inductive Ev | ans (q : ByteArray) (a : Digest) | cert (xs : List Item)
abbrev Log := List Ev

inductive OProg (α : Type)
  | ret (a : α)
  | query (q : ByteArray) (k : Digest → OProg α)
  | attest (h : Digest) (k : Bool → OProg α)
  | certify (xs : List Item) (k : Bool → OProg α)

def Log.answer (L : Log) (q : ByteArray) : Option Digest       -- first `ans q _` of `L`
def Log.attested (L : Log) (h : Digest) : Bool                 -- some `cert xs ∈ L` with `listHash xs = h`
/-- The service accepts `xs` on `L`: every answer is `L`'s first answer, every hash is attested,
every query is shorter than `2^64` bytes. -/
def Valid (L : Log) (xs : List Item) : Bool

/-- A verifier's verdict read from the log. A verifier does not certify. -/
def OProg.runLog (L : Log) : OProg α → Option α
  | ret a        => some a
  | query q k    => (L.answer q).bind fun a => (k a).runLog L
  | attest h k   => (k (L.attested h)).runLog L
  | certify _ _  => none
/-- The number of oracle calls of a run under an oracle function and an attest predicate. -/
def OProg.calls (H : ByteArray → Digest) (A : Digest → Bool) : OProg α → ℕ
```

`attest` on a log answers `false` rather than `none` when nothing matches: that is what the service
does, and a `V` accepting on a `false` is harmless (m3). `certify` in a verifier is `none`, so a
certifying `V` is never accepted on any log and cannot be complete: no extra clause is needed to
forbid it. `runLog` reads the *final* log, as in v3 §4.2: the verifier runs last, after every
certification, which is also the order the harness uses (the root, sample and canary checks run after
the tree).

### A.3 The relation and the submission (`Relation.lean` unchanged except one tag; `Certificate.lean`)

```lean
/-- `V`'s verdict on the log `L`, under the proof-size cap: v3's `Vb` with the log in place of BLAKE2s. -/
def accL (V : Digest → Proof → OProg Bool) (L : Log) (c : Digest) (π : Proof) : Bool :=
  π.size ≤ proofCap && ((V c π).runLog L == some true)
/-- The relation of a submission on a log: v3's `Rel` with `accL S.V L` as its verifier. -/
def Submission.RelL (S : Submission) (L : Log) : Digest → Wit → Prop := Rel (accL S.V L)
```

`Rel` (`Relation.lean:85-88`) and `Wit` are unchanged: leaf = concrete chain, node =
`c = nodeStmt c₁ c₂ ∧ Vb c₁ π₁ ∧ Vb c₂ π₂`. `Submission.Vb` and `blake2sOracle` disappear (the harness
runs `V` against the service; there is no closed-form instantiated verifier); `tagRO` is no longer a
relation constant. `Submission` keeps `V P E ext ε δ qV fuel`; `E`'s result type becomes `Option Out`
(A.4). A node proof carries the SNARK proof and the two attested hashes `h₁ h₂`; a leaf proof is as in
v3. The honest node prover reads `(c₁, c₂, π₁, π₂)` from `w`, assembles each child's list from the
answers it already holds (it made those queries when it produced `πᵢ`), certifies, proves in-circuit
`runTrace xsᵢ cᵢ πᵢ = some true ∧ listHash xsᵢ = hᵢ` (trace semantics: the `i`-th call is answered by
the `i`-th item; a Library lemma `runTrace_valid_runLog` lifts it to `runLog L` when `Valid L xs`), and
`V` attests `h₁ h₂` and verifies the SNARK.

### A.4 Knowledge soundness (`Security.lean`)

```lean
/-- What the extractor returns: a witness, or two distinct byte strings with one BLAKE2s digest. -/
inductive Out | wit (w : Wit) | coll (x y : List UInt8)
def Sound (R : Digest → Wit → Prop) (c : Digest) : Out → Prop
  | .wit w    => R c w
  | .coll x y => x ≠ y ∧ blake2s256 x = blake2s256 y

structure KState (R : Log → Digest → Wit → Prop) (V) (E : Digest → Proof → Log → Option Out) (ε) where
  μ     : Log → ℝ≥0
  empty : μ [] = 0
  step  : ∀ L q, L.length < logCap → μ L < 1 → L.answer q = none →
            ∑ a : Digest, μ (L ++ [.ans q a]) ≤ (μ L + ε) * 2 ^ 256
  cert  : ∀ L xs, L.length < logCap → Valid L xs → μ (L ++ [.cert xs]) ≤ μ L
  final : ∀ L c π, L.length ≤ logCap → μ L < 1 → (V c π).runLog L = some true →
            ∃ o, E c π L = some o ∧ Sound (R L) c o

def KS (R) (V) (E) (ε) (qV) : Prop := Nonempty (KState R V E ε) ∧ ∀ H A c π, (V c π).calls H A ≤ qV
```

`step` is v3's. `cert` is new and deterministic: a certification adds no randomness, so it may not
raise the potential at all; an honest potential ignores `cert` events (`μ L = μ (L.filter isAns)`) and
discharges it by `le_rfl`. `final` is v3's with `R L` and `Sound`. `Certificate.secure` becomes
`KS S.RelL S.V S.E S.ε S.qV`; `Computes` requires `decodeOut o = E c π L`.

**Why the disjunct is not vacuous.** `∃ x y, x ≠ y ∧ blake2s256 x = blake2s256 y` is a theorem of
Mathlib's pigeonhole (`Finite.exists_ne_map_eq_of_infinite`, **paper**: a classical fact, trivially
kernel-checkable), so a `final` whose conclusion were `(∃ w, …) ∨ Collision` would be satisfied by every
verifier. Here the collision must be the *value* of `E`, and `Computes` (rules worktree
`Extractor.lean`) says the step-bounded program's concrete output decodes to `E c π L`. A submitter
who defines `E` by `Classical.choose` of the pigeonhole must then prove that a deterministic program's
output *equals* the chosen pair, which needs the pair. The only way to prove `final` through the
`coll` branch is a program that compares two explicit strings and returns them when their digests
agree, which is exactly what the honest `E` does with the certified list and the decoded one. This is
the same mechanism by which `Computes` with the named extractor carries v3's knowledge content
(`Security.lean` header, V3-S1-A13). P1's `lazy_extractor_collides` (**kernel**) shows the shape from
the other side: an extractor for a lazy parent must output collisions.

**What an honest proof of `final` contains** for a node. The SNARK's knowledge-soundness lemma gives,
by decoding the committed witness from `L` (issue #7), `π₁ π₂` and lists `xs₁' xs₂'` with
`listHash xsᵢ' = hᵢ` and `runTrace xsᵢ' cᵢ πᵢ = some true`; `V`'s `attest hᵢ = true` gives
`cert xsᵢ ∈ L` with `listHash xsᵢ = hᵢ`. If `xsᵢ = xsᵢ'`, `Valid L xsᵢ` and `runTrace_valid_runLog`
give `accL V L cᵢ πᵢ`, so `E` returns `.wit (.node c₁ c₂ π₁ π₂)`; otherwise `E` returns
`.coll (tagList ‖ enc xsᵢ) (tagList ‖ enc xsᵢ')`. A leaf is v3's: `s n` in the clear, no list.

### A.5 Completeness

v3's `CompleteWithError` starts from the empty log, which is right for a concrete `Vb` and wrong here:
a node witness's children are accepted *on a log*, so the statement needs a starting state, and an
arbitrary starting log `L₀` is adversarial (it may answer the prover's next Fiat–Shamir query with a
rejecting value, so no Fiat–Shamir design meets `δ = 2^-128`; M10). The honest state is one produced
by an honest-oracle run, so quantify over the *context program* that produced it:

```lean
/-- The failure probability of "run `ctx`, then, if its result is in the relation on the log so far,
the honest prover and the verifier", under a lazily sampled oracle with the service's semantics. -/
noncomputable def failCtx (R : Log → Digest → Wit → Prop) (P) (V) : OProg (Digest × Wit) → Log → ℝ≥0
  -- `query` and `certify` as `failProb`; at `ret (c, w)` on `L`: `if R L c w then failProb ((P c w).bind (V c)) L else 0`
def CompleteWithError (R) (P) (V) (δ : ℝ≥0) : Prop := ∀ ctx, failCtx R P V ctx [] ≤ δ
```

`failProb` gains the two cases `attest h k ↦ failProb (k (L.attested h)) L` and
`certify xs k ↦ if Valid L xs then failProb (k true) (L ++ [.cert xs]) else failProb (k false) L`. The
context may query anything, including the prover's future queries, but receives the same random
answers the prover would, so `δ` is unaffected; it may certify anything valid. `ctx = ret (c, w)` is
v3's statement. The honest tree prover is a context, which is how tree completeness is proved in the
Library. About ten trusted lines.

### A.6 Composition and the error bound

With `R L` read from the same `L`, `final` applied to the root gives `(cᵢ, πᵢ)` with
`(V cᵢ πᵢ).runLog L = some true` on *the same log at the same potential*, so `final` applies again
without new hypotheses: the inner verifiers' queries are already in `L` (they are the certified lists'
entries, present by `Valid`), and only the root verifier's own calls are fresh. P1 proves this shape
(`compose`, `paper_tree`, **kernel**, for `RelL` without `cert` events); the D4 version adds the
constructive collision case. The Library theorem to write:

> `treeExtract : Digest → Proof → Log → List Digest → Option (List Digest ⊕ List UInt8 × List UInt8)`,
> a computable walk over the *harness's* tree `cs` (so it terminates; a cyclic extracted proof would
> need a BLAKE2s fixed point and surfaces as a collision against `cs`): at a harness node `nodeStmt
> c₁* c₂*` the extracted `(c₁, c₂)` either equals `(c₁*, c₂*)` or yields `.coll` of the two 65-byte
> preimages; at a harness leaf `leafStmt h* n` the extracted `.leaf s n'` either has
> `chainEnd s n' = h* ∧ n' = n` or yields a tagLeaf collision; an extracted node at a harness leaf is a
> cross-tag collision. **Statement**: `μ L < 1 →` root accepted on `L` `→ treeExtract … = some (inl
> starts) ∧ ∀ i, cs[i] = leafStmt (chainEnd starts[i] n) n`, or `= some (inr (x, y))` with
> `x ≠ y ∧ blake2s256 x = blake2s256 y`.

Error: by the paper theorem (`Library/PaperTheorem.lean`, `paper`, **kernel** for the lazily sampled
deterministic game; the `cert` moves are non-increasing and need a one-line extension), the root is
accepted while `μ L ≥ 1` with probability ≤ `Q·ε`, `Q` the number of fresh queries of the whole
evaluation (prover, service re-evaluations, root verifier). For the ranked tree `Q ≈ 2^26–2^28`
(C1 §5.1 **estimate**), far inside `logCap = 2^96` and the extractor domain `2^61` entries, so at
`ε = 2^-128` the whole-tree bound is about `2^-100`, with **no factor per level** and no heuristic log.
v3's §5.4 item 1 ("composition across levels") is gone.

### A.7 Deployment: why the model equals deployment

**Oracle channel.** The theorem averages over a random function; deployment uses `PRF_k` with `k`
secret from the prover, from `V`'s author (frozen before `k` exists) and from `V` (an `OProg` has no
input but `(c, π)` and the oracle). The bad event "root accepted ∧ `treeExtract` returns neither
starts nor a collision" is decided by a polynomial-time tester with oracle access (`E` is
step-bounded, `Sound` is decidable: `2^20` hashes for a leaf, a run of `V` on the log for a node, two
hashes for `coll`). So `Pr_deploy[bad] ≤ Pr_random[bad] + Adv^PRF(D)` where `D` is the whole
evaluation (**paper**, standard; `D` runs for hours and makes `≤ 2^28` queries, far below any keyed
BLAKE2s margin). A true random table would make the model exact without assumption, but needs 17–71 GB
of state per tree (C1 §5.3 **estimate**); use the PRF. **Attest channel.** `S` and `Log.attested` have
the same semantics by construction; no randomness, no assumption. **Collision channel.** BLAKE2s
collision resistance, already item 4 of the v3 trust statement for the statement tree, now also for
list hashes, and now *constructive*: a failed extraction hands over the colliding pair.

What is assumed at deployment, in full: PRF security of `BLAKE2s(k ‖ ·)`; collision resistance of
BLAKE2s-256; the service implements A.1 (tested, M8); the harness's instance and key freshness; the
paper step from the lazily sampled game to a random function and randomised adversaries (as v3).

### A.8 Trusted-base delta, harness work, what leaves §5.4

| File | Change | Lines (**estimate**) |
|---|---|---|
| `Oracle.lean` | `Item`, `Ev`, `Log`, two constructors, `runLog`/`calls` cases, `answer`, `attested`, `Valid`, `encItem`, `listHash` | +28 |
| `Relation.lean` | `tagList` | +1 |
| `Security.lean` | `cert` law, `Out`, `Sound`, `failCtx`, `attest`/`certify` cases of `failProb` | +16 |
| `Extractor.lean` | `decodeOut`, `extractorInput` over `Ev` | +6 |
| `Certificate.lean` | `accL`, `RelL`; `Vb`, `blake2sOracle` deleted | ±0 |
| total | 288 → ≈ 340 of 500 | +50 |

Harness: the service (Rust, ≈ 300–400 lines: PRF with cached key block, ring-buffer IPC with `B`-batched
flushes, the set, the caps, an event log at smoke size for the liveness check); the badge `verify`
gains a client (trusted badge code, item 6 of the trust statement); the runner starts, places (M4),
resets the service per repeat and runs the root, sample, canary and root-step checks before each
reset; `treeRoot` unchanged; the liveness check consumes the service's own log instead of a logging
wrapper (an improvement: the log of the native prover is now authentic). Library: `PaperTheorem` with
`cert` moves, `Tree.lean`'s `treeExtract`, `runTrace_valid_runLog`, the witness-sending baseline
re-certified (its `V` makes no calls; `μ := 0`; `cert` by `le_rfl`). Controls: `encItems_injective`,
`Valid` positive and negative, a `V` that accepts on `attest` alone has no `final` (the accept-all
argument), the service's test vectors against the Lean `Valid`/`listHash`.

Leaves §5.4: composition (now a theorem); "BLAKE2s is a random oracle" (replaced by a PRF assumption
with a reduction); O-25 (closed); "honest proofs verify under BLAKE2s" (closed by the same reduction).
Stays: the native prover's correctness; `E` outside its domain. Enters: the service's correctness
(tested); the PRF assumption; the fairness of the service's CPU (M4). The §6.7 rule "`V` must not
evaluate the instantiation" and the intake review of `V` for recognition are deleted; so is the need
for F2's typed interface, whose review found it broken anyway.

---

## B. Attacks

Major findings must be fixed before the design is adopted; minor ones are answered.

**M1. Encoding ambiguity turns a list mismatch into a non-collision.** Without a length prefix,
`ans q a` followed by `ans q' a'` re-parses as a different list with the same bytes; the circuit's
list `xs'` and the certified `xs` then differ with `enc xs = enc xs'`, and `E`'s `.coll` output fails
`x ≠ y`. The submitter cannot prove `final`. The same happens with `enc64` wrapping at `2^64` bytes
(an unbounded adversary certifies a `2^64 + 5`-byte query). **Fix**: A.1's prefix-free codes, the
`q.size < 2^64` bound inside `Valid` (so certified lists are in the injective range), and the
deployment cap `|q| ≤ 2^20`. The tag `0x41` keeps list preimages apart from the four relation
preimages, but note that this separation is only needed among *concrete* hashes: the oracle is
`PRF_k`, and no concrete preimage ever meets it.

**M2. Replay through the service's state.** (a) Across repeats: the three timed repeats run on the
same instances; if `S` persists, repeat 2's prover certifies nothing and submits repeat 1's hashes, and
v3's "fresh writable directory" rule, which blocks proof caching, is bypassed through `S`. (b) Across
evaluations or submitters: a persisting `S` or key lets lists certified elsewhere be attested here;
with published answers a `V` can be built that recognises them (A1 M9a). (c) Within a run, across
statements or children: harmless. An attested list is a set of true oracle facts bound to no
statement; using one child's list for another child, or the empty list, changes nothing the theorem
cares about (`Valid` is monotone in `L`, and acceptance still needs `V`). **Fix**: `k` and `S` fresh
per timed run; the root check, sample checks, canaries and the column-R root step run against the
*same* service state as the tree that produced the proofs, before the reset (the root-step prover's
output must attest level-7 lists certified during the tree run). The key is never logged.

**M3. The prover must not know the key, so everything goes through IPC.** If the prover held `k`
(for instance to hash locally and only *certify* through the service), the proof carries `k` and `V`
checks `PRF_k` against two oracle answers: that check is certifiable by pure counting (F2 §6, V3-S1-M1,
**paper**) and it is the backdoor. So `k` lives in a separate process the sandbox cannot read (own
uid, no ptrace, seccomp, no shared memory beyond the rings), and the prover's whole commitment phase is
oracle traffic: 262,614 calls and 278 MB per spartan-chain leaf, ≈ 10^6 calls per WHIR-class leaf,
6.7·10^7–2.7·10^8 calls per ranked tree (C1 §5.1 **estimate**). Measured on the dev VM (C1 §5.2): a
futex round trip per call is 82× slower than in-process; batched spinning rings reach 10–12.5 M
calls/s machine-wide, 0.3–0.6× the in-process rate. Consequence (C1 §5.4): +0.3–1.2% of leaf time for
spartan-chain, whose Merkle phase is 0.1 s of 7.7 s, but **+30–110% for a Flock-class prover**, whose
leaf *is* hashing. The competition's target class is the one penalised. **Fix within D4**: a
double-buffered ring per prover thread, flush sizes `≥ 2^10`, a SIMD multi-buffer BLAKE2s in the
service (up to 5× on the hashing-bound rows, C1 §5.2), and the placement of M4. **Fix beyond D4**: W1's
W5 channel split, where commitments use public BLAKE2s (binding by the same constructive collision
disjunct) and only challenges, ≈ 500 calls per proof, go to the service. W5 keeps this note's
`certify`/`attest`, `Out`/`Sound`, `failCtx` and `treeExtract` unchanged and changes only which
queries `step` prices; its open check is the two-channel potential law (W1 §7.7).

**M4. Whose cores run the service.** If the service runs outside the prover's cgroup it is a free
hashing co-processor of `2^33`–`2^35` compressions per tree, which favours Merkle-heavy designs
exactly as a free oracle charge would; if inside, it competes with the prover for the fixed core count,
which is fair but slows hashing-bound provers (M3). **Fix**: the service's worker threads are pinned to
the prover's cpuset and charged to its CPU cgroup, so the wall-time makespan prices them as it prices
the prover's own hashing; the service's memory (the set, the rings) is in a small separate memory
cgroup so a prover cannot evict it. The `certify` re-evaluation (2.6–14.5 M compressions per tree, C1
§4.3) and the list hashes are charged the same way; `certify` returns a bit, not the digest, so it is
not a hashing service. **Determinism**: IPC adds scheduler noise to a run that already has 32 threads;
the ABBA record rule and medians of three absorb it; the service's answers are deterministic in `k`,
and `k` is fresh per run exactly as the chain starts are.

**M5. The collision disjunct can be made vacuous in two ways.** (a) As a bare proposition (A.4): fixed
by making it an output of the `Computes`-bound program. (b) In the composition theorem: a Library
statement "… or a collision exists" is pigeonhole-trivial; `treeExtract` must *return* the pair, which
it can because it holds both preimages (the extracted and the harness's digests). (c) Weaker
constructive variants: a "deposit" service that stores child proofs so that `E` looks them up by hash
instead of decoding would need `final` to allow "`∃ y ≠ π₁, blake2s y = blake2s π₁`" for the
*specific* deposited `π₁`, which pigeonhole does not give but which no one can show unprovable either;
I rate it unsafe and do not recommend it. **Fix**: A.4 as written; `Sound` names `blake2s256` of the
contract, and `x ≠ y` is on bytes.

**M6. Issue #7 is unchanged, and D4 adds a comparison to it.** The child proof `π₁` and the list
`xs₁'` are inside the node SNARK's committed witness; the only route to them is decoding the codeword
from `L` (F1 §3.1's argument is untouched: the log holds the oracle's answers, the circuit's statement
is about the hash of a list). `E` must also find `cert xs₁` in `L` by hash (a scan, inside the
`2^16·t` term) and compare `xs₁` with `xs₁'` (linear). The budget `B t = 2^48 + 2^16·t` of the rules
worktree is sized for this. What D4 changes is the *tape*: `L` is now the entire evaluation's log,
tens of gigabytes (71 GB of queries for spartan-chain's leaves alone, C1 §5.3 **estimate**), which is
the honest size of the object the theorem quantifies over; the liveness smoke check at `r = 1`,
`n = 16` stays small. Leaves stay
cheap (`s n` in the clear) in the minimal design; the D4+ variant of §D loses that.

**M7. Issue #6 is unchanged on both halves; D4 adds no margin.** (a) The witness-sending root verifier
makes no oracle call and needs no service; it is certified under A.4 with `μ := 0`, and its root check
is 0.64–0.69 s sequential, 37–43 ms with `Task.spawn` (**measured**, issue #6), against a SNARK root of
`h_V ≈ 10k–26k` compressions, 8–30 ms native on a machine with carry-less multiply and ≈ 0.5 s on the
dev VM (C1 §2 **estimate/measured**). The attestation adds two calls and `≈ 10^4` IPC round trips
(3–12 ms batched, 0.4 ms for the ≈ 400 sequential Fiat–Shamir calls when spinning, 15 ms on futexes,
C1 §5.4): it *costs* the SNARK root a few milliseconds and the trivial root nothing. The CPU-time rule
of #6 (`T_V ≤ T_triv,best / 10`, or C1's 75–93 ms window) is still what separates them, and it must
now define whether the service's PRF time for the verifier's `≈ 10^4` queries (≈ 1.5 ms) is counted:
count it, by the placement of M4. (b) Witness-sending below level `j`: a level-`j` node's `V` verifies
a witness-sending child by recomputing chains, with *no* oracle call and *no* attest, so the level-`j`
SNARK is a flat SNARK over `2^j` chains exactly as in v3; at `j = 3`–`4` (memory-bound, 96 GB) it
replaces 255 node proofs by `2^{8−j} − 1` and halves the tree's constraint count (**estimate**: full
recursion `256·2^28 + 255·2^28.3 ≈ 2^37.2` against `16·2^32 + 15·2^28.3 ≈ 2^36.1`). Nothing in D4 sees
it; the rule remains the user's (V3-S2R-A7). Concatenation stays dead by `qV` and `proofCap` as in v3.
So on board T, D4 changes no incentive: what wins is what wins in v3 under the same rules. It changes
what a record *certifies*. §D gives the one D4-specific lever on (b).

**M8. The service is a trusted runtime component whose bug is accept-all.** A `certify` that accepts
one wrong answer, an `attest` that answers `true` for a never-certified hash, a reset that forgets to
empty `S`, a key reused by a crash-restart, a race between a concurrent `certify` and `attest`: each
one is a soundness hole no theorem sees. v3's harness components (runner, gate, renderer) are tested,
not proved, but none of them *answers questions whose answers the theorem relies on*. **Fix**: the
service is a small single-purpose program with the Lean `Valid`/`listHash`/`attested` definitions as
its specification and test vectors; `certify` is atomic under one lock; state lives in one process with
no persistence; a watchdog kills the run on a service crash (never restarts it); it enters the trust
statement explicitly as item 8's first *runtime* entry.

**M9. The service must never do verification work.** A `certify(c, π)` that ran `V` would make the
node proof two hashes and the competition a measurement of `V`'s own cost: hearsay in CT10's sense,
with the organiser as the prover of record. A.1's `certify` checks `PRF` values and set membership only.
Related resource attacks: `S` as memory (32 bytes per certification, nothing readable back: no);
`certify` as a hash accelerator (returns a bit: no); `certify` as a verification oracle for guessed
answers (`query` already gives them: no); huge lists or `2^20` certifications to burn organiser time
(the caps of A.1, charged to the prover's cores by M4).

**M10. Node completeness from an arbitrary starting log is unsatisfiable.** With `CompleteWithError`
quantified over all `L₀` on which the witness's children are accepted, an `L₀` that answers the
node prover's first Fiat–Shamir query with a rejecting value exists for every Fiat–Shamir design, so
no design meets `δ ≤ 2^-128`; from `L₀ = []` the node clause is empty. **Fix**: the context form of
A.5, whose starting state is produced by an honest-oracle program.

**M11. Recognition at deployment: nothing survives, with one process caveat.** Every F2 disguise
(any query, recomputed challenges, embedded image, partial or spread recognition, the literal trigger
and the trace check of ADV-M5, the `idx`/`CommRing`/`ofBytes` channels of the F2 review) compares an
oracle answer with a value `V` holds about the instantiation; under `PRF_k` there is no such value
before `k` is sampled, and A.7's reduction prices any residual at `Adv^PRF`. The attest channel
carries no randomness to recognise. The Goldwasser–Kalai, BBHMR19, KRS25 and Fenzi-2026 Fiat–Shamir
counterexamples (F2 review §4) construct protocols unsound for every *public* hash; a secret PRF behind
a query interface is a random oracle to every party without `k`, so they do not apply, and the
statement-binding rule the F2 review wanted as mandatory becomes optional hygiene. The caveat: the
model must define every response the service can give. A refused call (over cap, malformed, crashed)
must *abort* the verification as a reject, never return a value `V` can branch on, else deployment
has a symbol the model lacks. The liveness mirror (§5.4 item 4) closes by the same reduction: the
honest prover's acceptance is an efficiently testable event; what remains is "`V` rejects on an
instance the harness never runs", which is any software's residual and harms only its author.

**m1. `Valid`'s length bound and the deployment cap** (`2^64` in the model, `2^20` at the service):
the model's bound is what injectivity needs; the service's is what memory needs; a proof whose `V`
queries between them fails at deployment only, which is the author's problem (M11 caveat).

**m2. `qV` counts `attest` calls.** They cost service time, so the certificate's bound includes them
(`calls`). A `V` with `2^16` attests is admissible and pointless.

**m3. `attest` answering `false` on a miss.** A `V` that accepts *because* a hash is unattested is
accepted on the empty log for every statement, so its `final` is the accept-all obligation
(`acceptAll_kstate_iff`), which `Computes` with a real extractor cannot meet. No clause needed.

**m4. Timing and side channels on the service.** The PRF is constant-time in `q`'s content (BLAKE2s
has no data-dependent branches); `attest`'s timing reveals set membership, which the prover knows; the
rings reveal nothing but answers. The prover cannot measure the key through latency. The root
verifier's timing is the harness's. Residual: none beyond process isolation (M3).

**m5. Proof size and `proofCap`.** +64 bytes per node proof; the lists never enter a proof. Issue #8's
sizing stands (WHIR-class fits `proofCap` barely; C1 §4.1 puts the spartan-chain child list at 28.3k
compressions, 1.09× real recursion, `≈ 2^28.3` R1CS-of-bits rows per child). Nothing in D4 relaxes it;
raising `proofCap` for node proofs remains #8's decision.

**m6. In-circuit fidelity to a real public-hash recursion.** Per Merkle node query D4 hashes
`41 + |q|` bytes of list against `1 + |q|` bytes of `tagRO ‖ q` for the real circuit; per child the
ratio is 0.79–1.56 by query type and 1.09 for the spartan-chain child (C1 §4.1 **estimate**). The
gadget is the same BLAKE2s compression, the count is the child's query bytes over 64, and the thing
being minimised (verifier transcript bytes) is what a real recursion minimises. Two structural
differences: the real circuit *computes* answers and D4's *hashes* them (same compressions, no
transfer loss); and D4's list hash could in principle be any concrete hash the contract names, which
would decouple the in-circuit cost from BLAKE2s recursion, so the contract must keep BLAKE2s for it
(no "menu" for the list hash). A winning D4 node design transfers: it is "prove a short BLAKE2s
transcript of your own verifier fast", i.e. the Flock 2.0 target. What does not transfer is the
service plumbing, which a real deployment replaces by computing the hash.

**m7. Service log for liveness.** The native prover's query log is now the service's and is authentic;
the harness check "every entry's hash is right" becomes a no-op. At smoke size (`r = 1`, `n = 16`) the
log is megabytes; at ranked size it is not stored.

**m8. Comparison with D3 (signatures in-circuit, W1 §4).** Same relation, same `Out`/`Sound`, same
composition; the attestation becomes a hash-based signature the circuit verifies: +145 (XMSS,
leanSig parameters) to +1,059 (WOTS+ with a height-20 path) compressions per child, 0.5–11.5% of the
list hash (C1 §4.2 **estimate**); the root check is offline with `pk`; the trusted base gains a Lean
signature verification specification (≈ 100–200 lines against the 500 budget) and a signing oracle
whose answers are not uniform digests, which does not fit the potential's `step` law without a
substantial library (W1 §4). D3 buys third-party verifiability of records; W1's W4 (a published log of
list hashes and end-of-epoch key release) buys the same at D4's cost and is the better pairing. D4 is
the minimal theorem; D3 is a later season's hardening if offline records matter.

---

## C. Does recursion beat the alternatives on board T under D4?

No differently than under v3 (M7). The ledger, all **estimate** unless tagged:

| Strategy | Certified under D4? | Root check | Board T work | What stops it |
|---|---|---|---|---|
| Witness-sending (no proving) | yes, `μ := 0` | 37–43 ms threaded, 0.64 s one core (**measured**) | ≈ 20 ms native hashing | only a CPU-time `T_V` rule (#6(a)) |
| Concatenation of leaf SNARKs | no: `qV = 256·5156 > 2^16`; `proofCap` | 2 s–210 s | 256 leaf proofs | the caps, as v3 |
| Witness-sending below `j`, flat SNARK at `j` | yes | one proof | ≈ 0.5× full recursion at `j = 4` | nothing in the theorem; #6(b)'s rule |
| Full recursion | yes, and now composable | one proof + 2 attests, 8–30 ms native | `2^37.2` constraints | — |
| Deferral (D2: carry child queries) | yes but `qV`, `proofCap` broken at `r = 8` (A1) | 2.6 M calls | — | the impossibility, in numbers (C1 row 4) |

D4 moves the deferral row to the full-recursion row: that is the escape from the impossibility, by
authentication rather than by non-succinctness. It leaves the first and third rows where v3 left them.

---

## D. Verdict, and the minimal version to recommend

**Sound?** Yes: a potential-form `KState` over logs with `cert` events, a constructive collision
output, and a composition theorem on one log; the deployment argument is a standard PRF reduction with
a polynomial-time tester (**paper**), and every component the theorem relies on is either kernel-checked
(P1's shape), a standard falsifiable assumption on keyed BLAKE2s, or a few hundred lines of service
code with the Lean definitions as its specification. The findings that touch soundness (M1, M2, M5,
M8, M10, M11's caveat) each have a definite fix inside the design.

**Worth it?** As a contract: yes. For ≈ 50 trusted lines it deletes three heuristics and the O-25
rule-plus-review regime, and it makes F2's whole typed-interface programme unnecessary. As a
benchmark: it does not change incentives (M7), and in its all-oracle form it penalises hashing-bound
provers by up to 2× through the service (M3). The honest statement is that D4 is a security fix, not an
incentive fix, and that its engineering defect has a known cure (W5) that does not disturb its
theorem.

**Minimal version.**

1. Contract as in A.2–A.5: `Item`/`Ev`/`Log`, `attest` and `certify` in `OProg`, `runLog` with
   `certify ↦ none`, `Valid` with the length bound, `encItem`/`listHash` under `tagList`, `accL` and
   `Submission.RelL` with `Rel` and `Wit` untouched, `KState` with the `cert` law and `Sound`, `Out`
   with `decodeOut` under `Computes`, context-form completeness. Delete `Submission.Vb`,
   `blake2sOracle`, the §6.7 recognition rule and the intake review of `V`.
2. Recursive attestation only (A.1); `certify` returns a bit; caps of A.1.
3. Service: PRF `BLAKE2s(k ‖ ·)`; `k` and `S` fresh per timed run; checks before reset; a separate
   process the sandbox cannot read, pinned to the prover's cpuset and CPU cgroup, batched
   double-buffered rings; abort-on-refusal semantics; the Lean definitions as its test vectors.
4. Library: `PaperTheorem` with `cert` moves; `treeExtract` and its theorem; `runTrace_valid_runLog`;
   the witness-sending baseline re-certified; the controls of A.8.
5. Keep #6's CPU-time `T_V` rule and the per-level rule for (b); D4 does not replace them.
6. Prefer W5's channel split for deployment as soon as its potential law is probed (W1 §7.7), and W4's
   published log over online `attest` if third-party verifiability of records is wanted; both keep
   items 1–4.

**D4+, for a later decision.** D4 can relativize the *leaf* too: `RelL L c (.leaf s n) := n ≤ chainCap
∧ c = leafStmt (chainO L s n) n` with `chainO` applying `L.answer (tagChain ‖ ·)` `n` times, the leaf
prover querying its chain through the service and certifying the `n`-item list, the leaf circuit
hashing that list (`1.6·n` compressions against `n`, **estimate**). Then a witness-sending leaf verifier
makes `n` oracle calls, a witness-sending node at level `j` makes `2^j·n`, and the certificate's
`qV ≤ n` (with `n = 2^14` and the leaf SNARK's own ≈ 5k calls under it) excludes witness-sending above
the leaf and the trivial root **by the theorem**: #6(a) and #6(b) close without a measurement, and
`T_V` becomes a liveness cap. The brief rejected an oracle leaf because its verifier would need `Ω(n)`
queries; attestation is exactly what removes that objection. Costs: the leaf extractor must decode
(the collision branch needs the circuit's list, M6), so the cheap-leaf property of v3 is lost; the
leaf is no longer "prove a BLAKE2s computation" but "prove a BLAKE2s transcript of a computation", the
same gadget at 1.6× the bytes; and the leaf's `2^22` chain calls per tree join the service traffic
(negligible against commitments). It deserves its own attack pass before adoption; I would run it as
the second stage after the minimal version, because it is the only lever found in this exploration
that prices recursion in the theorem rather than in a rule.

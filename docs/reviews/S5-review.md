# S5 review: recursion (`aggOK`, `RecursionEntry`, `rootOK`) and the certificate types

Adversarial review of Stage 5 as it stands after the orchestrator's decision pass (S5-A7, S5-A8,
S5-A9), 2026-10-15. The reviewer read `CLAUDE.md`, DESIGN §3.3, §5, §6.2–§6.3, §7.3 and §8,
the amendments S1-A6, S1-A12(c), S3-A8, S6-A3 and S5-A1 to S5-A9, and `docs/stages/S5-RESULT.md`.
It then read the code in full: `Contract/{Recursion,Certificate}.lean` (trusted),
`Contract/{Compile,Protocol,Layout,Shapes}.lean`, `Library/{Recursion,Compile}.lean`,
`Controls/{RecursionData,Recursion,RecursionNode,Certificate,CompileToy,Toy}.lean` and
`probes/s5/recursion_ref.py`. Nothing under `RecursionFast/` was edited. The probes are in
`probes/s5/review/` and the logs in `logs/S5/review/`.

## Verdict

**Pass after one major fix.** The verdict covers six points.

- **The trusted definitions match DESIGN §5 and the accepted amendments.** These are
  `digestToSlot`, `nodeStmt`, `child`, `aggOK`, `rootOK`, `RecursionEntry` and the certificate
  structures. The node statement is a function of the keys and the children, with `d3 … d7 = 0`.
- **The byte encodings are injective and fixed-length.** `x₁ ‖ x₂` is always 512 bytes
  (`pair_inj`), and a digest slot determines the digest (`digestToSlot_inj`).
- **`D` is the sponge's key digest, index root included** (S3-A8).
- **Keys propagate in the right direction.** A node child must carry the parent's `d0` and
  `d1` and is verified under the parent's `vkC`. A leaf child carries no key and is verified
  under the parent's `vkL`, whose digest is the parent's `d1`.
- **S5-A1's 32-byte roots agree with `NARG`'s own check.** They also bound the one key that
  `NARG` never sees: `vkC` in a node with two leaf children, and `vkL` in a node with two node
  children.
- **The Python reference agrees with an independent 10-line reproduction.**

**One major finding (S5-M1).** The S5-A7 field `live` does not do what S5-A7 adopted it for.
`Secure` constrains `P.verify` only on keys of the form `P.VK L`. A secure protocol may
therefore accept every tape under a key that no layout has. A protocol whose compiled argument
accepts nothing under any indexer key (S5-A2's situation) then still satisfies `live`, and
`complete` covers only nodes on which `NARG` is trivial. The kernel checks this on a secure
variant of the toy (`toyCM`). The fix takes one line: state `live` at the indexer's keys. This
is exactly the form `aggOK_sat_of_secure` already produces, so it costs an honest submitter
nothing.

**Nine minor findings.**

**Tag binding is benchmark-level.** The contract does not bind tags. The probe `mistag`
accepts a node statement as a *leaf* child. What rejects such a statement in the benchmark is
the public chip of `L_chain`, which pins `x₅ … x₃₁ = 0` (`Lchain_stmt`, kernel-checked), and
the fact that leaf statements do not carry `D(vkC)` and `D(vkL)` in `d0` and `d1`. This is
enough for the one benchmark. S5-m1 gives a zero-cost contract-level binding.

## Findings

### S5-M1 (major): `live` can be met under a key no layout has, so S5-A2's vacuous recursion certificate survives S5-A7

- **Declaration.** `RecursionEntry.live : ∃ x' nw, aggOK cfg P x' nw = true`
  (`Contract/Recursion.lean`). The docstrings of the field and of the structure say that it
  keeps `sound` and `complete` from being vacuous and that, without it, `complete` is vacuous
  for a protocol whose proofs exceed the tape cap.
- **Problem.** `Protocol.Secure` evaluates `P.verify` only on `P.VK L` (`specVerifier`).
  `NARG` takes the key as an argument. `aggOK` lets a two-leaf node pick `vkL` freely, subject
  only to its digest being `d1`, and lets it pick `vkC` freely, subject only to its digest being
  `d0`. A secure protocol can therefore satisfy `live` with a "magic" key that no indexer
  produces. Its real compiled argument may still accept no tape at all, as S5-A2's toy does.
  Then `complete` constrains `C` only on magic-key nodes. On those nodes `NARG` reduces to "a
  32-byte tape". `C` needs three hashes and a few constants, and no part of the verifier.
- **Probe.** `probes/s5/review/MagicKey.lean` is kernel-checked, with axioms within the
  standard three. It runs in 21 s and 2.7 GB (`logs/S5/review/MagicKey.log`).
  - **`toyCM k`** is the toy (`Controls/Toy.lean`) with two changes. Its message is
    Merkle-committed in two leaves (shape `⟨k+10, k+9⟩`), so the rounds section is a 32-byte
    root. Its verifier begins with `if vk 0 = 2 then .done true`, and `toyVK` is never 2.
  - `toyCM_secure : (toyCM k hk).Secure` holds at every class in range. The magic branch is
    invisible to `Secure`.
  - `narg_indexed : NARG cfg2 P20 (index cfg2 P20 L) x t = false` holds for every `L`, `x`
    and `t`. The verifier's first query opens the index oracle, a leaf of `8·2^28` bytes, which
    is beyond the cap.
  - `toyCM_live (C)` gives `∃ x' nw, aggOK cfg2 P20 x' nw = true`. The witness is two magic
    leaves, and the recursion key can even be the indexer's key of any `C`.
  - `toyCM_no_indexed_node`: no node whose keys are indexer keys is accepted. The benchmark's
    nodes never are.
  - `toyCM_aggOK_iff` gives `aggOK` exactly: the aggregate statement, 32-byte roots, the magic
    element in the key each child uses, and 32-byte tapes. A `C` for this needs about 10
    BLAKE2s compressions, under 2^17 cells at `L_chain`'s rate of 9,225 cells per compression.
    With a verified BLAKE2s gadget, which every real submitter needs anyway, it is a
    `RecursionEntry`. With `toyCM_secure` it is a `SubmissionR` with a `CertificateR`, and no
    benchmark node can be proved. Only the benchmark run rejects it, which is the situation
    S5-A2 described and S5-A7 meant to close in Lean.
- **Fix (contract, +2 lines).** State `live` at the indexer's keys:
  ```lean
  /-- The compiled argument accepts a two-leaf node keyed by the indexer (`C`'s key, and the key
  of some layout `L`). Keys of no layout are excluded: `Secure` says nothing about them (S5-M1).
  A submitter proves it with `aggOK_sat_of_secure` plus a bound on its own proof size. -/
  live : ∃ L x₁ x₂ π₁ π₂, aggOK cfg P (nodeStmt cfg (index cfg P C) (index cfg P L) x₁ x₂)
    ⟨index cfg P C, index cfg P L, .leaf, .leaf, x₁, x₂, π₁, π₂⟩ = true
  ```
  - `aggOK_sat_of_secure` and `aggOK_sat_of_complete` already conclude exactly this.
  - The probe's `LiveIdx` is this field. `cmpToy_liveIdx` (positive) holds for `cmpToy` from
    `runs.1` and `index_eq`, with no new kernel evaluation. `toyCM_not_liveIdx` (negative)
    rules out `toyCM` for every `C`.
  - **Controls.** Move `toyCM` into `Controls/` as the negative of the new field.
    `toy_no_entry` still holds, because the new `live` implies the old one.
  - **Docstring and §5.3 wording for the residual.** "A protocol that special-cases the key of
    a trivially satisfiable layout can still meet `live` without accepting any proof of a hard
    layout; that the benchmark's nodes are provable is shown by the benchmark run (§6.3)."
  - A `live` at `L_chain` itself would close the residual as well. It needs a Lean proof that
    the compiled argument accepts an `L_chain` proof, which is out of reach today (S6a has no
    completeness theorem for whole chains).

### S5-m1: tags are witness, not bound by the contract; binding rests on the leaf layout

- **Declarations.** `Tag`, `child`, `aggOK`, and S5-A4's sentence "a tag is determined by the
  position".
- **Problem.** At the contract level nothing ties a child's tag to its position in the tree.
  Probe `mistag` (`probes/s5/review/TagSlots.lean`, kernel) shows
  `aggOK cfg2 cmpToy xR ⟨vkc2, vkc2, .leaf, .leaf, xN, x0, tapeXN, tape2⟩ = true`. The node
  statement `xN` is accepted as a *leaf* child, at the statement `xR` of the correctly tagged
  node `nwR`. The probe works because the controls' keys coincide. In the benchmark
  `vkC ≠ vkL`, and what keeps a node statement from being proved as a leaf child under `vkL` is
  the statement format of the leaf layout:
  - `Lchain_stmt` (`probes/s5/review/LchainStmt.lean`, kernel, 20 s) shows that `Lchain.rel k x w`
    implies `x₄ = 16` and `x₅ … x₃₁ = 0`, from the public chip alone. A node statement has
    `x₅ … x₇` equal to 24 bytes of `D(vkL)` and `x₈ … x₁₁` equal to `d2`. It is an `L_chain`
    statement only if those 56 hash-output bytes are zero (`node_not_Lchain`).
  - The reverse case, a leaf statement presented as a node child, is excluded by `child`'s
    `d0`/`d1` check. This is contract-level, given that leaf statements do not carry
    `D(vkC)` and `D(vkL)`.

  So `rootOK`'s guarantee, and the tree semantics of §5.4, depend on a property of `L_chain`
  that S5-A4 argues in prose and no control checks. The binding is **benchmark-level**. It is
  adequate for the one benchmark, and every future leaf layout must keep it.
- **Fix (recommended, zero hashes).** Put the tags in the statement as a tag limb:
  `nodeStmt cfg vkC vkL t₁ t₂ x₁ x₂` with `d3 = (t₁.code, t₂.code, 0, 0)`, where
  `Tag.code : Tag → K` maps leaf to 0 and node to 1, and `d4 … d7 = 0`.
  - `aggOK` compares `x'` with `nodeStmt … nw.t₁ nw.t₂ …`.
  - The harness's statement tree uses `(leaf, leaf)` at level 1 and `(node, node)` above.
  - The cost is no compression anywhere. `C_V` adds one linear constraint per tag, because the
    tags are already witness bits that select the keys. The native prover pays nothing.
  - The binding then holds for every leaf layout: by induction from the recomputed root,
    `d2`'s collision resistance fixes each child and `d3` fixes its tag.
  - `nonzero_d3` becomes "a nonzero `d3[2]`".
  - **Alternatives.**
    - Hash the tags into `d2`'s preimage: 514 bytes instead of 512, one more compression per
      node.
    - Derive the tag ("node iff the child's `d0`, `d1` equal the parent's"): zero cells, and
      it still relies on leaf statements not carrying the key digests.
    - Keep tags as witness and instead (i) move `Lchain_stmt` into `Controls/Chain.lean`,
      (ii) replace S5-A4's "a tag is determined by the position" with "a tag is forced by the
      position only through the leaf layout's statement format (`Lchain_stmt`)", and
      (iii) say so in `Tag`'s docstring.

### S5-m2: `complete` ranges over every key, not only indexer keys

- **Declaration.** `RecursionEntry.complete`.
- **Problem.** S5-A1 bounded the key *root*. The key *elements* are still arbitrary, so
  `complete` asks `C` to decode and accept every node that `NARG` accepts under any `vkC` and
  `vkL` with a 32-byte root. Two consequences follow.
  - `S5-M1`'s magic keys must be accepted by `C`. This is harmless.
  - `P.verify`'s work and tape usage on keys that no layout produces must fit `2^k` cells.
    Suppose a verifier reads a loop bound or a query count from a VK element: its queries of
    plain oracles cost no tape, and its openings fill up to 1 MiB, which is about 2^15
    compressions or about 2^28 cells of Merkle hashing. Such a verifier makes `complete`
    unprovable at every class, even though it is honest on every indexer key.
- **Fix.** Either option works.
  - **(a) Docstring.** Add to `complete` and §5.3: "ranges over every accepted node, whatever
    its keys; `verify` must bound its own work and its tape on every key (e.g. reject keys
    outside the format of `VK`)".
  - **(b) Contract.** Restrict `complete` to `nw.vkC = index cfg P C → (∃ L, nw.vkL =
    index cfg P L) → aggOK cfg P x' nw = true → …`. These are the only nodes a benchmark tree
    contains. `sound` is unchanged, and together with S5-M1's `live` it stays non-vacuous.
    This is the reviewer's preference: it removes a burden that buys nothing.

### S5-m3: the statement-tree check has no Lean specification; `rootOK` is a fragment of it

- **Declarations.** `rootOK`, `nodeStmt`, and §6.3 step 5 ("organiser checks `d0, d1` and the
  statement tree").
- **Problem.** The root check that carries the composition is the harness's recomputation of
  the tree, and it is not in Lean. It pins the children through `d2`, the tags by position
  under S5-m1, and the left/right order, and it rejects odd counts. `rootOK` checks only `d0`
  and `d1`. These follow from "root statement = recomputed root" (`rootOK_nodeStmt`), and no
  trusted statement uses `rootOK`. Stage 6b would implement the tree from prose.
- **Fix (≈ 10 trusted lines).**
  ```lean
  /-- One level of the statement tree: adjacent pairs aggregated, `none` on an odd count. -/
  def pairUp (cfg : Cfg) {n : ℕ} (vkC vkL : VKc n) : List Stmt → Option (List Stmt)
    | [] => some []
    | x₁ :: x₂ :: r => (pairUp cfg vkC vkL r).map (nodeStmt cfg vkC vkL x₁ x₂ :: ·)
    | [_] => none
  /-- The root of the statement tree of depth `d` over the leaf statements. -/
  def rootStmt (cfg : Cfg) {n : ℕ} (vkC vkL : VKc n) : ℕ → List Stmt → Option Stmt
    | 0, [x] => some x
    | d + 1, xs => (pairUp cfg vkC vkL xs).bind (rootStmt cfg vkC vkL d)
    | _, _ => none
  ```
  - The root check is `some x = rootStmt cfg (index cfg P C) (index cfg P L) 6 leaves`, for
    N = 64.
  - `rootOK` becomes a Library lemma.
  - Add a KAT: `rootStmt … 2 [x0, x1, x0, x1] = some (nodeStmt … xN xN)`.

### S5-m4: a node child's own `d3 … d7` (its shape) is not pinned by `aggOK`

- **Declarations.** `child`, and the header sentence "a node statement carries no free bits".
- **Problem.** The header sentence holds for the node's *own* statement. A node child need
  only carry the parent's `d0`, `d1` and be accepted under `vkC`. Probe `child_free_d3`
  (`TagSlots.lean`, kernel) has `aggOK` accept a node child `xN3` whose `d3 ≠ 0`, at its
  parent's aggregate statement, although `xN3` is no aggregate statement (`xN3_not_node`).
  Such a child is excluded by two things:
  - one level down, by the child's own `C_V` (`sound` means no witness has a non-aggregate
    statement);
  - for the tree, by the harness's recomputation and `d2`'s collision resistance.

  This is by design and not a defect.
- **Fix (wording).**
  - The header and `child`'s docstring should say: "a node child's statement is pinned by its
    parent's `d2` (collision resistance) and by its own proof (the `C_V` relation), not by
    `aggOK`".
  - DESIGN item (d) should read the same.

### S5-m5: the declared key digests have no harness specification and no control

- **Declarations.** `DeclaredR.digestC` and `DeclaredR.digestL` (S5-A3, S5-A9).
- **Problem.** These fields are trusted data that no trusted statement reads. The harness
  code that compares them does not exist yet. Stage 6b/7 must compare *exactly* the following.
  1. **Recursion key.** Compute `(index S.cfg S.P S.entry.C).digest S.cfg` with the compiled
     indexer from the submitted `S.entry.C`, never from a layout the prover supplies.
  2. **Leaf key.** Compute `(index S.cfg S.P (L_chain 1024)).digest S.cfg`. This uses the
     recursion tree's `n = 2^10`, not the rendered `Lchain` (= `L_chain(16)`).
  3. **Reject on mismatch** with the declared values.
  4. **Use the harness's own values** in the root check and as the key of every node's and
     leaf's `NARG`, never the declared ones.
- **Fix.**
  - In `digestL`'s docstring, write "`D (index cfg P L_chain(2^10))`".
  - Add a Stage 6b/7 negative control: a claim with one flipped bit in `digestC` is rejected,
    and so is a claim whose `digestL` is that of `L_chain(16)`.
  - Optionally, drop the two fields from the *trusted* `DeclaredR`. They are record data, and
    the harness is authoritative for them.

### S5-m6: `decode` may read cells outside `rows × cols`, so `complete` does not place the decoded node in the paid cells

- **Declarations.** `RecursionEntry.decode`, `complete` and their docstrings ("Every accepted
  node is held by a satisfying witness (of at most `2^k` cells)").
- **Problem.** `Table.cell` is total, and `rel` reads only `rows × cols` (`rel_trim_iff`).
  A `decode` can therefore return a node stored in unpaid cells whenever that node is accepted,
  and otherwise fall back to the paid cells. `complete` then holds once *some* accepted node at
  each accepted statement fits `2^k` paid cells, rather than *every* accepted node. `sound` is
  unaffected, because it is universal over unpaid cells too. For the fixed point, "every
  accepted statement has a witness of at most `2^k` cells" is the property that matters, and
  it holds.
- **Fix.** Either option works.
  - **(a) Docstrings.** Write "every accepted node is decoded from a satisfying witness, and
    every accepted statement has a witness of at most `2^k` cells".
  - **(b) Contract.** Trim the witness before decoding in both clauses
    (`decode (C.trim w)`). This moves `Layout.trim`, 3 lines, into the contract.

### S5-m7: the controls cannot tell `vkC` from `vkL`, or a 32-byte root from another length

- **Declarations.** `child` (key selection by tag) and `aggOK` (S5-A1's two conjuncts).
- **Problem.** Every S5 control uses `vkc2` as both keys, because `cmpToy` ignores the layout.
  None uses a root that is not 32 bytes. Two one-line mutants agree with `aggOK` on every node
  of the controls, positive and negative (probe `KeySwap.lean`, `#guard`s,
  `logs/S5/review/KeySwap.log`):
  - `childSwap`, which verifies leaf children under `vkC`;
  - `aggOKNoRoot`, which drops the root-length conjuncts.

  The same holds for `rootOK` with `C` and `L` swapped.
- **Fix (two kernel controls).**
  1. **Distinct keys.** Add a two-leaf node with `vkL := vkK`. `vkK` is the indexer key of
     `cmpToyK2`: VK element `0x1235` with its own honest prover, and the same root as `vkc2`.
     Use the 152-byte tape `tapeK` from the probe. `aggOK` accepts this node and the swap mutant
     rejects it. The cost is one `NARG` run, about 25 s.
  2. **Root length.** A two-leaf node whose `vkC` has a 33-byte root is rejected by `aggOK`
     and accepted by `aggOKNoRoot`. No hash is evaluated.

  A `rootOK` control with `C ≠ L` needs a layout-dependent key: `cmpToyK2` with `VK L`
  depending on `L`.

### S5-m8: `aggOK_sat_of_secure` has no instance

- **Status.** Observation. S5-RESULT's open question 4 stands.
- **Problem.** The docstring of `live` names `aggOK_sat_of_secure` as the submitter's route.
  Its hypotheses, a secure `P` whose honest tapes fit the cap, are jointly satisfied by no
  protocol in the repository. The toy fails them, and so does `toyCM`, whose openings are
  `8·2^29` bytes. The theorem is not vacuous in principle, since a real SNARK satisfies its
  hypotheses, but the repository does not show it.
- **Fix.** None now. The first board-R entry is the instance. Record that in the report's
  §9.

### S5-m9: DESIGN §5.1–§5.3 are stale against the amendments

- **Problem.** DESIGN still has the following, all superseded:
  - §5.1: `D vk := blake2s256 (vk.flatMap …)`, which omits the index root (S3-A8);
  - §5.1–§5.2: `d2 = blake2s256 (x₁ ‖ x₂)`, now `cfg.hash` (S5-A8);
  - §5.2: `aggOK` without the root conjuncts (S5-A1);
  - §5.3: `RecursionEntry` without `live` (S5-A7), and the paragraph "That clause is vacuous …
    The benchmark run is what catches it".
- **Fix.** The orchestrator's fold. Apply S5-M1's wording at the same time.

## Why `sound` + `complete` + `live` force a real circuit (for the report, §9)

Let `Acc = {(x', nw) | aggOK cfg P x' nw = true}`.

1. **Exact image.** `sound` and `complete` together say that, at every statement `x'`,
   `decode` maps the satisfying witnesses of `C` *onto* `Acc(x')`. So `C`'s language at class
   `k` is exactly `{x' | Acc(x') ≠ ∅}`, and each such statement has a witness of at most `2^k`
   cells.
2. **`sound` puts `NARG` in the constraints.** `sound` quantifies over every `w`, and `rel`
   sees only `C`'s constraints. So the claim that `NARG` accepts `decode w`'s tapes must
   *follow from* those constraints. `decode` may compute, but it cannot make an unconstrained
   tape accept. For a concrete hash, Lean establishes "this path climbs to that root" or "this
   challenge is that squeeze" only through constraints that entail the computation.
3. **`complete` admits nothing stronger than `NARG`.** `complete` quantifies over every `nw`,
   so `C` must accept *every* tape `NARG` accepts, including Fiat–Shamir forgeries that no one
   can find. A `C` that checks anything stronger than acceptance, such as the truth of the
   child statement in the trivial verifier, would need a proof that every accepted tape has a
   true statement. That is standard-model knowledge soundness of BLAKE2s, which is not
   provable. A `C` that checks anything weaker breaks `sound`.
4. **The fixed point.** The decoded predicate is therefore `NARG` itself. The fixed point is
   that its trace on two tapes of at most 1 MiB fits `2^k` cells.
5. **`live` rules out degenerate decoders.** `live` makes `Acc ≠ ∅`. Then `Acc` is infinite,
   because the recursion key of a two-leaf node is free (`live_family`). So no constant or
   finitely-valued `decode` passes `complete` (`decode_not_const`, kernel, for every `P`). A
   constant decoder would also need `C` to pin its statement, because `aggOK x' nw₀` forces
   `x' = nodeStmt(nw₀)`.
6. **Where `Secure` stops.** `Secure` constrains `P.verify` only on keys `P.VK L`. On such keys
   an accept-all verifier contradicts round-by-round knowledge soundness with the bounded
   extractor. On other keys it may accept everything (`toyCM`). `live` must therefore name
   indexer keys (S5-M1), or the "trace" of step 4 can be three hashes.
7. **What is not forced, and is the benchmark's job.** `live` does not force `Acc` to contain
   the benchmark's nodes. `decode` need not be efficient. Composition across levels (§5.4) is
   Fiat–Shamir and BCS knowledge soundness in the random-oracle model, applied once per level.
   `rootOK`, the collision resistance of `d2` and the leaf layout's statement format (tags,
   S5-m1) do the bookkeeping.

## Coverage

| Item | Verdict | Evidence |
|---|---|---|
| 1a tags witness, wrong key | contract does not bind; **benchmark-level** (S5-m1) | `mistag` (kernel), `Lchain_stmt`, `node_not_Lchain` (kernel) |
| 1b key propagation | correct direction: node child carries parent's `d0`/`d1`, verified under parent's `vkC`; leaf under parent's `vkL` (digest `d1`) | read `child`, `aggOK_iff`; `node_child_d0/d1` |
| 1c `d2` encoding | injective, fixed 256 + 256 bytes; slot ↔ digest bijective on 32 bytes | `pair_inj` (kernel, `StmtBytes.lean`); `digestToSlot_inj`; Python KAT |
| 1d unused slots | own `d3…d7` pinned (`nonzero_d3`); a node child's are not, by `aggOK` (S5-m4) | `child_free_d3`, `xN3_not_node` (kernel) |
| 1e `rootOK`'s `D` | same `VKc.digest cfg` as `seed`, index root included | read `rootOK`, `seed`, `nodeStmt` |
| 1f `live` degenerate | same-tape nodes harmless (`live_family` uses them); key-degenerate nodes defeat it (**S5-M1**) | `toyCM_*` (kernel) |
| 1g S5-A1 vs `NARG` | consistent; bounds the one key `NARG` does not see | read `NARG`, `aggOK`; mutant gap S5-m7 |
| 2 fixed point | argument above; constant decoder excluded for every `P` | `decode_not_const` (kernel); S5-m2, S5-m6 |
| 3 statements vs code | `aggOK_iff`, `child_iff`, `aggOK_leaves/_nodes`, `rootOK_nodeStmt`, `keys_of_root` faithful; `aggOK_sat_of_complete` instantiated (`toy_sat_via_complete`); `_of_secure` not (S5-m8) | read; S5 controls |
| 3 certificates | static `chips`/`entries` certified; digests declared only (S5-m5); no positive `SubmissionR` exists (§7.3), so `CertificateR.size` is unexercised | read |
| 4 trust/hygiene | imports minimal (`Compile` → `Recursion` → `Certificate`); docstrings on every declaration; `check-hygiene.sh` OK; 45 + 23 code lines (`loc.py`), contract 519 ≤ 850; axioms: 57 declarations within the three (`logs/S5/axioms.log`), audit PASS. `Gate.lean`'s `--computable` table is still v0.3's (S5-A9, Stage 6b). `rootOK` belongs in Library once `rootStmt` exists (S5-m3). `Declared` does not duplicate gate data | `scripts/check-hygiene.sh`, `scripts/loc.py` |
| 5 Python | independent 10-line reproduction from DESIGN §5.1 and the `Compile.lean` header matches `xN`, `xR` and `D(vkc2)` | `node_stmt_indep.py`, `logs/S5/review/node_stmt_indep.log` |

## Probes

All Lean probes were run with `lake env lean` against the built `.olean` files. The only
imported files the golf agent edits are `Library/Recursion.lean` and, through it,
`Controls/RecursionData.lean`. Their `.olean` files were current when the probes ran
(`lake build --no-build`). Every theorem is within `propext`, `Classical.choice` and
`Quot.sound`.

| File | What | Cost (wall, RSS) | Log |
|---|---|---|---|
| `probes/s5/review/MagicKey.lean` | S5-M1: `toyCM` secure, `live`, no indexer-key node, `aggOK` characterisation, `LiveIdx` fix (positive on `cmpToy`, negative on `toyCM`) | 21 s, 2.7 GB | `MagicKey.log` |
| `probes/s5/review/TagSlots.lean` | S5-m1 `mistag`, S5-m4 `child_free_d3`, `xN3_not_node`; two `decide +kernel` runs | 62 s, 6.1 GB | `TagSlots.log` |
| `probes/s5/review/LchainStmt.lean` | `Lchain_stmt` (`x₄ = 16`, `x₅…x₃₁ = 0`), `node_not_Lchain` | 20 s, 2.7 GB | `LchainStmt.log` |
| `probes/s5/review/LiveFamily.lean` | `live_family`, `decode_not_const` (every `P`) | 6 s, 2.6 GB | `LiveFamily.log` |
| `probes/s5/review/StmtBytes.lean` | `stmtBytes_inj`, `pair_inj` | 6 s, 2.6 GB | `StmtBytes.log` |
| `probes/s5/review/KeySwap.lean` | S5-m7 mutants `childSwap`, `aggOKNoRoot` survive the controls; `vkK` and 33-byte-root nodes kill them (`#guard`) | 7 s, 2.6 GB | `KeySwap.log` |
| `probes/s5/review/node_stmt_indep.py` | item 5, `python3 -I … Controls/RecursionData.lean` | < 1 s | `node_stmt_indep.log` |

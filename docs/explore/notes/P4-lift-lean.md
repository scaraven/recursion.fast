# P4: the lift in Lean (T1 Theorem 4.1) and the deterministic core of deferral

Probe author: Lean implementer agent, 2026-10-20. Code: `RecursionFast/Explore/Lift/*.lean`
(`Basic`, `WS`, `Tree`, `Deferral`, root `All`), imported by `RecursionFast/Explore.lean`. Every
claim is **kernel** unless marked **paper** or **estimate**. Namespace
`RecursionFast.Explore.Lift` is omitted below.

## Conclusions

1. **T1 Theorem 4.1 holds, in the strongest abstract form I could state** (`lift`, Basic). Take any
   statement type `X`, any flat argument `V₀ : X → Proof → OProg Bool` with a knowledge state of
   error `ε` (the contract's three laws, word for word, `GKState`) for any relation whose witnesses
   are flat shapes of the digest `stmt x`, and any query bound `qV` of `V₀`. Then the lifted
   verifier `liftV` satisfies `KSRel` (P1's relativized knowledge soundness) with **the same `ε` and
   the same `qV`**. Its knowledge state *is* `V₀`'s potential (`liftState_μ`, by `rfl`). On a flat
   frame, `liftV` **is the program `V₀ x π₀`** (`liftV_snark`), so it asks exactly `V₀`'s queries
   in the same order. On a witness-sending frame it asks nothing (`queries_liftV_ws`). It is not
   recursive: it never runs itself or `V₀` on a sub-proof. Its extractor turns a flat proof into the
   node witness whose two children are **witness-sending proofs of the two subtrees**, accepted with
   no query on every log, or into the leaf witness of a one-leaf tree (`halves`, `relL_halves`).
2. **No side condition with a cap-free witness-sending format** (`lift_free`, WS). **For the runner's
   own statement** (the `2^d` chain starts and lengths in the clear, digest = `treeRoot` of their
   leaf statements), every knowledge state of `V₀` gives the lift, whatever its witness type and
   extractor (`lift_runner`, Tree). The bridge is kernel-checked: the perfect shape over `2^d`
   chains folds to the runner's `treeRoot` (`perfect_root`, through `treeRoot_append`).
3. **With the library's witness-sending format the lift is limited by `proofCap`, not by anything
   in the relativized definition.** `WitnessSending.check` caps every child proof at `2^20` bytes,
   and a shape's proof has `136 · #leaves − 88` bytes (`size_wsProof`). The extractor's children
   are therefore accepted for perfect trees of up to `2^14` leaves (`lift_runner_ws`, `d ≤ 14`).
   At `2^15` leaves a half's child proof exceeds `proofCap` (`not_halvesFit_perfect`). v3's ranked
   tree (`r = 8`) is far inside the limit. A larger cap, or the cap-free format, removes it (item 2).
4. **Deferral, deterministic core** (`reask`, `flip_reask`, Deferral). Let the extractor be
   *decoding*: on a node proof it returns nothing or the node witness of exactly the committed
   children. Let the parent accept on a log `L`, and let some committed child read a query `q` on
   `L`. If the log without `q` has potential below `1`, the parent reads `q` too. The oracle-flip form
   (T1 Theorem 2.2 (a), (b), (d)) is: the parent accepts under `O[q ↦ a]`; a true-oracle log covers
   its queries, below potential `1`; a committed child is rejected on that log (answer-sensitive).
   Then the parent asks `q`. The theorem has teeth: it re-derives P1's `lazy_W1_no_kstate`
   (`lazy_W1_no_kstate'`).
5. **What the relativized requirement buys, given 1–4** (**paper**, restating T1 §0 with kernel
   backing). Any flat SNARK for the runner's statement, with a 32-byte-per-leaf header, already
   meets `KSRel` at its own error and query count, and never recurses. A recursive design with a
   decoding extractor must re-ask every query its children's verification reads. So the
   requirement does not force recursion, and it taxes the designs that do recurse.

## Theorems

| Lean name | File | Plain-words meaning |
|---|---|---|
| `GKState`, `KState.toG`, `GKState.toKState`, `GKState.map` | Basic | The contract's `KState` with the statement and witness types open; at `Digest`, `Wit` it is the contract's. `map`: post-composing the extractor with a witness map that carries `R` into `R'` keeps the potential. |
| `Flat` | Basic | The flat relation: the shape folds (`leafStmt (chainEnd s n) n` at leaves, `nodeStmt` at nodes) to `c`, and every chain is within `chainCap`. This is exactly `compose_flat`'s conclusion. |
| `WSys`, `WSys.HalvesFit` | Basic | A witness-sending system: an oracle-free `chk`, sound (accepted proofs decode to the relation's clauses with accepted children), complete on shapes that fit its size predicate `Fits`. |
| `LFrame`, `LCodec`, `liftV`, `liftE`, `halves`, `wrap`, `rewrap` | Basic | The lifted format (`ws π` or `snark x π₀`, over P1's abstract `Codec`), verifier and extractor. |
| `liftV_ws`, **`liftV_snark`** | Basic | On a witness-sending frame the lift is `ret (chk c π)`. On a flat frame it is `V₀ x π₀` when `stmt x = c`, else `ret false`. Both are program equalities. |
| `relL_halves`, `relL_rewrap` | Basic | The extractor's witnesses satisfy the relativized relation `RelL` on **every** log. |
| **`liftState`**, `liftState_μ` | Basic | A `GKState` for `V₀` gives a `KStateRel` for the lift with the same potential and error. |
| `queries_liftV_ws`, `queries_liftV_snark`, `queries_liftV_le` | Basic | No query on witness-sending frames. Exactly `V₀`'s queries on flat frames. At most `qV` everywhere. |
| **`lift`** | Basic | Headline: `KSRel (liftV …) (liftE …) ε qV`, the lift is `V₀` on flat frames, and no query on witness-sending frames. |
| `lift_paper` | Basic | The same through `Library/PaperTheorem.lean`: in a game of `n ≤ logCap` lazily sampled queries, P[lift accepts ∧ no `RelL` witness on the final log] ≤ `n · ε`. |
| `flatV`, `flatE`, `flatState` | Basic | Non-vacuity of the hypothesis: the flat check (decide `Flat` on a statement carrying the shape; no query) has a `GKState` at `0`. |
| `wsProof`, `WSFits`, `check_wsProof`, `ws_sound`, `wsSys` | WS | The library's format as a `WSys`: `check` accepts `wsProof t` for every fitting flat shape. |
| `size_wsProof` | WS | A shape's library proof has `136 · #leaves − 88` bytes. |
| `wsFits_of_length_le`, `not_wsFits`, `SmallHalves`, `halvesFit_of_small`, **`lift_ws`** | WS | Every shape with at most 7711 leaves fits. A child with more than 7710 leaves does not. The lift over the library format, for halves of at most 7711 leaves. |
| `witSub`, `freeChk`, `freeEnc`, `freeChk_sound`, `freeChk_freeEnc`, `freeSys`, `witCodec` | WS | The cap-free witness-sending format over an abstract `Codec Wit`. Every shape fits. A codec exists (`Codec.unary`). |
| **`lift_free`** | WS | The lift with no side condition. |
| `lift_flat_free`, `lift_flat_accepts` | WS | Non-vacuity: the lifted flat check is `KSRel` at `ε = 0`, `qV = 0`, and accepts the flat frame of every flat statement under every oracle. |
| `treeLevel_append`, `iterate_pow_eq`, **`treeRoot_append`** | Tree | `d` levels reduce `2^d` digests to their root. The runner's root of `2^(d+1)` digests is `nodeStmt` of its two halves' roots. |
| `Shape.perfect`, `perfect_leaves`, **`perfect_root`** | Tree | The perfect shape over `2^d` chains (split in the middle at every level) has those chains as leaves and folds to `treeRoot (ls.map leafDigest)`. |
| `RunnerFlat`, `flat_perfect`, `runnerE`, **`lift_runner`** | Tree | The runner's flat relation (starts in the clear, digest = `treeRoot`). Any `GKState` for it lifts. |
| `wsFits_perfect`, `halvesFit_perfect`, `not_halvesFit_perfect`, **`lift_runner_ws`** | Tree | Over the library format: perfect shapes of depth ≤ 13 fit, so the lift holds for `d ≤ 14`. At `d = 15` the halves do not fit. |
| `path`, `eraseKey`, `mem_of_runLog` | Deferral | A program's path on a log. Log coverage (T1 Lemma 2.1): an accepted run's path lies in the log's keys. |
| `runLog_eraseKey`, `runLog_eraseKey_of_mem` | Deferral | Locality. Erasing a query off the path changes nothing. Erasing one on the path makes the run fail (`none`). |
| `Decoding`, **`reask`** | Deferral | Log form of "the parent re-asks". |
| `run_congr`, **`flip_reask`** | Deferral | Oracle-flip form (T1 Theorem 2.2 (a), (b), (d)). `run_congr`: verdict and queries depend only on the asked points. |
| `dChildren`, `dE_decoding`, `lazy_W1_no_kstate'` | Deferral | P1's natural extractor is decoding. `reask` re-derives that the lazy parent over `W1` has no relativized knowledge state. |

The signatures of `lift`, `lift_free`, `lift_runner`, `lift_runner_ws`, `reask`, `flip_reask` and
`liftState` were printed with `#check` (scratch file `P4Check.lean`). For example:

```
lift : (C : LCodec X) → GKState R₀ V₀ E₀ ε → (∀ x t, R₀ x t → Flat (stmt x) t ∧ W.HalvesFit t) →
  (∀ H x π₀, ((V₀ x π₀).queries H).length ≤ qV) →
  KSRel (liftV C W stmt V₀) (liftE C W E₀) ε qV ∧
  (∀ c x π₀, stmt x = c → liftV C W stmt V₀ c (C.enc (.snark x π₀)) = V₀ x π₀) ∧
  (∀ H c π, (liftV C W stmt V₀ c (wrap C π)).queries H = [])
```

## `#print axioms`

`timeout 600 lake env lean <scratchpad>/P4Axioms.lean`, output in `logs/p4-axioms.log`. Every
declaration depends only on `propext`, `Classical.choice`, `Quot.sound`. A grep of the probe finds
no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `csimp` or `axiom`.

```
'RecursionFast.KState.toG' depends on axioms: [propext, Classical.choice, Quot.sound]
'GKState.toKState' depends on axioms: [propext, Classical.choice, Quot.sound]
'GKState.map' depends on axioms: [propext, Classical.choice, Quot.sound]
'liftV_ws' depends on axioms: [propext, Quot.sound]
'liftV_snark' depends on axioms: [propext, Quot.sound]
'relL_halves' depends on axioms: [propext, Quot.sound]
'relL_rewrap' depends on axioms: [propext, Quot.sound]
'liftState' depends on axioms: [propext, Classical.choice, Quot.sound]
'queries_liftV_ws' depends on axioms: [propext, Quot.sound]
'queries_liftV_snark' depends on axioms: [propext, Quot.sound]
'queries_liftV_le' depends on axioms: [propext, Quot.sound]
'lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'lift_paper' depends on axioms: [propext, Classical.choice, Quot.sound]
'flatState' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_wsProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'ws_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'wsSys' depends on axioms: [propext, Classical.choice, Quot.sound]
'size_wsProof' depends on axioms: [propext, Quot.sound]
'wsFits_of_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'not_wsFits' depends on axioms: [propext, Quot.sound]
'halvesFit_of_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'lift_ws' depends on axioms: [propext, Classical.choice, Quot.sound]
'freeChk_sound' depends on axioms: [propext, Quot.sound]
'freeChk_freeEnc' depends on axioms: [propext, Quot.sound]
'freeSys' depends on axioms: [propext, Quot.sound]
'lift_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'lift_flat_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'treeLevel_append' depends on axioms: [propext, Quot.sound]
'iterate_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'treeRoot_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'perfect_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'perfect_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'flat_perfect' depends on axioms: [propext, Classical.choice, Quot.sound]
'lift_runner' depends on axioms: [propext, Classical.choice, Quot.sound]
'wsFits_perfect' depends on axioms: [propext, Classical.choice, Quot.sound]
'halvesFit_perfect' depends on axioms: [propext, Classical.choice, Quot.sound]
'not_halvesFit_perfect' depends on axioms: [propext, Classical.choice, Quot.sound]
'lift_runner_ws' depends on axioms: [propext, Classical.choice, Quot.sound]
'mem_of_runLog' depends on axioms: [propext, Quot.sound]
'runLog_eraseKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'runLog_eraseKey_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'reask' depends on axioms: [propext, Classical.choice, Quot.sound]
'run_congr' depends on axioms: [propext]
'flip_reask' depends on axioms: [propext, Classical.choice, Quot.sound]
'dE_decoding' depends on axioms: [propext]
'lazy_W1_no_kstate'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(Names other than the first are in `RecursionFast.Explore.Lift`.)

## Check times (**measured**)

- Fresh `timeout 900 lake build RecursionFast.Explore.Lift.All` after deleting the probe's oleans:
  17.0 s wall. Per module: Basic 3.0 s, WS 3.8 s, Tree 3.6 s, Deferral 3.4 s, All 2.0 s
  (`logs/p4-build.log`). The contract, library and P1 modules were prebuilt. This worktree had not
  built `Contract/Tree` or `Library/Oracle`, so I built them once, with targeted builds of 1.6 s and
  1.8 s.
- `timeout 600 lake env lean` per file: Basic 5.50 s, WS 6.06 s, Tree 5.96 s, Deferral 6.00 s
  (`logs/p4-check-times.log`). `All.lean`, which only imports, takes 5.22 s, so each file elaborates
  in under 1 s. The rest is loading imports.
- Combined import with the other agents' modules (`Attested.All`, `TwoChannel.Backdoor`,
  Relativized): no name clash.

## Abstractions and deviations

1. **Statement type generalised (`GKState`).** The contract's `KState` fixes statements to `Digest`
   and witnesses to `Wit`. A flat argument's statement must carry the leaves (T1 §7: "do not state
   the lift with the starts outside the public input"), so `GKState` keeps the three laws verbatim
   over any `X`, `W`. `KState.toG` and `GKState.toKState` show that nothing else changed. The lift
   is generic in `X` and `stmt : X → Digest`. Two cases are covered:
   - T1's form, starts in the clear: `X = Digest × List (Digest × ℕ)` with `RunnerFlat`
     (`lift_runner`), or `X = Digest × Shape` (`flatState`).
   - A knowledge-sound flat argument whose witness hides the starts: `X = Digest`, `stmt = id`,
     `E₀` returning shapes.

   The hypothesis is a knowledge state for **any** relation `R₀` that implies `Flat`. So `lift` needs
   only soundness of `V₀` for the flat statement, which makes the theorem stronger.
2. **Tree shape.** The general theorem uses P1's `Shape`, an arbitrary binary tree of
   `(start, length)` leaves, folded with `leafStmt`/`nodeStmt`. "The two halves" are its two
   subtrees. The runner's `treeRoot` is connected for the **perfect** shape over `2^d` leaves,
   split in the middle at every level (`Shape.perfect`, `perfect_root`). Leaves carry per-leaf
   lengths, so a fixed length `n` is the special case of all lengths equal.
3. **The witness-sending branch is a tagged frame.** A lifted proof is `C.enc (.ws π)` or
   `C.enc (.snark x π₀)`. Raw library witness-sending bytes are not lifted proofs. The extractor
   therefore re-wraps the children it returns (`rewrap`, `halves`), so that the lift accepts them
   through its own decoder. Without the tag, a library node's children are raw bytes that the
   lift's decoder does not read as witness-sending proofs, and the relativized node clause fails.
4. **The library format's cap is a real limit, stated explicitly.** The brief says "children are
   witness-sending proofs of the two halves (so they are accepted with zero queries on every log)".
   With `WitnessSending.check` that holds only when the halves fit `proofCap`
   (`WSys.HalvesFit wsSys`). `lift_runner_ws` carries `d ≤ 14`, and `lift_ws` carries `SmallHalves`.
   `not_halvesFit_perfect` shows the fit condition fails at `d = 15`. This is not a
   counterexample to the lift itself: `lift_free` and `lift_runner` have no condition. What is kernel
   at `d = 15` is only that `WSys.HalvesFit wsSys` fails. That `check` then rejects the halves is
   read off `decodeWit`, which rejects a child longer than `proofCap`, and is **not** kernel-checked.
   Under a relation that also caps child proofs at `proofCap`, as v3's `Submission.Vb` does, the
   halves themselves (`136 · 2^(d−1) − 88` bytes) must fit too, so `d ≤ 13` (**paper**; `RelL` has
   no such cap).
5. **"Never recurses"** means that `liftV` is a non-recursive definition. It calls neither itself
   nor `V₀` on a sub-proof. The witness-sending check recurses over its own proof's children, as
   the library's does; that recursion is oracle-free decoding.
6. **Codecs.** P1's `Codec`, with no sub-proofs for `LFrame` because nothing recurses. Non-vacuity
   uses `Codec.unary`. It needs `Encodable Shape`, obtained via `deriving Countable` and
   `Encodable.ofCountable`, which is noncomputable. Only the non-vacuity theorems use it.
7. **Deferral.** `Decoding` is positional: `children π = some (c₁, c₂, π₁, π₂)` forces `E` to return
   `none` or exactly `node c₁ c₂ π₁ π₂`. This removes T1 §2.2 (d)'s assumption
   `(c₁', c₂') = (c₁, c₂)` (no `nodeStmt` collision), because the extractor returns positions, not
   statements. P1's `dE` is decoding (`dE_decoding`). Erasure removes **every** entry for `q`
   (`List.filter`). `reask`'s potential hypothesis is on the erased log. `flip_reask`'s is on the
   true log, and its hypothesis `hacc` (acceptance under the flipped oracle) is what completeness of
   the honest proof built under `O[q ↦ a]` provides.

## What this does not show

- **Completeness of the lift for the relativized relation** (**paper, sketched**). The honest leaf
  prover sends `wrap (W.enc (leaf s n))`, accepted with no query under every oracle. The honest
  node prover reads the two children's shapes and runs `V₀`'s prover on the combined statement. A
  witness-sending child gives its shape by decoding; a flat child gives it in the clear. This is
  complete for children whose clear statements are true, in particular every honestly produced
  child. The open case is an adversarially chosen child that `V₀` accepted with a false clear
  shape. Whether the honest prover's output is still accepted then depends on `V₀`, so perfect
  completeness over every oracle function is not implied. Over a random oracle, the adaptive
  failure probability is at most `V₀`'s completeness error plus its soundness bound
  `(Q + qV₀) · ε`. By contrast, concatenation and deferral have perfectly complete identity node
  provers (P1 `concatV_node_run`). Any completeness clause for `RelO` in D1/D2 must be adaptive and
  probabilistic, as in [BCG] Def. 3.12, or the lift is not an entry.
- **That a succinct `V₀` exists.** The only Lean instance is the non-succinct flat check
  (`flatState`). Existence of a succinct one is **paper** (Micali/BCS, and spartan-chain at `d = 0`).
- **The extractor's cost.** `liftE` builds the halves' witness-sending proofs, which contain every
  subtree digest. That is about `Σ nᵢ` chain compressions plus `2^d` node hashes. At `r = 8` and
  `n = 2^14` this is `2^22` compressions, about `2^34` RISC-V steps against `extractorBudget ≥ 2^40`
  (**estimate**, at about `2^12` steps per compression). No image is built.
- **The probabilistic half of deferral.** T1 §2.2 (c) writes the two-run adversary as one `OProg`
  game and applies `KStateRel.paper`. Only the deterministic core and `KStateRel.paper` itself are
  kernel-checked here.

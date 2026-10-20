# P1: Lean probes for the relativized relation

Probe author: Lean implementer agent, 2026-10-20. Code: `RecursionFast/Explore/Relativized/*.lean`,
root `RecursionFast/Explore.lean`. All claims below are **kernel** unless marked otherwise.

## Conclusions

1. **Composition becomes a theorem.** With the node clause read from the log (`RelL`), one
   relativized knowledge state extracts the whole tree from one log, to every depth, with no extra
   error. In probability (lazily sampled oracle), the root verifier accepts while some level fails
   to extract with probability at most `(Q + qV) · ε` (`paper_tree`). v3's `Rel Vb` does not give
   this. The certified backdoor of `Controls/Backdoor.lean` has a v3 knowledge state, yet on a log
   of potential `0` it accepts a node proof that cannot be extracted to depth 2 (`V3.v3_no_compose`).
2. **The requirement does not force compression.** A concatenating verifier (a node proof is the
   two child proofs in the clear, checked by the same verifier) gets a relativized knowledge state
   from a leaf-only state, with the same potential and error (`concatState`). Witness-sending has
   one at potential `0` and error `0` (`ws_ksRel`).
3. **Relativization alone does not close O-25.** The ported backdoor is relativized-sound at
   `errorCap` with one query, and accepts a 32-byte magic proof of every statement under the
   deployed `blake2sOracle` (`Backdoor.backdoor`). What could close it is how the oracle is
   deployed (a secret oracle `V` cannot evaluate). That is a **paper** argument, outside these
   probes.
4. **A parent must re-ask its children's queries.**
   - A lazy parent judges children against answers the prover supplies, without asking the oracle.
     It has no relativized knowledge state with its natural extractor (`lazy_no_kstate`). Every
     extractor that would certify it must output BLAKE2s collisions (`lazy_extractor_collides`).
   - A parent that first re-asks every supplied answer is sound, with the child's potential
     (`deferState`). It makes `|Q|` oracle queries per node, so it saves only local work.

## Theorems

Build: `timeout 900 lake build RecursionFastExplore`, 9.1–12.9 s wall with the contract and
library prebuilt (**measured**, `logs/p1-explore-build.log`, `logs/p1-explore-build-fresh.log`).
Per file, fresh: Defs 3.6 s, Concat 3.1 s, Backdoor 3.1 s, Compose 3.2 s, Lazy 3.3 s, root 2.0 s.
Warming the library the probes import (`Library.WitnessSending`, `Controls.Backdoor`) took 16 s
(`logs/p1-warm-library.log`). Namespace `RecursionFast.Explore.Relativized` is omitted below.

| Lean name | File | What it shows |
|---|---|---|
| `RelWith`, `rel_eq` | Defs | The relation with the node clause's child condition left open. v3's `Rel Vb` is `RelWith (Vb · · = true)`. |
| `RelL`, `relL_leaf`, `relL_node` | Defs | The relativized relation. Leaf clause as in `Rel`. Node: `c = nodeStmt c₁ c₂` and both children accepted by `V` reading the same log. |
| `RelH`, `runLog_run`, `RelL.toH` | Defs | The relation under an oracle function `H`. A verdict read from a log whose every entry agrees with `H` is the verdict under `H`. So a `RelL V L` witness is a `RelH V H` witness. |
| `Agrees`, `runLog_of_agrees` | Defs | Monotonicity: if each entry of `Q` is `L`'s first answer to its query, every verdict read from `Q` is the same when read from `L`. |
| `KStateRel`, `KSRel` | Defs | `KState` with `final` concluding `∃ w, E c π L = some w ∧ RelL V L c w`; `KSRel` is `KS` with it. |
| `KStateRel.ofKState`, `.zero`, `.ofBool` | Defs | Builders. `ofBool` turns good/bad predicates into a 0/1 potential, through the library's `KState.ofBool`. |
| `KStateRel.toKState`, `KStateRel.paper_of`, `KStateRel.paper` | Defs | The library's paper theorem (`Library/PaperTheorem.lean`) carries over unchanged. Accepting without a `RelL` witness on the final log has probability at most `n · ε` for games of `n ≤ logCap` queries. |
| `Codec`, `Codec.unary`, `CFrame`, `DFrame` | Defs | The abstract byte format (see Abstractions), and a proof that one exists for every encodable frame type. |
| `TreeOK`, **`compose`** | Compose | Below potential 1, every proof `V` accepts on `L` is extracted on `L` to every depth `d`. |
| **`paper_tree`** | Compose | Whole-tree soundness: P[root accepted ∧ tree not extracted to some depth] ≤ `n · ε`. |
| `Shape`, `extract`, `extract_root`, **`compose_flat`** | Compose | Flat witness: when the extractor's walk ends in leaves, `nodeStmt` folds their `leafStmt`s to the root, and every chain is within `chainCap`. |
| **`V3.v3_no_compose`** | Compose | v3 does not compose. On a log of potential 0, the certified backdoor accepts `encode (node c₀ c₀ (magic c₀) (magic c₀))`, but the tree is not extracted to depth 2 (`decode (magic c₀) = none`). |
| `concatV`, `concatE`, `concatV_leaf`, `concatV_node` | Concat | The concatenating verifier over any leaf verifier, and its extractor. |
| **`concatState`**, `concatState_μ` | Concat | A `KState LeafRel Vl El ε` gives a `KStateRel (concatV C Vl) (concatE C El) ε` with the same `μ`. |
| `concatV_node_run` | Concat | The honest node prover is the identity: a node encoding is accepted under `H` exactly when it is a `RelH` witness. |
| `wsState`, **`ws_ksRel`** | Concat | The real witness-sending verifier: `KSRel` at `μ = 0`, `ε = 0`, `qV = 0`. No abstraction. |
| `Backdoor.check`, `Backdoor.V`, `Backdoor.kstate` | Backdoor | The ported backdoor. Its `KStateRel` at `errorCap` is potential 1 exactly on logs that answer `q0` with `trigger`. |
| `Backdoor.complete` | Backdoor | The honest proof of every fitting `RelH V H` witness is accepted under every `H`. |
| **`Backdoor.backdoor`** | Backdoor | `KSRel V E errorCap 1`, and `(V c (magic c)).run blake2sOracle = true` with a 32-byte proof, for every `c`. |
| `lazyV`, `deferV`, `checkAll`, `dE`, `lift`, `nodeProof` | Lazy | The lazy parent and the re-asking (deferral) parent over a base verifier `Vc`, with their natural extractor. |
| **`lazy_no_kstate`** | Lazy | If `Vc` queries on every input and two base proofs are accepted on some `Q`, there is no `KStateRel (lazyV C Vc) (dE C E) ε` at any `ε`. |
| **`lazy_extractor_collides`**, `Collides`, `IsLazyNode`, `isLazyNode_of_empty` | Lazy | Under the same hypotheses, any extractor of a `KStateRel` for `lazyV` returns on the empty log a leaf witness of `nodeStmt c₁ c₂`, or a node witness `(d₁, d₂)` with `nodeStmt d₁ d₂ = nodeStmt c₁ c₂` whose children are lazy node statements. For leaf-statement `c₁`, every such output is a BLAKE2s collision between distinct inputs. |
| `kstate_of_leaf_surjective` | Lazy | If every digest were `leafStmt (chainEnd s 0) 0` for some `s`, every verifier would have a `KStateRel` at error 0. This is why `∀ E, ¬ KStateRel` cannot be proved (see Deviations). |
| `runLog_checkAll`, `queries_checkAll`, `queries_defer` | Lazy | Re-asking passes only if `Q` agrees with the log. A deferral node asks at most `|Q|` queries. |
| **`deferState`** | Lazy | A `KStateRel Vc E ε` gives a `KStateRel (deferV C Vc) (dE C E) ε` with the same `μ`. |
| `W1`, `w1State`, `W1_accepts`, `lazy_W1_no_kstate`, `lazy_W1_collides`, `lazy_unary_no_kstate`, `defer_W1` | Lazy | Instance: `W1` is witness-sending with one dummy query, sound at `μ = 0`. Over `W1` the lazy parent is unsound; that also holds with `Codec.unary`, so the result is not vacuous. The deferral parent is sound at `μ = 0`. |

## `#print axioms`

Output of `lake env lean <scratchpad>/P1Axioms.lean` (`logs/p1-axioms.log`). Every declaration
depends only on `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `native_decide`,
`implemented_by`, `extern` or `csimp` appears in the probes.

```
'runLog_run' depends on axioms: [propext, Quot.sound]
'RelL.toH' depends on axioms: [propext, Quot.sound]
'runLog_of_agrees' depends on axioms: [propext, Quot.sound]
'KStateRel.ofBool' depends on axioms: [propext, Classical.choice, Quot.sound]
'KStateRel.paper_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KStateRel.paper' depends on axioms: [propext, Classical.choice, Quot.sound]
'paper_tree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Codec.unary' depends on axioms: [propext, Classical.choice, Quot.sound]
'compose' depends on axioms: [propext, Classical.choice, Quot.sound]
'extract_root' depends on axioms: [propext, Quot.sound]
'compose_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
'V3.v3_no_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
'concatState' depends on axioms: [propext, Classical.choice, Quot.sound]
'concatV_node_run' depends on axioms: [propext, Quot.sound]
'wsState' depends on axioms: [propext, Classical.choice, Quot.sound]
'ws_ksRel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Backdoor.kstate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Backdoor.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Backdoor.backdoor' depends on axioms: [propext, Classical.choice, Quot.sound]
'lazy_no_kstate' depends on axioms: [propext, Classical.choice, Quot.sound]
'lazy_extractor_collides' depends on axioms: [propext, Classical.choice, Quot.sound]
'lazy_W1_no_kstate' depends on axioms: [propext, Classical.choice, Quot.sound]
'lazy_W1_collides' depends on axioms: [propext, Classical.choice, Quot.sound]
'lazy_unary_no_kstate' depends on axioms: [propext, Classical.choice, Quot.sound]
'runLog_checkAll' depends on axioms: [propext, Classical.choice, Quot.sound]
'queries_defer' depends on axioms: [propext, Classical.choice, Quot.sound]
'deferState' depends on axioms: [propext, Classical.choice, Quot.sound]
'w1State' depends on axioms: [propext, Classical.choice, Quot.sound]
'defer_W1' depends on axioms: [propext, Classical.choice, Quot.sound]
'kstate_of_leaf_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Abstractions, and why

- **Byte codecs for the generic constructions** (`Codec F sub`, Defs). Concat and Lazy take their
  byte format as a structure: an encoder, a decoder that inverts it, and sub-proofs of a decoded
  frame strictly shorter than the proof. Without the last property the recursive verifiers do not
  terminate. This keeps byte parsing out of the probes. To show the hypotheses can be met,
  `Codec.unary` builds a codec for any `Encodable` frame type: a run of zero bytes whose length
  pairs the frame's code with one more than the total size of its sub-proofs. The proofs are
  astronomically long, which only matters for non-vacuity. `CFrame` and `DFrame` are given
  `Encodable` instances, and `lazy_unary_no_kstate` instantiates (a) with the unary codec.
  `wsState`, the backdoor and `v3_no_compose` use the real witness-sending byte format, with no
  abstraction.
- **`OProg.bind`** is copied verbatim from the rules worktree's contract (V3-S2R-A2), because this
  worktree's contract lacks it. Delete the copy when the branch picks up the contract that has it.
- **Probability** is the library's lazy-sampling model (`Library/PaperTheorem.lean`). The step to a
  uniformly random function and to randomised adversaries remains on **paper**, as in v3.

## Deviations from the brief

1. **Item 5(a) as stated is not provable; corrected statement proved.** The brief asked for
   `¬ Nonempty (KStateRel lazyV E ε)` for every extractor `E` (or for `ε < 1`). The kernel cannot
   prove this, because whether such an extractor exists depends on properties of BLAKE2s.
   `kstate_of_leaf_surjective` makes this precise: if `s ↦ leafStmt (chainEnd s 0) 0` were
   surjective, every verifier, the lazy one included, would have a `KStateRel` at error 0. This is
   the obstruction behind the library's `acceptAll_kstate_iff`. No counterexample to the stated
   form is known either: refuting it would need a BLAKE2s preimage fact. Two statements are proved
   instead:
   - `lazy_no_kstate`: no state at any error for the natural extractor `dE`, the one that reads the
     node off the proof;
   - `lazy_extractor_collides`: every extractor of a state outputs, on the empty log, a preimage of
     `nodeStmt c₁ c₂` that is a BLAKE2s collision (`Collides`).
2. **Backdoor port: children are judged by `V` itself, with the same oracle answer.** The control's
   `check` accepts magic children whatever the oracle answers. That is exactly what
   `v3_no_compose` breaks, and under `RelL` the natural extractor would have no state. The port
   threads the answer `a` to `q0` through the recursion (`check a`), so a child is accepted on a
   log exactly when `V` accepts it there. The node clause is then the relativized one, and the
   magic branch fires only on the deployment answer.
3. **`TreeOK` is `RelWith (TreeOK E L d)`.** The relation's clauses are shared through `RelWith`
   instead of being duplicated. The depth-`(d+1)` clause is literally the brief's: the leaf clause,
   or a node with `c = nodeStmt c₁ c₂` and both children `TreeOK` at depth `d`.
4. **Consistency condition of `runLog_run`:** `∀ e ∈ L, H e.1 = e.2`, so every entry agrees with
   `H`. It holds for the log of any run against `H`. The exact condition is agreement on first
   answers only (`firstAns`). The weaker form is not needed here.
5. **Extras beyond the brief:** `paper_tree` and `KStateRel.paper` tie `compose` to the probability
   bound; `V3.v3_no_compose` is a kernel version of the docstring's explanation of why v3 does not
   compose; `concatV_node_run` and `Backdoor.complete` cover completeness.

## What the probes do not show

- Any bound on the cost of the extracted tree. `compose_flat` only applies when the extractor's
  walk ends. A cyclic proof (a child equal to its parent) would need `c = nodeStmt c c'`, a BLAKE2s
  fixed point, which is not excluded.
- That a **compressing** relativized verifier exists. The concatenation and deferral verifiers are
  both non-compressing in oracle queries: the root asks every leaf's queries. That is consistent
  with the impossibility result, and whether the result applies to this relation is item 2 of the
  brief (paper).
- Anything about deploying the oracle (D2/D4): the probes fix no deployment.

# Composition over the stream's comb (closes design §2.4 / §6.2 open item)

File: `RecursionFast/Explore/CombCompose.lean` (295 lines, not imported by `RecursionFast.lean`).
Checked with `lake env lean` through the capped runner: 5.2 s wall, no error, no `sorry`
(**measured**, `logs/audit/comb-2.log`). Axioms of `combWalk`, `comb_compose`, `comb_prob`,
`card_combPaths`: `propext, Classical.choice, Quot.sound` (`logs/audit/comb-axioms.log`).

## Shape checked against the harness

`harness/rfh/bench.py` `stream_run`: `ld[i] = leafStmt (chainEnd sᵢ nᵢ) nᵢ` for `i = 0..M`, each
`nᵢ` drawn separately; `stmts[0] = nodeStmt ld[0] ld[1]` (step 1, `PROVER first`);
`stmts[i-1] = nodeStmt stmts[i-2] ld[i]` (step `i ≥ 2`, `PROVER step`). Design §3.4 row 6 agrees:
first child = previous statement, second child = fresh leaf.

## Statements (kernel)

```lean
def combRoot (d₀ : Digest) (ds : List Digest) : Digest := ds.foldl nodeStmt d₀
def combStmt (l₀ : Digest × ℕ) (ls : List (Digest × ℕ)) : Digest :=
  combRoot (leafStmt l₀.1 l₀.2) (ls.map fun x => leafStmt x.1 x.2)       -- step |ls|'s statement
def combPaths (M : ℕ) : Finset (List Bool) :=     -- spine replicate j false (j ≤ M) ∪
  (range (M+1)).image (replicate · false) ∪ (range M).image (true :: replicate · false)  -- leaves
theorem card_combPaths (M) : (combPaths M).card = 2 * M + 1
theorem combPaths_subset (M) : combPaths M ⊆ paths M            -- every comb path has length ≤ M
def combWalk (L : Log) (l₀) (ls) (hn : ∀ x ∈ l₀ :: ls, x.2 ≤ chainCap) (p : Signed)
    (hacc : S.acc vk (combStmt l₀ ls) p = true) :
    COut S vk L (l₀ :: ls) (combStmt l₀ ls) p (combPaths ls.length)
theorem comb_compose ... :   -- the proposition combWalk proves
  (∃ ss, Forall₂ (fun s x => chainEnd s x.2 = x.1) ss (l₀ :: ls)) ∨ Nonempty Collision ∨
  (∃ (f : Forgery vk L) c bs, InTree S L (combStmt l₀ ls) p bs c f.p) ∨
  ∃ bs ∈ combPaths ls.length, bs.length ≤ ls.length ∧
    ∃ c q, InTree S L (combStmt l₀ ls) p bs c q ∧ Escape S vk L c q
theorem comb_prob (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (l₀ ls hn) (A : OProg Signed)
    (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun p L => ∃ hacc, (combWalk L l₀ ls hn p hacc).Escaped) A []
      ≤ (2 * ls.length + 1 : ℕ) * ((Q + qV) * ε)
```

`COut` is `Compose.Outcome` with per-leaf lengths and the escape's path in a given `Finset` (here
`combPaths M`) instead of a depth bound. Reused unchanged from `Library/Compose.lean`: `InTree`,
`Forgery`, `Escape`, `extract`, `paths`/`mem_paths`, `escape_prob_le` (the tighter count is just
`escape_prob_le` at `P = combPaths M`). Re-stated locally because they are `private` there:
`leafCollision`, `leafNodeCollision`, `nodeCollision` (verbatim copies).

**The tight count is reached**: `(2M+1)·(Q+qV)·ε`, 193 members at `M = 96` (control
`(combPaths 96).card = 193`), not `2^97 − 1`.

## Controls

- `combRoot d [] = d`, `combRoot a [b] = nodeStmt a b`, `combRoot a [b,c] = nodeStmt (nodeStmt a b) c`
  (`rfl`); `combRoot_append_singleton` is the harness loop's invariant.
- Known answer (`#guard`, evaluated, not a kernel proof): `combStmt` on starts `00³²,01³²,02³²,00³²`,
  lengths `0..3`, equals the digests the harness's own `rfh.digest` loop prints for step 1 and step 3;
  a deliberately wrong hex fails (`logs/audit/comb-axioms.log`). Negative: `treeRoot` of the same
  four leaves differs from step 3's statement.
- Negative: `[false, true] ∉ combPaths M` for every `M` while `∈ paths 2`;
  `(combPaths 2).card < (paths 2).card`.
- Not done: `combWalk` returning `starts` on an honest extraction (balanced: `walkFrom_leaf`).

## What remains paper (unchanged from the balanced case, Compose.lean header)

- Bounding the forgery outcome: a trace not contained in `L` is either an EUF-CMA forgery of the
  WOTS/Merkle signer or a `traceBytes` collision (`traceBytes_inj` gives injectivity under
  `queryCap`); and the collision outcome by `Adv_coll`. Only the split is paper; the outcome is kernel.
- The PRF hybrid (keyed BLAKE2s vs a random function), lazy sampling vs a random function,
  randomised adversaries (design §2.3).
- The union over **every** checked output (`Σ_{k≤M}(2k+1) = M²+2M`, 9,408 at `M = 96`): each
  `comb_prob` instance is per output; combining them needs one adversary emitting all outputs.

## Differences from the balanced case

1. **Per-leaf lengths.** The balanced walk has one `n` for all leaves; the comb's leaves have
   distinct `nᵢ`. The leaf step compares `(chainEnd s m, m)` with `(hᵢ, nᵢ)` and turns a mismatch
   into a collision via `enc64_inj` (both `≤ chainCap`); no new assumption.
2. **Linear path set.** The extraction tree's comb shape has `2M+1` members at depth up to `M`
   (versus `2^(r+1)−1` at depth `r`); the union bound is linear in `M`, as the design assumed.
3. **Inner members are extracted, not the runner's stored outputs.** The spine member at depth `j`
   proves `stmts[M−1−j]`, but its signed proof is the one `S.E` returns from the final output, not
   `π_{M−j}` the runner checked; the walk never uses intermediate outputs. Same as the balanced walk.
4. `M = 0` (one leaf) is covered too. Otherwise the same: one log, one root, same outcomes.

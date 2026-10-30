# The depth-free whole-stream bound, and a V-free event for the PRF hybrid (C4)

`RecursionFast/Explore/StreamBound.lean` (247 lines; imports `Explore/CombCompose`, olean compiled
into `.lake/build/lib/lean/RecursionFast/Explore/`): 4.6 s wall, no error, warning or `sorry`; axioms
`propext, Classical.choice, Quot.sound` only (**measured**, `logs/audit/stream-5.log`).

## 1. Statements (kernel)

```lean
theorem KS.exists_wins (h : KS R V E ε qV) (A : OProg α) (hA : ∀ H, (A.queries H).length ≤ Q)
    (hQ : Q + qV ≤ logCap) : prob (fun _ L => ∃ y, Wins R V E y L) A [] ≤ (Q + qV) * ε
theorem escape_any_le hks (A : OProg α) hA hQ : prob (fun _ L => ∃ c q, Escape S vk L c q) A [] ≤ …
theorem stream_escape_le hks (A : OProg (List (Digest × Signed))) hA hQ :
    prob (fun xs L => ∃ r ∈ xs, ∃ bs c q, InTree S L r.1 r.2 bs c q ∧ Escape S vk L c q) A [] ≤ …
theorem stream_prob hks l₀ ls hn (A : OProg (List Signed)) hA hQ :
    prob (fun xs L => ∃ i (hi : i < xs.length) (hacc : S.acc vk (combStmt l₀ (ls.take (i+1))) xs[i]),
      (combWalk L l₀ (ls.take (i+1)) (hn_take hn (i+1)) xs[i] hacc).Escaped) A [] ≤ (Q + qV) * ε
```

**Meaning.** `KS.exists_wins` is one `KS.select` with the selector `Classical.epsilon` of "wins".
The contract's `KS` quantifies over every query program and every function of its log, with no
efficiency bound, so an adversary that outputs *some* winning pair whenever one exists is
admissible (CGSY24 Thm 5.1's first failing vertex, no tree needed). So an escape of **any**
signed proof on the final log costs `(Q + qV)·ε`, and so does an escape of any member, at any depth,
of any output's tree. `stream_prob` (the chains `l₀ :: ls` fixed, `xs[i]` proving step `i+1`): for
each accepted output, `combWalk` returns a `COut`: the leaf starts, an explicit collision, an
explicit capped forgery in that output's tree, or an escape. That some accepted output escapes has
probability `≤ (Q + qV)·ε`, with no factor `M`. Forgery and collision stay **paper** (EUF-CMA,
`Adv^coll`).
**Consequence (kernel, ROM).** Design §2.4's factors `N = 193` and `9,408` are not needed: the
oracle term is `(Q + qV)·ε` for the whole stream, any `M`, re-timed outputs included; seams-T1
Finding 6 and ideation C5's margin concerns close. The bound is information-theoretic, so it
transfers to the deployment only through an efficiently decidable event (§3).
## 2. Arithmetic (kernel, `norm_num`)

`stream_err_target`: `Q ≤ 2^64 → qV ≤ 2^16 → ε ≤ 2^-120 → (Q + qV)·ε ≤ 2^-55` (`ℝ≥0`;
`stream_err_q` over `ℚ`). `union_factors`: `2^7·x ≤ 193·x`, `2^13·x ≤ 9408·x`, `193 < 2^8`,
`9408 < 2^14`: the design's figures are `2^7`–`2^8` and `2^13`–`2^14` times the depth-free bound.
## 3. C4: where the walk runs `V`, and a V-free event

**Text check.** In `walkFrom` (`Library/Compose.lean`) and in `combWalk`, `S.acc` (hence `V`) runs
only inside `extract`, which decides `Rel (S.acc vk) c w` for `E`'s output `w`. On a node witness,
`decRel` runs `acc` on both children. So `acc` runs on the root (a hypothesis: the harness's check)
and on the children `E` returns at each member it opens to a node, nowhere else. C4's premise (a
child is one a prover proved in-circuit) holds only when `E` succeeds. The walk runs `acc` exactly to
decide that; when `E` fails, the children are whatever `E` returned. So design §2.3's `D` **runs `V`
on `E`-chosen inputs**, with no time bound in the contract, and C4's cost argument fails as stated
(seams-T1 Finding 2 stands). **A V-free event suffices** (kernel):

```lean
def StructOk S L c p : Prop := ∃ w, S.E c p.π L = some w ∧ Rel (fun _ _ => true) c w  -- decidable
theorem escape_or_forgery_of_bad (hroot : S.acc vk c₀ p₀) (hm : InTree S L c₀ p₀ bs c q)
    (hbad : ¬ StructOk S L c q) : ∃ bs' c' q', bs' <:+ bs ∧ InTree S L c₀ p₀ bs' c' q' ∧
      (Escape S vk L c' q' ∨ ∃ f : Forgery vk L, f.p = q')
theorem stream_bad_prob hks A hA hQ P (hP : suffix-closed) : prob (fun xs L => ∃ r ∈ xs,
    S.acc vk r.1 r.2 ∧ (∃ bs ∈ P, ∃ c q, InTree S L r.1 r.2 bs c q ∧ ¬ StructOk S L c q) ∧
    ¬ ∃ (f : Forgery vk L), ∃ bs ∈ P, ∃ c, InTree S L r.1 r.2 bs c f.p) A [] ≤ (Q + qV) * ε
```

A member with no structural witness gives an escape or a forgery, at itself or at its nearest
accepted ancestor, whose `E` output names a rejected child (`anc_of_not_acc`). At `P = combPaths M`
the event runs only the harness's capped acceptance of the roots, `E` (`2M+1` calls per output),
BLAKE2s, trace membership and `SigOk` (`combPaths_suffix`: comb paths are suffix-closed). Controls: `StructOk` rejects children that do not hash to
`c`, and accepts a node whose children `acc` rejects.
**Real side (paper, mechanical; not in Lean).** The chain starts come from the *E-only comb walk*:
`combWalk` with `Rel (fun _ _ => true)`. It returns the starts, an explicit collision, or a comb
member with `¬ StructOk`, and it runs no `V`. Its failure without an explicit collision or forgery
is therefore inside `stream_bad_prob`'s event, so
`Pr_deploy ≤ (Q + qV)·ε + Adv^PRF(D) + Adv^EUF-CMA + Adv^coll` with a V-free `D`.
**Patch for §2.3:** define *bad* by the E-only walk.

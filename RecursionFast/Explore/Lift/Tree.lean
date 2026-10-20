/-
# Exploration: the lift for the runner's tree                                    (UNTRUSTED)

Probe P4. `Lift/Basic.lean` states the flat relation over any binary `Shape`. The runner hashes a
power of two of leaf digests up to its root with `treeRoot` (`Contract/Tree.lean`). This file
connects the two and states the lift for the runner's own flat statement.

* `treeRoot_append`: **halving**: the root of `2^(d+1)` digests is `nodeStmt` of the roots of its
  two halves of `2^d` (through `treeLevel_append` and `iterate_pow_eq`: `d` levels reduce `2^d`
  digests to their root).
* `Shape.perfect d ls`: the perfect shape of depth `d` over the list `ls` of `2^d` chain starts and
  lengths, split in the middle at every level. `perfect_leaves`: its leaves are `ls`;
  `perfect_root`: its root is the runner's `treeRoot` of the leaf digests.
* `RunnerFlat d (c, ls)`: the runner's flat relation: `ls` lists `2^d` chains within `chainCap`
  and `c` is the runner's root over their leaf statements. The chain starts are in the statement,
  in the clear.
* `lift_runner`: **any** knowledge state for `RunnerFlat d` (any witness type, any extractor) gives
  the lifted verifier over the cap-free witness-sending format a relativized knowledge state with
  the same potential, error and query bound. `lift_runner_ws`: the same over the library's
  witness-sending format for `d ≤ 14` (`halvesFit_perfect`); at `d = 15` the proof of a half's
  child (`2^13` leaves) exceeds `proofCap`, so the halves do not fit (`not_halvesFit_perfect`).
-/
import RecursionFast.Explore.Lift.WS
import RecursionFast.Contract.Tree

open scoped NNReal

namespace RecursionFast.Explore.Lift
open Relativized

/-! ## Halving the runner's tree -/

theorem length_treeLevel : ∀ cs : List Digest, (treeLevel cs).length = (cs.length + 1) / 2
  | [] => rfl
  | [_] => by simp [treeLevel]
  | _ :: _ :: cs => by simp only [treeLevel, List.length_cons, length_treeLevel cs]; omega

/-- A level of an even-length prefix and the rest is the two levels side by side. -/
theorem treeLevel_append : ∀ {xs : List Digest} (ys : List Digest), xs.length % 2 = 0 →
    treeLevel (xs ++ ys) = treeLevel xs ++ treeLevel ys
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | _ :: _ :: xs, ys, h => by
    simp only [List.cons_append, treeLevel, List.cons.injEq, true_and]
    exact treeLevel_append ys (by simp only [List.length_cons] at h; omega)

theorem length_iterate_pow : ∀ (d : ℕ) {xs : List Digest}, xs.length = 2 ^ d →
    (treeLevel^[d] xs).length = 1
  | 0, _, h => by simpa using h
  | d + 1, _, h => by
    rw [Function.iterate_succ_apply]
    exact length_iterate_pow d (by rw [length_treeLevel, h, pow_succ]; omega)

theorem iterate_singleton (a : Digest) : ∀ m, treeLevel^[m] [a] = [a]
  | 0 => rfl
  | m + 1 => by rw [Function.iterate_succ_apply]; exact iterate_singleton a m

/-- `d` levels reduce `2^d` digests to their root. -/
theorem iterate_pow_eq {d : ℕ} {xs : List Digest} (h : xs.length = 2 ^ d) :
    treeLevel^[d] xs = [treeRoot xs] := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (length_iterate_pow d h)
  have hd : d ≤ 2 ^ d := Nat.lt_two_pow_self.le
  rw [ha]
  unfold treeRoot
  rw [h, show 2 ^ d = (2 ^ d - d) + d by omega, Function.iterate_add_apply, ha, iterate_singleton]
  rfl

theorem iterate_append : ∀ (d : ℕ) {xs ys : List Digest}, xs.length = 2 ^ d →
    ys.length = 2 ^ d → treeLevel^[d] (xs ++ ys) = treeLevel^[d] xs ++ treeLevel^[d] ys
  | 0, _, _, _, _ => rfl
  | d + 1, xs, ys, hx, hy => by
    simp only [Function.iterate_succ_apply]
    rw [treeLevel_append ys (by rw [hx, pow_succ]; omega)]
    exact iterate_append d (by rw [length_treeLevel, hx, pow_succ]; omega)
      (by rw [length_treeLevel, hy, pow_succ]; omega)

/-- **Halving**: the runner's root of two halves of `2^d` digests each is `nodeStmt` of their
roots. -/
theorem treeRoot_append {d : ℕ} {xs ys : List Digest} (hx : xs.length = 2 ^ d)
    (hy : ys.length = 2 ^ d) : treeRoot (xs ++ ys) = nodeStmt (treeRoot xs) (treeRoot ys) := by
  have h := iterate_pow_eq (d := d + 1) (xs := xs ++ ys) (by simp [hx, hy, pow_succ]; omega)
  rw [Function.iterate_succ_apply', iterate_append d hx hy, iterate_pow_eq hx, iterate_pow_eq hy]
    at h
  simpa [treeLevel] using h.symm

/-! ## Perfect shapes -/

/-- The statement of a chain, from its start and length: the runner's leaf digest. -/
def leafDigest (x : Digest × ℕ) : Digest := leafStmt (chainEnd x.1 x.2) x.2

/-- **The perfect shape** of depth `d` over the chains `ls`: a leaf for depth `0` (the first chain);
for depth `d + 1`, the perfect shapes of depth `d` over the first `2^d` chains and the rest. -/
def Shape.perfect : ℕ → List (Digest × ℕ) → Shape
  | 0, ls => .leaf (ls.headD (Vector.replicate 32 0, 0)).1 (ls.headD (Vector.replicate 32 0, 0)).2
  | d + 1, ls => .node (perfect d (ls.take (2 ^ d))) (perfect d (ls.drop (2 ^ d)))

theorem length_take_pow {d : ℕ} {ls : List (Digest × ℕ)} (h : ls.length = 2 ^ (d + 1)) :
    (ls.take (2 ^ d)).length = 2 ^ d := by
  rw [List.length_take, h, pow_succ]; omega

theorem length_drop_pow {d : ℕ} {ls : List (Digest × ℕ)} (h : ls.length = 2 ^ (d + 1)) :
    (ls.drop (2 ^ d)).length = 2 ^ d := by
  rw [List.length_drop, h, pow_succ]; omega

/-- The leaves of the perfect shape over `2^d` chains are those chains. -/
theorem perfect_leaves : ∀ (d : ℕ) {ls : List (Digest × ℕ)}, ls.length = 2 ^ d →
    (Shape.perfect d ls).leaves = ls
  | 0, [_], _ => rfl
  | 0, [], h | 0, _ :: _ :: _, h => by simp at h
  | d + 1, ls, h => by
    rw [Shape.perfect, Shape.leaves, perfect_leaves d (length_take_pow h),
      perfect_leaves d (length_drop_pow h), List.take_append_drop]

/-- **The perfect shape folds to the runner's root** of the chains' leaf digests. -/
theorem perfect_root : ∀ (d : ℕ) {ls : List (Digest × ℕ)}, ls.length = 2 ^ d →
    (Shape.perfect d ls).root = treeRoot (ls.map leafDigest)
  | 0, [_], _ => rfl
  | 0, [], h | 0, _ :: _ :: _, h => by simp at h
  | d + 1, ls, h => by
    rw [Shape.perfect, Shape.root, perfect_root d (length_take_pow h),
      perfect_root d (length_drop_pow h), ← treeRoot_append (d := d) (by rw [List.length_map, length_take_pow h])
        (by rw [List.length_map, length_drop_pow h]), ← List.map_append, List.take_append_drop]

/-! ## The runner's flat relation -/

/-- **The runner's flat relation** at depth `d`: the statement lists `2^d` chain starts and lengths
in the clear, each chain within `chainCap`, and its digest is the runner's root over their leaf
statements. -/
def RunnerFlat (d : ℕ) (x : Digest × List (Digest × ℕ)) : Prop :=
  x.2.length = 2 ^ d ∧ x.1 = treeRoot (x.2.map leafDigest) ∧ ∀ l ∈ x.2, l.2 ≤ chainCap

theorem flat_perfect {d : ℕ} {x : Digest × List (Digest × ℕ)} (h : RunnerFlat d x) :
    Flat x.1 (Shape.perfect d x.2) :=
  ⟨(perfect_root d h.1).trans h.2.1.symm, by rw [perfect_leaves d h.1]; exact h.2.2⟩

/-- The lift's flat extractor for the runner's relation: the perfect shape of the statement's
chains, whenever the flat extractor returns a witness. -/
def runnerE {W₀ : Type} (d : ℕ) (E₀ : Digest × List (Digest × ℕ) → Proof → Log → Option W₀)
    (x : Digest × List (Digest × ℕ)) (π : Proof) (L : Log) : Option Shape :=
  (E₀ x π L).map fun _ => Shape.perfect d x.2

variable {d : ℕ} {W₀ : Type} {V₀ : Digest × List (Digest × ℕ) → Proof → OProg Bool}
  {E₀ : Digest × List (Digest × ℕ) → Proof → Log → Option W₀} {ε : ℝ≥0} {qV : ℕ}

/-- **The lift for the runner's tree**: any knowledge state of error `ε` for the runner's flat
relation, with any witness type and extractor, and a query bound `qV`, gives the lifted verifier
(over the cap-free witness-sending format) relativized knowledge soundness with the same error and
query bound; it is `V₀` on flat frames and asks nothing on witness-sending frames. -/
theorem lift_runner (D : Codec Wit witSub) (C : LCodec (Digest × List (Digest × ℕ)))
    (k : GKState (fun x (_ : W₀) => RunnerFlat d x) V₀ E₀ ε)
    (hq : ∀ H x π₀, ((V₀ x π₀).queries H).length ≤ qV) :
    KSRel (liftV C (freeSys D) Prod.fst V₀) (liftE C (freeSys D) (runnerE d E₀)) ε qV ∧
      (∀ c x π₀, x.1 = c → liftV C (freeSys D) Prod.fst V₀ c (C.enc (.snark x π₀)) = V₀ x π₀) ∧
      (∀ H c π, (liftV C (freeSys D) Prod.fst V₀ c (wrap C π)).queries H = []) :=
  lift_free D C (k.map (R' := fun x t => t = Shape.perfect d x.2 ∧ RunnerFlat d x)
    (fun x _ => Shape.perfect d x.2) fun _ _ h => ⟨rfl, h⟩) (fun _ _ ⟨ht, h⟩ => ht ▸ flat_perfect h)
    hq

/-! ## The library's witness-sending format on perfect shapes -/

theorem length_perfect_leaves {d : ℕ} {ls : List (Digest × ℕ)} (h : ls.length = 2 ^ d) :
    (Shape.perfect d ls).leaves.length = 2 ^ d := by rw [perfect_leaves d h, h]

/-- Perfect shapes of depth at most `13` fit the library's format. -/
theorem wsFits_perfect : ∀ {d : ℕ} {ls : List (Digest × ℕ)}, d ≤ 13 → ls.length = 2 ^ d →
    WSFits (Shape.perfect d ls)
  | 0, _, _, _ => trivial
  | d + 1, ls, hd, h => by
    have h₁ := size_wsProof (Shape.perfect d (ls.take (2 ^ d)))
    have h₂ := size_wsProof (Shape.perfect d (ls.drop (2 ^ d)))
    rw [length_perfect_leaves (length_take_pow h)] at h₁
    rw [length_perfect_leaves (length_drop_pow h)] at h₂
    have : 2 ^ d ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨by unfold proofCap; omega, by unfold proofCap; omega,
      wsFits_perfect (by omega) (length_take_pow h), wsFits_perfect (by omega) (length_drop_pow h)⟩

/-- The halves of a perfect shape of depth at most `14` fit the library's format. -/
theorem halvesFit_perfect {d : ℕ} {ls : List (Digest × ℕ)} (hd : d ≤ 14) (h : ls.length = 2 ^ d) :
    wsSys.HalvesFit (Shape.perfect d ls) := by
  cases d with
  | zero => trivial
  | succ d =>
    exact ⟨wsFits_perfect (by omega) (length_take_pow h),
      wsFits_perfect (by omega) (length_drop_pow h)⟩

/-- At depth `15` the halves do not fit: each half's children have `2^13` leaves, whose proofs
exceed `proofCap`. -/
theorem not_halvesFit_perfect {ls : List (Digest × ℕ)} (h : ls.length = 2 ^ 15) :
    ¬ wsSys.HalvesFit (Shape.perfect 15 ls) := by
  rintro ⟨hl, -⟩
  have h₁ := length_take_pow (d := 14) h
  refine not_wsFits (Or.inl ?_) (show WSFits (Shape.perfect 14 _) from hl)
  rw [length_perfect_leaves (length_take_pow h₁)]
  norm_num

/-- **The lift for the runner's tree over the library's witness-sending format**, for trees of at
most `2^14` leaves. -/
theorem lift_runner_ws (hd : d ≤ 14) (C : LCodec (Digest × List (Digest × ℕ)))
    (k : GKState (fun x (_ : W₀) => RunnerFlat d x) V₀ E₀ ε)
    (hq : ∀ H x π₀, ((V₀ x π₀).queries H).length ≤ qV) :
    KSRel (liftV C wsSys Prod.fst V₀) (liftE C wsSys (runnerE d E₀)) ε qV ∧
      (∀ c x π₀, x.1 = c → liftV C wsSys Prod.fst V₀ c (C.enc (.snark x π₀)) = V₀ x π₀) ∧
      (∀ H c π, (liftV C wsSys Prod.fst V₀ c (wrap C π)).queries H = []) :=
  lift C (k.map (R' := fun x t => t = Shape.perfect d x.2 ∧ RunnerFlat d x)
    (fun x _ => Shape.perfect d x.2) fun _ _ h => ⟨rfl, h⟩)
    (fun _ _ ⟨ht, h⟩ => ht ▸ ⟨flat_perfect h, halvesFit_perfect hd h.1⟩) hq

end RecursionFast.Explore.Lift

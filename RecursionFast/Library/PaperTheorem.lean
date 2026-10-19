/-
  RecursionFast.Library.PaperTheorem  (UNTRUSTED, kernel-checked)

  **The paper theorem of `Contract/Security.lean` (DESIGN-v3 §4.5), over the exact contract
  text**, for a lazily sampled random oracle. From the V3-S2-KS review's probe
  `logs/ks-review-probes/PaperTheorem.lean` (`Probe.paper`, in the submissions repository), moved
  here with the constant `2^256` of the amended `step` (V3-KS-A7) and nothing else changed.

  * `prob B p L`: the probability that the query program `p`, started with the table `L`, ends in
    a leaf `(x, L')` with `B x L'`, where a fresh query is answered uniformly at random over the
    `2^256` digests (and recorded) and a repeated query reads the table by first match, as
    `runLog` does. This is the random oracle by lazy sampling.
  * `DepthLE p n`: `p` asks at most `n` queries on every path.
  * `pot`: the potential capped at `1` and stopped when it first reaches `1`, in expectation at
    the end of the run; `pot_le`: it rises by at most `ε` per query (a supermartingale, `step`);
    `prob_le_pot`: failure at a leaf within `logCap` forces the potential to `1` (`final`).
  * **`paper`**: for a game `G` (the adversary followed by the verifier's queries, so that the
    final table answers them) asking at most `n ≤ logCap` queries, the probability that the
    verifier accepts on the final table and the extractor does not return a witness is at most
    `n · ε`; with `n = Q + qV`, the bound `(Q + qV) · ε` of the contract's header.

  Not covered, standard and on paper: lazy sampling against a uniformly random function, and
  randomised adversaries (average the deterministic case over the coins).
-/
import RecursionFast.Library.Security

open scoped NNReal

namespace RecursionFast.PaperTheorem
open RecursionFast

variable {α : Type} {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
  {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0}

local notation "N" => ((2 : ℝ≥0) ^ 256)

theorem N_pos : 0 < N := by positivity

/-- At most `n` queries on every path. -/
def DepthLE : OProg α → ℕ → Prop
  | .ret _, _ => True
  | .query _ _, 0 => False
  | .query _ c, n + 1 => ∀ a, DepthLE (c a) n

/-- Lazy-sampling probability of ending in a leaf satisfying `B`. -/
noncomputable def prob (B : α → Log → Prop) : OProg α → Log → ℝ≥0
  | .ret x, L => by classical exact if B x L then 1 else 0
  | .query q c, L =>
    match L.find? (fun e => e.1 = q) with
    | some e => prob B (c e.2) L
    | none => N⁻¹ * ∑ a : Digest, prob B (c a) (L ++ [(q, a)])

/-- The capped potential, stopped at `1`, in expectation at the end of the run. -/
noncomputable def pot (k : KState R V E ε) : OProg α → Log → ℝ≥0
  | .ret _, L => min 1 (k.μ L)
  | .query q c, L =>
    if 1 ≤ k.μ L then 1 else
    match L.find? (fun e => e.1 = q) with
    | some e => pot k (c e.2) L
    | none => N⁻¹ * ∑ a : Digest, pot k (c a) (L ++ [(q, a)])

theorem avg_le {f : Digest → ℝ≥0} {b : ℝ≥0} (h : ∀ a, f a ≤ b) : N⁻¹ * ∑ a, f a ≤ b := by
  have : ∑ a, f a ≤ N * b := by
    calc ∑ a, f a ≤ ∑ _a : Digest, b := Finset.sum_le_sum fun a _ => h a
      _ = N * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, fintype_card_digest, Nat.cast_pow,
          Nat.cast_ofNat]
  calc N⁻¹ * ∑ a, f a ≤ N⁻¹ * (N * b) := by gcongr
    _ = b := by rw [← mul_assoc, inv_mul_cancel₀ N_pos.ne', one_mul]

theorem prob_le_one (B : α → Log → Prop) : ∀ (p : OProg α) (L : Log), prob B p L ≤ 1
  | .ret x, L => by classical simp only [prob]; split_ifs <;> simp
  | .query q c, L => by
    simp only [prob]
    split
    · exact prob_le_one B _ _
    · exact avg_le fun a => prob_le_one B _ _

theorem find_none_fresh {L : Log} {q : ByteArray}
    (h : L.find? (fun e => decide (e.1 = q)) = none) : q ∉ L.map Prod.fst := by
  intro hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  exact (List.find?_eq_none.mp h) e he (by simp)

/-- The stopped capped potential is a supermartingale with drift `ε` per query. -/
theorem pot_le (k : KState R V E ε) :
    ∀ (p : OProg α) (n : ℕ) (L : Log), DepthLE p n → L.length + n ≤ logCap →
      pot k p L ≤ min 1 (k.μ L) + n * ε
  | .ret _, n, L, _, _ => by simp [pot]
  | .query q c, 0, L, h, _ => h.elim
  | .query q c, n + 1, L, h, hlen => by
    simp only [pot]
    split_ifs with h1
    · simp [h1]
    · push Not at h1
      have hmin : min 1 (k.μ L) = k.μ L := min_eq_right h1.le
      split
      · rename_i e he
        calc pot k (c e.2) L ≤ min 1 (k.μ L) + n * ε := pot_le k _ n L (h _) (by omega)
          _ ≤ min 1 (k.μ L) + (n + 1 : ℕ) * ε := by gcongr; omega
      · rename_i hf
        have hq := find_none_fresh hf
        have hstep := k.step L q (by omega) h1 hq
        have hrec : ∀ a, pot k (c a) (L ++ [(q, a)]) ≤ k.μ (L ++ [(q, a)]) + n * ε := fun a =>
          (pot_le k _ n _ (h a) (by simp; omega)).trans (by gcongr; exact min_le_right _ _)
        calc N⁻¹ * ∑ a, pot k (c a) (L ++ [(q, a)])
            ≤ N⁻¹ * ∑ a, (k.μ (L ++ [(q, a)]) + n * ε) := by
              exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hrec a) bot_le
          _ = N⁻¹ * ∑ a, k.μ (L ++ [(q, a)]) + n * ε := by
              rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ,
                nsmul_eq_mul, fintype_card_digest, Nat.cast_pow, Nat.cast_ofNat]
              congr 1
              rw [← mul_assoc, inv_mul_cancel₀ N_pos.ne', one_mul]
          _ ≤ N⁻¹ * ((k.μ L + ε) * N) + n * ε := by
              have h2 := mul_le_mul_of_nonneg_left hstep (bot_le : (0 : ℝ≥0) ≤ N⁻¹)
              exact add_le_add h2 le_rfl
          _ = min 1 (k.μ L) + (n + 1 : ℕ) * ε := by
              rw [hmin, mul_comm _ N, ← mul_assoc, inv_mul_cancel₀ N_pos.ne', one_mul]
              push_cast; ring

/-- The failure probability is below the stopped potential, when failure at a leaf within
`logCap` forces the potential to `1`. -/
theorem prob_le_pot (k : KState R V E ε) (B : α → Log → Prop)
    (hB : ∀ x L, B x L → L.length ≤ logCap → 1 ≤ k.μ L) :
    ∀ (p : OProg α) (n : ℕ) (L : Log), DepthLE p n → L.length + n ≤ logCap →
      prob B p L ≤ pot k p L
  | .ret x, n, L, _, hlen => by
    classical
    simp only [prob, pot]
    split_ifs with hb
    · exact le_min le_rfl (hB x L hb (by omega))
    · exact bot_le
  | .query q c, 0, L, h, _ => h.elim
  | .query q c, n + 1, L, h, hlen => by
    simp only [prob, pot]
    split_ifs with h1
    · split
      · exact prob_le_one B _ _
      · exact avg_le fun a => prob_le_one B _ _
    · split
      · exact prob_le_pot k B hB _ n L (h _) (by omega)
      · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
          prob_le_pot k B hB _ n _ (h a) (by simp; omega)) bot_le

/-- **The paper theorem** over the exact contract text: the knowledge-soundness failure
probability of a game asking at most `n ≤ logCap` queries is at most `n · ε`. -/
theorem paper (k : KState R V E ε) (G : OProg (Digest × Proof)) (n : ℕ) (hG : DepthLE G n)
    (hn : n ≤ logCap) :
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧
      ¬ ∃ w, E x.1 x.2 L = some w ∧ R x.1 w) G [] ≤ n * ε := by
  have hB : ∀ (x : Digest × Proof) L, ((V x.1 x.2).runLog L = some true ∧
      ¬ ∃ w, E x.1 x.2 L = some w ∧ R x.1 w) → L.length ≤ logCap → 1 ≤ k.μ L := by
    intro x L ⟨hacc, hext⟩ hlen
    by_contra hlt
    exact hext (k.final L x.1 x.2 hlen (not_le.mp hlt) hacc)
  calc _ ≤ pot k G [] := prob_le_pot k _ hB G n [] hG (by simpa using hn)
    _ ≤ min 1 (k.μ []) + n * ε := pot_le k G n [] hG (by simpa using hn)
    _ = n * ε := by simp [k.empty]

end RecursionFast.PaperTheorem

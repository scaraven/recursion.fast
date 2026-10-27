/-
  RecursionFast.Library.PaperTheorem  (UNTRUSTED, kernel-checked)

  **From a knowledge state to the contract's knowledge soundness** (DESIGN-v3 §4.5, V4-A10): the
  bridge an entry that proves its security through a potential uses. From the V3-S2-KS review's
  probe `logs/ks-review-probes/PaperTheorem.lean` (`Probe.paper`, in the submissions repository),
  with the constant `2^256` of the amended `step` (V3-KS-A7); generalised in v4 from a syntactic
  depth bound to the functional query bounds the contract states.

  * `pot`: the potential capped at `1` and stopped when it first reaches `1`, in expectation at
    the end of the run; `pot_le`: it rises by at most `ε` per query (a supermartingale, `step`);
    `prob_le_pot`: failure at a leaf within `logCap` forces the potential to `1` (`final`). Both
    count the queries of a run from the table `L` through every oracle function consistent with
    `L`: a lazily sampled run agrees with one, so it asks at most as many fresh queries.
  * **`paper`**: for a game `G` asking at most `n ≤ logCap` queries under every oracle function,
    the probability (`prob`, the contract's lazy sampling) that the verifier accepts on the final
    table and the extractor does not return a witness is at most `n · ε`;
    `prob_potential_ge_one`: so is the probability that the final table's potential is at least
    `1`, the one event of the meter's lossless composition (`Library/Compose.lean`).
  * **`KState.ks`, the bridge**: a knowledge state with error `ε` and a verifier asking at most
    `qV` queries give `KS R V E ε qV`. The contract's game (the adversary, then `V` on its output)
    asks at most `Q + qV` queries (`OProg.queries_bind`), so `paper` gives `(Q + qV) · ε`.

  Not covered, standard and on paper: lazy sampling against a uniformly random function, and
  randomised adversaries (average the deterministic case over the coins).
-/
import RecursionFast.Library.Prob

open scoped NNReal

namespace RecursionFast.PaperTheorem
open RecursionFast

variable {α : Type} {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
  {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0}

local notation "N" => ((2 : ℝ≥0) ^ 256)

/-- The capped potential, stopped at `1`, in expectation at the end of the run. -/
noncomputable def pot (k : KState R V E ε) : OProg α → Log → ℝ≥0
  | .ret _, L => min 1 (k.μ L)
  | .query q c, L =>
    if 1 ≤ k.μ L then 1 else
    match L.find? (fun e => e.1 = q) with
    | some e => pot k (c e.2) L
    | none => N⁻¹ * ∑ a : Digest, pot k (c a) (L ++ [(q, a)])

theorem find_none_fresh {L : Log} {q : ByteArray}
    (h : L.find? (fun e => decide (e.1 = q)) = none) : q ∉ L.map Prod.fst := by
  intro hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  exact (List.find?_eq_none.mp h) e he (by simp)

/-- A program that asks at most `n + 1` queries under every oracle consistent with `L` asks at
most `n` after its first query, when `L` answers that query. -/
theorem bound_found {c : Digest → OProg α} {q : ByteArray} {L : Log} {n : ℕ}
    {e : ByteArray × Digest} (he : L.find? (fun e => e.1 = q) = some e)
    (h : ∀ H, Consistent H L → ((OProg.query q c).queries H).length ≤ n + 1) :
    ∀ H, Consistent H L → ((c e.2).queries H).length ≤ n := fun H hH => by
  have := h H hH
  rw [OProg.queries, List.length_cons, hH q e he] at this
  omega

/-- The same when the first query is fresh, under every oracle consistent with its answer. -/
theorem bound_fresh {c : Digest → OProg α} {q : ByteArray} {L : Log} {n : ℕ}
    (hf : L.find? (fun e => e.1 = q) = none)
    (h : ∀ H, Consistent H L → ((OProg.query q c).queries H).length ≤ n + 1) (a : Digest) :
    ∀ H, Consistent H (L ++ [(q, a)]) → ((c a).queries H).length ≤ n := fun H hH => by
  obtain ⟨hL, ha⟩ := consistent_append hf hH
  have := h H hL
  rw [OProg.queries, List.length_cons, ha] at this
  omega

/-- A program that asks a query asks at least one. -/
theorem bound_zero {c : Digest → OProg α} {q : ByteArray} {L : Log}
    (h : ∀ H, Consistent H L → ((OProg.query q c).queries H).length ≤ 0) : False := by
  obtain ⟨H, hH⟩ := exists_consistent L
  simpa [OProg.queries] using h H hH

/-- The stopped capped potential is a supermartingale with drift `ε` per query. -/
theorem pot_le (k : KState R V E ε) :
    ∀ (p : OProg α) (n : ℕ) (L : Log), (∀ H, Consistent H L → (p.queries H).length ≤ n) →
      L.length + n ≤ logCap → pot k p L ≤ min 1 (k.μ L) + n * ε
  | .ret _, n, L, _, _ => by simp [pot]
  | .query q c, 0, L, h, _ => (bound_zero h).elim
  | .query q c, n + 1, L, h, hlen => by
    simp only [pot]
    split_ifs with h1
    · simp [h1]
    · push Not at h1
      have hmin : min 1 (k.μ L) = k.μ L := min_eq_right h1.le
      split
      · rename_i e he
        calc pot k (c e.2) L ≤ min 1 (k.μ L) + n * ε :=
              pot_le k _ n L (bound_found he h) (by omega)
          _ ≤ min 1 (k.μ L) + (n + 1 : ℕ) * ε := by gcongr; omega
      · rename_i hf
        have hq := find_none_fresh hf
        have hstep := k.step L q (by omega) h1 hq
        have hrec : ∀ a, pot k (c a) (L ++ [(q, a)]) ≤ k.μ (L ++ [(q, a)]) + n * ε := fun a =>
          (pot_le k _ n _ (bound_fresh hf h a) (by simp; omega)).trans
            (by gcongr; exact min_le_right _ _)
        calc N⁻¹ * ∑ a, pot k (c a) (L ++ [(q, a)])
            ≤ N⁻¹ * ∑ a, (k.μ (L ++ [(q, a)]) + n * ε) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hrec a) bot_le
          _ = N⁻¹ * ∑ a, k.μ (L ++ [(q, a)]) + n * ε := by
              rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ,
                nsmul_eq_mul, fintype_card_digest, Nat.cast_pow, Nat.cast_ofNat]
              congr 1
              rw [← mul_assoc, inv_mul_cancel₀ N_pos.ne', one_mul]
          _ ≤ N⁻¹ * ((k.μ L + ε) * N) + n * ε :=
              add_le_add_left (mul_le_mul_of_nonneg_left hstep bot_le) _
          _ = min 1 (k.μ L) + (n + 1 : ℕ) * ε := by
              rw [hmin, mul_comm _ N, ← mul_assoc, inv_mul_cancel₀ N_pos.ne', one_mul]
              push_cast; ring

/-- The failure probability is below the stopped potential, when failure at a leaf within
`logCap` forces the potential to `1`. -/
theorem prob_le_pot (k : KState R V E ε) (B : α → Log → Prop)
    (hB : ∀ x L, B x L → L.length ≤ logCap → 1 ≤ k.μ L) :
    ∀ (p : OProg α) (n : ℕ) (L : Log), (∀ H, Consistent H L → (p.queries H).length ≤ n) →
      L.length + n ≤ logCap → prob B p L ≤ pot k p L
  | .ret x, n, L, _, hlen => by
    classical
    simp only [prob, pot]
    split_ifs with hb
    · exact le_min le_rfl (hB x L hb (by omega))
    · exact bot_le
  | .query q c, 0, L, h, _ => (bound_zero h).elim
  | .query q c, n + 1, L, h, hlen => by
    simp only [prob, pot]
    split_ifs with h1
    · split
      · exact prob_le_one B _ _
      · exact avg_le fun a => prob_le_one B _ _
    · cases hf : L.find? (fun e => decide (e.1 = q)) with
      | some e => exact prob_le_pot k B hB _ n L (bound_found hf h) (by omega)
      | none =>
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
          prob_le_pot k B hB _ n _ (bound_fresh hf h a) (by simp; omega)) bot_le

/-- **The paper theorem** over the exact contract text: the knowledge-soundness failure
probability of a game asking at most `n ≤ logCap` queries under every oracle is at most `n · ε`. -/
theorem paper (k : KState R V E ε) (G : OProg (Digest × Proof)) (n : ℕ)
    (hG : ∀ H, (G.queries H).length ≤ n) (hn : n ≤ logCap) :
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧
      ¬ ∃ w, E x.1 x.2 L = some w ∧ R x.1 w) G [] ≤ n * ε := by
  have hB : ∀ (x : Digest × Proof) L, ((V x.1 x.2).runLog L = some true ∧
      ¬ ∃ w, E x.1 x.2 L = some w ∧ R x.1 w) → L.length ≤ logCap → 1 ≤ k.μ L :=
    fun x L ⟨hacc, hext⟩ hlen => not_lt.mp fun hlt => hext (k.final L x.1 x.2 hlen hlt hacc)
  calc _ ≤ pot k G [] := prob_le_pot k _ hB G n [] (fun H _ => hG H) (by simpa using hn)
    _ ≤ min 1 (k.μ []) + n * ε := pot_le k G n [] (fun H _ => hG H) (by simpa using hn)
    _ = n * ε := by simp [k.empty]

/-- **The potential reaches `1` rarely**: for a game asking at most `n ≤ logCap` queries under
every oracle, the final log's potential is at least `1` with probability at most `n · ε`. The one
event of the meter's lossless composition (`Library/Compose.lean`, `compose_of_kstate`). -/
theorem prob_potential_ge_one (k : KState R V E ε) (G : OProg α) (n : ℕ)
    (hG : ∀ H, (G.queries H).length ≤ n) (hn : n ≤ logCap) :
    prob (fun _ L => 1 ≤ k.μ L) G [] ≤ n * ε :=
  calc _ ≤ pot k G [] :=
        prob_le_pot k _ (fun _ _ h _ => h) G n [] (fun H _ => hG H) (by simpa using hn)
    _ ≤ min 1 (k.μ []) + n * ε := pot_le k G n [] (fun H _ => hG H) (by simpa using hn)
    _ = n * ε := by simp [k.empty]

end RecursionFast.PaperTheorem

namespace RecursionFast

/-- **The bridge from the potential to the contract** (V4-A10): a knowledge state with error `ε`,
for a verifier asking at most `qV` queries on every input and oracle, gives knowledge soundness
`KS R V E ε qV`. -/
theorem KState.ks {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} {qV : ℕ} (k : KState R V E ε)
    (hq : ∀ H c π, ((V c π).queries H).length ≤ qV) : KS R V E ε qV :=
  ⟨hq, fun A Q hA hQ => by
    have hG : ∀ H, ((A.bind fun x => (V x.1 x.2).bind fun _ => .ret x).queries H).length ≤
        Q + qV := fun H => by
      rw [OProg.queries_bind, OProg.queries_bind, List.length_append, List.length_append]
      exact Nat.add_le_add (hA H) (by simpa [OProg.queries] using hq H _ _)
    simpa using PaperTheorem.paper k _ (Q + qV) hG hQ⟩

end RecursionFast

/-
# Controls: completeness with error (`Contract/Security.lean`, V3-S2R-A2), positive and negative

`failProb` over a lazily sampled oracle, `CompleteWithError` and `completenessCap = 2^-128`. The
answers are split by the top bit of their first byte (`good`); flipping that bit is a bijection
of the digests, so exactly half are good (`sum_bad`).

Positive:
* `grind_exact`: a verifier that accepts the proof `z i` iff the answer to the query `z i` is good,
  with a prover that tries the nonces `0, …, k − 1` and falls back to nonce `0` (already tried,
  bad), fails with probability **exactly** `2^-k` for every `k ≥ 1` (review H-m1: the fallback is
  what makes it exact). `grind128_complete`: at `k = 128` it is complete at the cap. This is
  proof-of-work grinding, which `Complete ∀ H` excluded.
* `fixed_complete_half`: a verifier that accepts iff the answer to one fixed query is good is
  complete at `δ = 1/2`, with every prover.
* The embedding `Complete → CompleteWithError 0` is `Library/Completeness.lean`'s
  `complete_withError_zero`; the witness-sending argument uses it (`Controls/Security.lean`,
  `ws_complete`).

Negative:
* `grind127_not_complete`: with 127 nonces (`2^-127`) it is not complete at the cap, for any
  relation with a witness.
* `fixed_not_complete`: the fixed-query verifier is not complete at any `δ < 1/2`, **whatever the
  prover does**: a prover can ask the query too, and cannot change its answer.
* Rejecting everything is complete at no `δ < 1` (`Controls/Security.lean`,
  `rejectAll_not_complete`).
-/
import RecursionFast.Library.Completeness
import RecursionFast.Controls.Potential

open scoped NNReal

namespace RecursionFast.Controls.Completeness
open RecursionFast
open RecursionFast.Controls.Potential (z z_size z_inj)

/-! ## Half of the answers are good -/

/-- An answer is good when the top bit of its first byte is `0`. -/
def good (a : Digest) : Bool := decide (a[0] < 128)

/-- Flip the top bit of the first byte. -/
def flipTop (a : Digest) : Digest := a.set 0 (a[0] ^^^ 128)

theorem xor_lt (x : UInt8) : (x ^^^ 128 < 128) ↔ ¬ x < 128 := by
  have h : ∀ n : Fin 256, (UInt8.ofFin n ^^^ 128 < 128 ↔ ¬ UInt8.ofFin n < 128) := by
    decide +kernel
  simpa using h x.toFin

theorem xor_xor (x : UInt8) : x ^^^ 128 ^^^ 128 = x := by
  have h : ∀ n : Fin 256, UInt8.ofFin n ^^^ 128 ^^^ 128 = UInt8.ofFin n := by decide +kernel
  simpa using h x.toFin

theorem good_flipTop (a : Digest) : good (flipTop a) = !good a := by
  simp only [good, flipTop, Vector.getElem_set_self, xor_lt]
  cases h : decide (a[0] < 128) <;> simp_all

theorem flipTop_flipTop (a : Digest) : flipTop (flipTop a) = a := by
  ext i hi
  simp [flipTop, Vector.getElem_set]
  split <;> simp_all [xor_xor]

/-- `flipTop` as a bijection. -/
def topEquiv : Digest ≃ Digest := ⟨flipTop, flipTop, flipTop_flipTop, flipTop_flipTop⟩

/-- Exactly `2^255` answers are bad. -/
theorem sum_bad (x : ℝ≥0) : ∑ a : Digest, (if good a then 0 else x) = 2 ^ 255 * x := by
  have h1 : ∑ a : Digest, (if good a then 0 else x) = ∑ a : Digest, (if good a then x else 0) := by
    rw [← Equiv.sum_comp topEquiv]
    simp [topEquiv, good_flipTop]
    exact Finset.sum_congr rfl fun a _ => by cases good a <;> simp
  have h2 : ∑ a : Digest, ((if good a then 0 else x) + (if good a then x else 0)) =
      2 ^ 256 * x := by
    simp only [show ∀ a, ((if good a then 0 else x) + (if good a then x else 0)) = x from
      fun a => by cases good a <;> simp]
    rw [Finset.sum_const, Finset.card_univ, fintype_card_digest, nsmul_eq_mul]; norm_num
  rw [Finset.sum_add_distrib, ← h1] at h2
  have : (2 : ℝ≥0) * ∑ a : Digest, (if good a then 0 else x) = 2 * (2 ^ 255 * x) := by
    rw [two_mul, h2]; ring
  exact mul_left_cancel₀ two_ne_zero this

theorem avg_bad (x : ℝ≥0) :
    ((2 : ℝ≥0) ^ 256)⁻¹ * ∑ a : Digest, (if good a then 0 else x) = 2⁻¹ * x := by
  rw [sum_bad, pow_succ, mul_inv, mul_comm ((2 : ℝ≥0) ^ 255)⁻¹, mul_assoc,
    ← mul_assoc ((2 : ℝ≥0) ^ 255)⁻¹, inv_mul_cancel₀ (by positivity), one_mul]

/-! ## Grinding: exactly `2^-k` with `k` nonces -/

/-- Accept the proof `z i` iff the answer to the query `z i` is good. -/
def Vg (_ : Digest) (π : Proof) : OProg Bool := .query (z π.size) fun a => .ret (good a)

/-- Try the nonces `i, i + 1, …` (`k` of them); fall back to nonce `0`. -/
def grindP : ℕ → ℕ → OProg Proof
  | 0, _ => .ret (z 0)
  | k + 1, i => .query (z i) fun a => if good a then .ret (z i) else grindP k (i + 1)

/-- The nonces below `i` are in the log with bad answers; the others are not in it. -/
def Tried (L : Log) (i : ℕ) : Prop :=
  (∀ j < i, ∃ a, L.find? (fun e => e.1 = z j) = some (z j, a) ∧ good a = false) ∧
    ∀ j, i ≤ j → L.find? (fun e => e.1 = z j) = none

theorem grind_fail (c : Digest) : ∀ k i L, Tried L i → (k = 0 → 0 < i) →
    failProb ((grindP k i).bind (Vg c)) L = 2⁻¹ ^ k
  | 0, i, L, ⟨h1, _⟩, hi => by
    obtain ⟨a, ha, hb⟩ := h1 0 (hi rfl)
    simp [grindP, OProg.bind, Vg, z_size, failProb, ha, hb]
  | k + 1, i, L, ⟨h1, h2⟩, _ => by
    have step : ∀ a, failProb ((if good a then OProg.ret (z i) else grindP k (i + 1)).bind
        (Vg c)) (L ++ [(z i, a)]) = if good a then 0 else 2⁻¹ ^ k := by
      intro a
      cases hg : good a
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine grind_fail c k (i + 1) _ ⟨fun j hj => ?_, fun j hj => ?_⟩ (fun _ => by omega)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · obtain ⟨a', ha', hb'⟩ := h1 j hj
            exact ⟨a', by simp [List.find?_append, ha'], hb'⟩
          · exact ⟨a, by simp [List.find?_append, h2 j le_rfl], hg⟩
        · have hne : z i ≠ z j := fun h => by have := z_inj h; omega
          simp [List.find?_append, h2 j (by omega), hne]
      · simp [OProg.bind, Vg, z_size, failProb, List.find?_append, h2 i le_rfl, hg]
    rw [show (grindP (k + 1) i).bind (Vg c) = .query (z i) fun a =>
      (if good a then OProg.ret (z i) else grindP k (i + 1)).bind (Vg c) from rfl,
      failProb.eq_2, h2 i le_rfl]
    simp only [step, avg_bad]
    rw [pow_succ (2⁻¹ : ℝ≥0) k, mul_comm]

/-- **Grinding with `k ≥ 1` nonces fails with probability exactly `2^-k`.** -/
theorem grind_exact (c : Digest) {k : ℕ} (hk : 0 < k) :
    failProb ((grindP k 0).bind (Vg c)) [] = 2⁻¹ ^ k :=
  grind_fail c k 0 [] ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩ (by omega)

/-- **128 nonces are complete at the cap**, for every relation. -/
theorem grind128_complete (R : Digest → Wit → Prop) :
    CompleteWithError R (fun _ _ => grindP 128 0) Vg completenessCap :=
  fun c _ _ => (grind_exact c (by decide)).le

/-- **127 nonces are not**, for any relation with a witness. -/
theorem grind127_not_complete (R : Digest → Wit → Prop) {c : Digest} {w : Wit} (h : R c w) :
    ¬ CompleteWithError R (fun _ _ => grindP 127 0) Vg completenessCap := fun hc => by
  have := hc c w h
  rw [grind_exact c (by decide), completenessCap] at this
  exact absurd this (not_le.mpr (pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num)
    (by norm_num)))

/-! ## A fixed query: no prover gets below `1/2` -/

/-- Accept iff the answer to the fixed query `z 0` is good. -/
def Vh (_ : Digest) (_ : Proof) : OProg Bool := .query (z 0) fun a => .ret (good a)

theorem fixed_known (c : Digest) : ∀ (p : OProg Proof) (L : Log) (e : ByteArray × Digest),
    L.find? (fun e => e.1 = z 0) = some e →
      failProb (p.bind (Vh c)) L = if good e.2 then 0 else 1
  | .ret _, L, e, he => by
    simp only [OProg.bind, Vh, failProb, he]
  | .query q k, L, e, he => by
    simp only [OProg.bind, failProb]
    split
    · exact fixed_known c _ L e he
    · simp only [fun a => fixed_known c (k a) (L ++ [(q, a)]) e (by simp [List.find?_append, he]),
        avg_const]

theorem fixed_fresh (c : Digest) : ∀ (p : OProg Proof) (L : Log),
    L.find? (fun e => e.1 = z 0) = none → failProb (p.bind (Vh c)) L = 2⁻¹
  | .ret _, L, he => by
    simp only [OProg.bind, Vh, failProb, he]
    simpa using avg_bad 1
  | .query q k, L, he => by
    simp only [OProg.bind, failProb]
    split
    · exact fixed_fresh c _ L he
    · rename_i hq
      by_cases h0 : q = z 0
      · subst h0
        simp only [fun a => fixed_known c (k a) (L ++ [(z 0, a)]) (z 0, a)
          (by simp [List.find?_append, he])]
        simpa using avg_bad 1
      · simp only [fun a => fixed_fresh c (k a) (L ++ [(q, a)]) (by
          simp [List.find?_append, he, h0]), avg_const]

/-- **The fixed-query verifier is complete at `1/2`**, with every prover. -/
theorem fixed_complete_half (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof) :
    CompleteWithError R P Vh 2⁻¹ := fun c w _ => (fixed_fresh c (P c w) [] rfl).le

/-- **No prover makes it complete at `δ < 1/2`.** -/
theorem fixed_not_complete (R : Digest → Wit → Prop) (P : Digest → Wit → OProg Proof)
    {c : Digest} {w : Wit} (h : R c w) {δ : ℝ≥0} (hδ : δ < 2⁻¹) :
    ¬ CompleteWithError R P Vh δ := fun hc =>
  absurd ((fixed_fresh c (P c w) [] rfl).symm.trans_le (hc c w h)) (not_le.mpr hδ)

end RecursionFast.Controls.Completeness

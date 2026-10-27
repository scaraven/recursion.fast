/-
  RecursionFast.Library.Prob  (UNTRUSTED, kernel-checked)

  **The calculus of the contract's lazy-sampling probability `prob`** (`Contract/Security.lean`,
  V4-A10), on which the paper theorem and the tree's composition rest.

  * `expect F p L`: the expectation of `F x L'` over the end `(x, L')` of the run of `p` from the
    table `L`, the oracle lazily sampled as in `prob`; `prob_eq_expect`: `prob` is the
    expectation of the indicator `ind`. `avg_le`, `avg_const`, `expect_const`, `prob_le_one`.
  * Monotonicity: `expect_mono`, `prob_mono`, and along an invariant of the table that every
    fresh answer keeps (`expect_mono_of_inv`, `prob_mono_of_inv`; the composition uses the log's
    functionality).
  * **The union bound** (`prob_exists_le`), through linearity (`expect_sum`).
  * **Sequential composition**: `expect_bind`, `prob_bind` (`p.bind f` is `p`, then `f` on its
    output from the table `p` ended with); `prob_bind_of_runLog` (a program that the table
    already answers asks nothing fresh, so it changes nothing).
  * **A program that keeps its own log** (`withLog p L`): it asks those of `p`'s queries that its
    record does not answer, records them, and returns `p`'s output with the table that lazy
    sampling ends with (`expect_withLog`), asking no more than `p` (`queries_withLog_le`). It is
    how an adversary outputs a function of its own query log (`Library/KS.lean`, `KS.select`).
-/
import RecursionFast.Library.Security
import RecursionFast.Library.Oracle

open scoped NNReal

namespace RecursionFast
variable {α β : Type}

local notation "N" => ((2 : ℝ≥0) ^ 256)

theorem N_pos : 0 < N := by positivity

/-- The average over the answers of a function bounded by `b` is at most `b`. -/
theorem avg_le {f : Digest → ℝ≥0} {b : ℝ≥0} (h : ∀ a, f a ≤ b) : N⁻¹ * ∑ a, f a ≤ b := by
  have : ∑ a, f a ≤ N * b := by
    calc ∑ a, f a ≤ ∑ _a : Digest, b := Finset.sum_le_sum fun a _ => h a
      _ = N * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, fintype_card_digest, Nat.cast_pow,
          Nat.cast_ofNat]
  calc N⁻¹ * ∑ a, f a ≤ N⁻¹ * (N * b) := by gcongr
    _ = b := by rw [← mul_assoc, inv_mul_cancel₀ N_pos.ne', one_mul]

/-- The average of a constant over the `2^256` answers. -/
theorem avg_const (x : ℝ≥0) : N⁻¹ * ∑ _a : Digest, x = x := by
  rw [Finset.sum_const, Finset.card_univ, fintype_card_digest, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-! ## Expectation -/

/-- **The expectation of `F`** at the end of the run of `p` from the table `L`, the oracle lazily
sampled as in `prob`. -/
noncomputable def expect (F : α → Log → ℝ≥0) : OProg α → Log → ℝ≥0
  | .ret x, L => F x L
  | .query q k, L =>
    match L.find? fun e => e.1 = q with
    | some e => expect F (k e.2) L
    | none => N⁻¹ * ∑ a : Digest, expect F (k a) (L ++ [(q, a)])

/-- The indicator of `B`. -/
noncomputable def ind (B : α → Log → Prop) (x : α) (L : Log) : ℝ≥0 := by
  classical exact if B x L then 1 else 0

theorem ind_of {B : α → Log → Prop} {x : α} {L : Log} (h : B x L) : ind B x L = 1 := by
  classical simp [ind, h]

theorem ind_of_not {B : α → Log → Prop} {x : α} {L : Log} (h : ¬ B x L) : ind B x L = 0 := by
  classical simp [ind, h]

theorem ind_le_ind {B B' : α → Log → Prop} {x : α} {L : Log} (h : B x L → B' x L) :
    ind B x L ≤ ind B' x L := by
  by_cases hb : B x L
  · rw [ind_of hb, ind_of (h hb)]
  · rw [ind_of_not hb]; exact bot_le

theorem ind_le_one (B : α → Log → Prop) (x : α) (L : Log) : ind B x L ≤ 1 := by
  by_cases hb : B x L
  · rw [ind_of hb]
  · rw [ind_of_not hb]; exact zero_le_one

/-- **`prob` is the expectation of the indicator.** -/
theorem prob_eq_expect (B : α → Log → Prop) :
    ∀ (p : OProg α) (L : Log), prob B p L = expect (ind B) p L
  | .ret _, _ => rfl
  | .query q k, L => by
    simp only [prob, expect]
    cases L.find? fun e => decide (e.1 = q) with
    | some e => exact prob_eq_expect B _ _
    | none => simp only [prob_eq_expect B]

theorem prob_ret (B : α → Log → Prop) (x : α) (L : Log) : prob B (.ret x) L = ind B x L := rfl

theorem expect_mono_of_inv (I : Log → Prop)
    (hI : ∀ L q a, I L → L.find? (fun e => e.1 = q) = none → I (L ++ [(q, a)]))
    {F G : α → Log → ℝ≥0} (h : ∀ x L, I L → F x L ≤ G x L) :
    ∀ (p : OProg α) (L : Log), I L → expect F p L ≤ expect G p L
  | .ret x, L, hL => h x L hL
  | .query q k, L, hL => by
    simp only [expect]
    split
    · exact expect_mono_of_inv I hI h _ L hL
    · rename_i hf
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
        expect_mono_of_inv I hI h _ _ (hI L q a hL hf)) bot_le

theorem expect_mono {F G : α → Log → ℝ≥0} (h : ∀ x L, F x L ≤ G x L) (p : OProg α) (L : Log) :
    expect F p L ≤ expect G p L :=
  expect_mono_of_inv (fun _ => True) (fun _ _ _ _ _ => trivial) (fun x L _ => h x L) p L trivial

theorem expect_const (c : ℝ≥0) : ∀ (p : OProg α) (L : Log), expect (fun _ _ => c) p L = c
  | .ret _, _ => rfl
  | .query q k, L => by
    simp only [expect]
    split
    · exact expect_const c _ _
    · simp only [expect_const c, avg_const]

/-- **Linearity over a finite sum.** -/
theorem expect_sum {ι : Type} (s : Finset ι) (F : ι → α → Log → ℝ≥0) :
    ∀ (p : OProg α) (L : Log),
      expect (fun x L => ∑ i ∈ s, F i x L) p L = ∑ i ∈ s, expect (F i) p L
  | .ret _, _ => rfl
  | .query q k, L => by
    simp only [expect]
    cases L.find? fun e => decide (e.1 = q) with
    | some e => exact expect_sum s F _ _
    | none => simp only [expect_sum s F, Finset.mul_sum]; exact Finset.sum_comm

/-- **Sequential composition**: the expectation over `p.bind f` is the expectation over `p` of
the expectation over `f` of its output, from the table `p` ended with. -/
theorem expect_bind (F : β → Log → ℝ≥0) (f : α → OProg β) :
    ∀ (p : OProg α) (L : Log),
      expect F (p.bind f) L = expect (fun x L' => expect F (f x) L') p L
  | .ret _, _ => rfl
  | .query q k, L => by
    simp only [OProg.bind, expect]
    split
    · exact expect_bind F f _ _
    · simp only [expect_bind F f]

/-- A program that the table answers asks nothing fresh: what follows it starts from the same
table. -/
theorem expect_bind_of_runLog (F : β → Log → ℝ≥0) (f : α → OProg β) {L : Log} :
    ∀ (p : OProg α) {b : α}, p.runLog L = some b → expect F (p.bind f) L = expect F (f b) L
  | .ret _, _, h => by cases h; rfl
  | .query q k, b, h => by
    simp only [OProg.runLog] at h
    cases hf : L.find? (fun e => decide (e.1 = q)) with
    | none => simp [hf] at h
    | some e =>
      simp only [hf, Option.bind_some] at h
      simp only [OProg.bind, expect, hf]
      exact expect_bind_of_runLog F f (k e.2) h

/-! ## Probability -/

theorem prob_le_one (B : α → Log → Prop) (p : OProg α) (L : Log) : prob B p L ≤ 1 :=
  (prob_eq_expect B p L).trans_le
    ((expect_mono (fun x L => ind_le_one B x L) p L).trans (expect_const 1 p L).le)

theorem prob_mono_of_inv (I : Log → Prop)
    (hI : ∀ L q a, I L → L.find? (fun e => e.1 = q) = none → I (L ++ [(q, a)]))
    {B B' : α → Log → Prop} (h : ∀ x L, I L → B x L → B' x L) (p : OProg α) {L : Log}
    (hL : I L) : prob B p L ≤ prob B' p L := by
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_mono_of_inv I hI (fun x L hL => ind_le_ind (h x L hL)) p L hL

theorem prob_mono {B B' : α → Log → Prop} (h : ∀ x L, B x L → B' x L) (p : OProg α) (L : Log) :
    prob B p L ≤ prob B' p L :=
  prob_mono_of_inv (fun _ => True) (fun _ _ _ _ _ => trivial) (fun x L _ => h x L) p trivial

/-- An event that never holds has probability `0`. -/
theorem prob_eq_zero {B : α → Log → Prop} (h : ∀ x L, ¬ B x L) (p : OProg α) (L : Log) :
    prob B p L = 0 := by
  rw [prob_eq_expect]
  exact le_antisymm ((expect_mono (fun x L => (ind_of_not (h x L)).le) p L).trans
    (expect_const 0 p L).le) bot_le

/-- **The union bound.** -/
theorem prob_exists_le {ι : Type} (s : Finset ι) (B : ι → α → Log → Prop) (p : OProg α)
    (L : Log) : prob (fun x L => ∃ i ∈ s, B i x L) p L ≤ ∑ i ∈ s, prob (B i) p L := by
  simp only [prob_eq_expect]
  rw [← expect_sum s (fun i => ind (B i))]
  refine expect_mono (fun x L => ?_) p L
  by_cases h : ∃ i ∈ s, B i x L
  · obtain ⟨i, hi, hb⟩ := h
    rw [ind_of ⟨i, hi, hb⟩, ← ind_of (B := B i) hb]
    exact Finset.single_le_sum (f := fun j => ind (B j) x L) (fun _ _ => bot_le) hi
  · rw [ind_of_not h]; exact bot_le

theorem prob_bind (B : β → Log → Prop) (p : OProg α) (f : α → OProg β) (L : Log) :
    prob B (p.bind f) L = expect (fun x L' => prob B (f x) L') p L := by
  simp only [prob_eq_expect, expect_bind]

theorem prob_bind_of_runLog (B : β → Log → Prop) (f : α → OProg β) {L : Log} {p : OProg α}
    {b : α} (h : p.runLog L = some b) : prob B (p.bind f) L = prob B (f b) L := by
  simp only [prob_eq_expect, expect_bind_of_runLog _ f p h]

/-! ## A program that keeps its own log -/

/-- **`p`, keeping its log**: the queries of `p` that the record `L` does not answer are asked and
recorded; `p`'s output is returned with the final record. -/
def withLog : OProg α → Log → OProg (α × Log)
  | .ret x, L => .ret (x, L)
  | .query q k, L =>
    match L.find? fun e => e.1 = q with
    | some e => withLog (k e.2) L
    | none => .query q fun a => withLog (k a) (L ++ [(q, a)])

/-- **The record is the table**: run from the table `L` with the record `L`, `withLog p` ends
with `p`'s output and the table lazy sampling ends with. -/
theorem expect_withLog (F : α × Log → Log → ℝ≥0) :
    ∀ (p : OProg α) (L : Log), expect F (withLog p L) L = expect (fun x L' => F (x, L') L') p L
  | .ret _, _ => rfl
  | .query q k, L => by
    cases hf : L.find? (fun e => decide (e.1 = q)) with
    | some e => simp only [withLog, expect, hf]; exact expect_withLog F _ _
    | none => simp only [withLog, expect, hf, expect_withLog F]

/-- `withLog p` asks no more queries than `p` under an oracle consistent with the record. -/
theorem queries_withLog_le (H : ByteArray → Digest) :
    ∀ (p : OProg α) (L : Log), Consistent H L →
      ((withLog p L).queries H).length ≤ (p.queries H).length
  | .ret _, _, _ => le_rfl
  | .query q k, L, hH => by
    cases hf : L.find? (fun e => decide (e.1 = q)) with
    | some e =>
      simp only [withLog, hf, OProg.queries, List.length_cons, hH q e hf]
      exact (queries_withLog_le H _ L hH).trans (Nat.le_succ _)
    | none =>
      simp only [withLog, hf, OProg.queries, List.length_cons]
      exact Nat.succ_le_succ (queries_withLog_le H _ _ (consistent_append_self hH))

end RecursionFast

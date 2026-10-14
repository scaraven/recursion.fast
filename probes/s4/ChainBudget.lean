import RecursionFast.Controls.Extractor
import RecursionFast.Library.RbrSound
/-! **Fix pass (S4-A9, S4-A14).** `B(k)` is now the total over the calls, split as the submitter
declares (`ExtractorImage.fuel`). Part (a)
(`resumeImage` … `chain_round0`) and the chained-search definitions of part (b) (`padShape`, `St`,
`step`, `finish`, `WM`, `callAt`, `chainE`) moved to `Controls/Extractor.lean`, which adds the
negative control `chain_search_fails`. This file keeps `chain_secure` and the arithmetic of (c)
as the record of what the **per-call** reading (`B(k)` steps per call) allowed: with `2^10`
padding rounds and `2^54 - 3` candidates per call at class 20. Under the split fuel a call at
`n = 2^10` has fewer than `2^47` steps, so `chain_search_fails` applies.

S4 review probe (finding S4-M1): the fuel bound is **per call**; the knowledge guarantee is
for the composed extractor, `n + 1` calls, and the calls can share one computation through the
witness words.

* **(a) The machine.** `resumeImage` (`probes/s4/asm/resume.S`, 34 instructions) is the
  brute-force image of `Controls/Extractor.lean` made resumable: its search state `[flag, c]`
  travels in the witness section. At class 20, on a three-round transcript, `extractOut` tries
  candidates `0 … 3`, `extractMid 2` tries `4 … 7` and `extractMid 1` finds the secret `9`:
  the chain finds what no single call of the image does (`chain_finds`), and the composed
  extractor of `Library/RbrSound.lean` (`chain`) returns the preimage (`chain_round0`).
* **(b) The laws.** `chain_secure`: on any `n` rounds, the accept-all verifier is `SecureWith`
  (complete, `RbrKS` at error `0`, the cap) for the relation "`f c = x`" of any bijection `f`
  of 64-bit words, with the extractor whose every call tries `T` candidates, as soon as
  `(n + 1)·T ≥ 2^64`. Nothing in `KSF` bounds the number of candidates per extraction by the
  per-call budget: the state function threads the search state. The rounds may be empty
  challenge rounds (`padShape`: admissible, one value each, so free for the verifier and for
  the error budget).
* **(c) The arithmetic.** At class 20 one call of the brute-force loop tests `2^54 - 3`
  candidates (`brute_none`, `brute_steps_exceed`), so `n = 2^10 ≤ roundCap` rounds enumerate
  `2^64` (`rounds_suffice_20`). In general the composed budget is
  `(n + 1)·B(k) < 2^(2k+31)` (`composed_budget_lt`), and at the round cap it covers `2^64`
  candidates of 64 steps at every class (`composed_budget_ge`).
-/

open scoped NNReal
namespace RecursionFast.Probe.Chain
open RecursionFast RecursionFast.Controls

/-! ## (b) The laws: per-call search budget `T`, total `(n + 1)·T` -/

section Laws
variable (f : Word → Word) (T n : ℕ) (sh : Fin n → Round)

/-- `n` **empty** challenge rounds (the definition is `Controls.padShape`). -/
example : padShape n = fun _ => .chal 0 [] := rfl

/-- Some value of every round (the trivial prover's messages). -/
def Round.dflt : (r : Round) → r.Ty
  | .msg _ => fun _ => 0
  | .chal _ _ => (fun _ => 0, fun _ => 0)

/-- The invariant after `calls` calls. -/
def Inv (x : Word) (calls : ℕ) : St → Prop
  | .inr w => f w = x
  | .inl c => calls * T ≤ c ∧ ∀ d < c, f (BitVec.ofNat 64 d) ≠ x

theorem step_inv {x : Word} {calls : ℕ} {s : St} (h : Inv f T x calls s) :
    Inv f T x (calls + 1) (step f T x s) := by
  cases s with
  | inr w => exact h
  | inl c =>
    obtain ⟨hc, hlt⟩ := h
    simp only [step]
    split
    · rename_i i hi
      simpa [Inv] using List.find?_some hi
    · rename_i hn
      refine ⟨by rw [Nat.succ_mul]; omega, fun d hd => ?_⟩
      by_cases hdc : d < c
      · exact hlt d hdc
      · have := List.find?_eq_none.mp hn (d - c) (List.mem_range.mpr (by omega))
        simpa [Nat.add_sub_cancel' (Nat.le_of_not_lt hdc)] using this

/-- If `2^64` candidates are covered, the last call returns the preimage. -/
theorem finish_inv (hf : Function.Bijective f) {x : Word} {calls : ℕ} {s : St}
    (h : Inv f T x calls s) (hT : 2 ^ 64 ≤ (calls + 1) * T) : f (finish f T x s) = x := by
  have h' := step_inv f T h
  unfold finish
  split
  · rename_i w hw; rw [hw] at h'; exact h'
  · rename_i c hc
    rw [hc] at h'
    obtain ⟨hcT, hlt⟩ := h'
    obtain ⟨p, hp⟩ := hf.2 x
    have := hlt p.toNat (lt_of_lt_of_le p.isLt (le_trans hT hcT))
    simp [hp] at this

/-- The state: "`f w = x`" before round 0; the invariant after round `j ≥ 1` (`n + 1 - j` calls
done). It ignores the transcript. -/
def chainState (j : Fin (n + 1)) (x : Word) : WM n j → Prop :=
  Fin.cases (motive := fun j => WM n j → Prop) (fun w => f w = x)
    (fun i s => Inv f T x (n - i.val) s) j

/-- One call backwards keeps the state true (message and challenge rounds alike). -/
theorem chainState_back (hf : Function.Bijective f) (hT : 2 ^ 64 ≤ (n + 1) * T) (m : Fin n)
    (x : Word) (s : WM n m.succ) (h : chainState f T n m.succ x s) :
    chainState f T n m.castSucc x (callAt f n (fun _ => T) x m.castSucc s) := by
  obtain ⟨m, hm⟩ := m
  cases m with
  | zero =>
    have h1 : Inv f T x (n - 0) s := h
    exact finish_inv f T hf h1 (by omega)
  | succ m =>
    have h1 : Inv f T x (n - (m + 1)) s := h
    show Inv f T x (n - m) (step f T x s)
    have := step_inv f T h1
    rwa [show n - (m + 1) + 1 = n - m by omega] at this

/-- The state function of the chained search, for the accept-all verifier. -/
def chainKSF (hf : Function.Bijective f) (hT : 2 ^ 64 ≤ (n + 1) * T) :
    KSF {p : Word × Word | f p.2 = p.1} Set.univ (fun _ _ => some ()) (chainE f n (fun _ => T) sh) where
  toFun j x _ := chainState f T n j x
  empty _ _ := Iff.rfl
  next m x _ _ s h := chainState_back f T n hf hT m.1 x s h
  full x _ _ _ _ _ := by
    cases n with
    | zero =>
      exact finish_inv f T hf (calls := 0) (s := .inl 0) ⟨by simp, by simp⟩ (by simpa using hT)
    | succ n =>
      show Inv f T x (n + 1 - n) (step f T x (.inl 0))
      rw [show n + 1 - n = 0 + 1 by omega]
      exact step_inv f T ⟨by simp, by simp⟩

/-- No challenge is ever bad: the state goes back through challenge rounds as through messages. -/
theorem chain_noBad (hf : Function.Bijective f) (hT : 2 ^ 64 ≤ (n + 1) * T) (c : ChallengeIdx sh)
    (x : Word) (tr : Transcript sh c.1.castSucc) (ch : (sh c.1).Ty) :
    ¬ (chainKSF f T n sh hf hT).Bad c x tr ch :=
  fun ⟨w, hno, hyes⟩ => hno (chainState_back f T n hf hT c.1 x w hyes)

/-- **Accept-all is "knowledge-sound" for any 64-bit permutation relation**, on any round shapes,
once `n + 1` calls of `T` candidates cover the `2^64` words: complete, `RbrKS` at error `0` (no
challenge is bad), the cap. The state function threads the search through the witness. -/
theorem chain_secure (hf : Function.Bijective f) (hT : 2 ^ 64 ≤ (n + 1) * T) :
    SecureWith {p : Word × Word | f p.2 = p.1} Set.univ
      ({ next := fun _ _ m _ => Round.dflt (sh m.1), output := fun _ _ _ => ((), ()) } :
        Strategy sh Word Word Unit Unit)
      (fun _ _ => some ()) (chainE f n (fun _ => T) sh) (fun _ => 0) where
  complete _ _ _ _ := ⟨rfl, Set.mem_univ _⟩
  sound := ⟨chainKSF f T n sh hf hT, fun x c tr => by
    have : IsEmpty {ch // (chainKSF f T n sh hf hT).Bad c x tr ch} :=
      ⟨fun ⟨ch, hb⟩ => chain_noBad f T n sh hf hT c x tr ch hb⟩
    simp⟩
  cap _ := zero_le

/-- The hypotheses are satisfiable at the class-20 numbers (`2^10` rounds, `2^54 - 3` candidates
per call), with the bijection `c ↦ c ⊕ 0x1b`, on **empty challenge rounds** (`padShape`). -/
example : SecureWith {p : Word × Word | p.2 ^^^ 0x1b = p.1} Set.univ
    ({ next := fun _ _ m _ => Round.dflt (padShape (2 ^ 10) m.1),
       output := fun _ _ _ => ((), ()) } :
      Strategy (padShape (2 ^ 10)) Word Word Unit Unit)
    (fun _ _ => some ()) (chainE (· ^^^ 0x1b) (2 ^ 10) (fun _ => 2 ^ 54 - 3) (padShape _)) (fun _ => 0) :=
  chain_secure (· ^^^ 0x1b) (2 ^ 54 - 3) (2 ^ 10) _
    (Function.Involutive.bijective fun c => by simp [BitVec.xor_assoc]) (by norm_num)

end Laws

/-! ## (c) The arithmetic -/

/-- At class 20, `2^10` rounds of the brute-force loop (`2^54 - 3` candidates per call, the most
`brute_steps_exceed` allows) cover `2^64` candidates, within the round cap. -/
theorem rounds_suffice_20 : 2 ^ 64 ≤ (2 ^ 10 + 1) * (2 ^ 54 - 3) ∧ 2 ^ 10 ≤ roundCap :=
  ⟨by norm_num, by unfold roundCap; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)⟩

/-- The composed extractor's budget: `(n + 1)·B(k) < 2^(2k+31)` for `n ≤ roundCap`. At
`k = 20` that is `2^71`, at `k = 28` `2^87`: below `2^128` (two words), above `2^64` (one). -/
theorem composed_budget_lt {n k : ℕ} (hn : n ≤ roundCap) :
    (n + 1) * 2 ^ (2 * k + 16) < 2 ^ (2 * k + 31) := by
  have e : 2 ^ (2 * k + 31) = 2 ^ 15 * 2 ^ (2 * k + 16) := by
    rw [show 2 * k + 31 = 15 + (2 * k + 16) by omega, Nat.pow_add]
  have : n + 1 < 2 ^ 15 := by unfold roundCap at hn; omega
  rw [e]
  exact Nat.mul_lt_mul_of_pos_right this (by positivity)

/-- ... and at every class in range, `roundCap + 1` calls cover `2^64` candidates at `2^6` steps
per candidate: no class protects a one-word secret whose test costs at most 64 steps. -/
theorem composed_budget_ge {k : ℕ} (hk : 20 ≤ k) :
    2 ^ 64 * 2 ^ 6 ≤ (roundCap + 1) * 2 ^ (2 * k + 16) := by
  calc 2 ^ 64 * 2 ^ 6 = 2 ^ 14 * 2 ^ (2 * 20 + 16) := by norm_num
    _ ≤ (roundCap + 1) * 2 ^ (2 * k + 16) := Nat.mul_le_mul (by simp [roundCap])
        (Nat.pow_le_pow_right (by norm_num) (by omega))

#print axioms chain_secure
#print axioms composed_budget_lt
#print axioms composed_budget_ge

end RecursionFast.Probe.Chain

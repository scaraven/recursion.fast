import RecursionFast.Controls.Extractor
/-! (Fix pass: ported to `Controls/Extractor.lean` as `clmul_lt`, `bruteHash_lt`, `bruteHash_top`,
`bruteHash_ne_top`, `sTop`, `brute_nonvacuous`; this copy is kept as the review's record.)

S4 review probe: the hypothesis of the Q1 negative control is satisfiable by a statement
that **has** a witness, so `brute_extractMid_nil` is not vacuous and it is the fuel, not the
absence of a preimage, that empties the extracted witness.

`brute_extractMid_nil`'s docstring asserts this ("`bruteHash` is injective below `2^60`"), but
no control proves it. Here: `bruteHash (2^63) = 2^63` (a preimage exists), and no `c < 2^54`
maps to `2^63`, because `clmul(c, 0x1b) < 2^59` for `c < 2^54` (a degree bound). Hence at the
statement `x₀ = 2^63` the brute-force image's extractor returns `[]` at class 20. -/

namespace RecursionFast.Probe
open RecursionFast RecursionFast.Controls

private theorem foldl_inv {α β : Type} (P : α → Prop) (f : α → β → α) (l : List β) (x : α)
    (hx : P x) (hf : ∀ a b, b ∈ l → P a → P (f a b)) : P (l.foldl f x) := by
  induction l generalizing x with
  | nil => exact hx
  | cons b l ih =>
    exact ih (f x b) (hf x b (by simp) hx) (fun a b' hb => hf a b' (by simp [hb]))

/-- Degree bound for the carry-less product: `a < 2^p`, `b < 2^q` give `a ⊗ b < 2^(p+q)`. -/
theorem clmul_lt {a b : Word} {p q : ℕ} (ha : a.toNat < 2 ^ p) (hb : b.toNat < 2 ^ q) :
    (K.clmul a b).toNat < 2 ^ (p + q) := by
  unfold K.clmul
  rw [Fin.foldl_eq_finRange_foldl]
  refine foldl_inv (fun acc : BitVec 128 => acc.toNat < 2 ^ (p + q)) _ _ _
    (by simp) fun acc i _ hacc => ?_
  split
  · rename_i hbit
    rw [BitVec.toNat_xor]
    refine Nat.xor_lt_two_pow hacc ?_
    have hip : i.val < p := by
      by_contra h
      have : a.toNat < 2 ^ i.val :=
        lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [BitVec.getLsbD, Nat.testBit_eq_false_of_lt this] at hbit
      exact absurd hbit (by simp)
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
    have hb' : b.toNat % 2 ^ 128 = b.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hb', Nat.shiftLeft_eq]
    calc b.toNat * 2 ^ i.val % 2 ^ 128 ≤ b.toNat * 2 ^ i.val := Nat.mod_le _ _
      _ < 2 ^ q * 2 ^ i.val := Nat.mul_lt_mul_of_pos_right hb (by positivity)
      _ ≤ 2 ^ (p + q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact hacc

/-- `bruteHash c < 2^59` for `c < 2^54`. -/
theorem bruteHash_lt {c : ℕ} (hc : c < 2 ^ 54) :
    (bruteHash (BitVec.ofNat 64 c)).toNat < 2 ^ 59 := by
  have h1 : (BitVec.ofNat 64 c).toNat < 2 ^ 54 := by simp; omega
  have h2 : (0x1b : Word).toNat < 2 ^ 5 := by decide
  have := clmul_lt h1 h2
  show ((K.clmul (BitVec.ofNat 64 c) 0x1b).setWidth 64).toNat < 2 ^ 59
  rw [BitVec.toNat_setWidth]
  exact lt_of_le_of_lt (Nat.mod_le _ _) this

/-- A preimage of `2^63` exists: `2^63` itself (`x^63 · (x^4+x^3+x+1)` truncated to 64 bits). -/
theorem bruteHash_top : bruteHash (BitVec.ofNat 64 (2 ^ 63)) = BitVec.ofNat 64 (2 ^ 63) := by
  decide +kernel

/-- ... and none below `2^54`. -/
theorem bruteHash_ne_top (c : ℕ) (hc : c < 2 ^ 54) :
    bruteHash (BitVec.ofNat 64 c) ≠ BitVec.ofNat 64 (2 ^ 63) := fun h => by
  have := bruteHash_lt hc
  rw [h] at this
  simp at this

/-- The statement `x₀ = 2^63` over `triv`. -/
def sTop : Layout K × Stmt := (triv, fun i => if i = 0 then ⟨BitVec.ofNat 64 (2 ^ 63)⟩ else 0)

/-- **The Q1 negative control fires on a statement with a preimage**: `bruteHash` has a preimage
of `x₀ = 2^63`, yet the brute-force extractor at class 20 returns `[]`. -/
theorem brute_nonvacuous :
    (∃ c : Word, bruteHash c = (sTop.2 0).bits) ∧
      ((bruteImage.toExtractor sh2).extractMid 1 sTop tr2 w3 : List Word) = [] := by
  refine ⟨⟨_, bruteHash_top⟩, ?_⟩
  refine brute_extractMid_nil bruteImage rfl sh2 1 sTop tr2 w3 ?_ (fun c hc => bruteHash_ne_top c hc)
  have : triv.words.length = 264 := by decide +kernel
  simp [sTop, this]

#print axioms brute_nonvacuous

end RecursionFast.Probe

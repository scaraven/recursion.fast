import Mathlib
/-! O25 review probe P1: type-level facts about the Candidate-E interface (F2 memo §9.1).
Self-contained sketch of the interface; no contract import. Checks only that certain terms are
well-typed and computable, and two small facts about the wrapper's `idxOf`. -/

namespace O25P1

abbrev Digest := Vector UInt8 32
def natLE (a : Digest) : ℕ := ∑ i : Fin 32, a[i.1].toNat * 256 ^ i.1
def idxOf (ℓ : ℕ) (a : Digest) (i : ℕ) : ℕ := natLE a / 2 ^ (i * ℓ) % 2 ^ ℓ

/-- The memo's `ChallengeOps` (E-3), with `idx` taking the width from `V`. -/
structure ChallengeOps (D F : Type) where
  squeezeF : D → F
  idx      : D → ℕ → ℕ → ℕ

/-- (a) `idx` at a `V`-chosen width is a full projection of the answer to `ℕ`
    when the wrapper fills it with `idxOf`: width 256, index 0 returns `natLE a`. -/
theorem sum_lt : ∀ (k : ℕ) (f : Fin k → ℕ), (∀ i, f i < 256) →
    ∑ i, f i * 256 ^ i.1 < 256 ^ k := by
  intro k
  induction k with
  | zero => intro f _; simp
  | succ k ih =>
    intro f hf
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun i => f i.castSucc) (fun i => hf _)
    have h2 := hf (Fin.last k)
    simp only [Fin.val_castSucc, Fin.val_last]
    calc _ < 256 ^ k + f (Fin.last k) * 256 ^ k := by omega
      _ ≤ 256 ^ k + 255 * 256 ^ k := by gcongr; omega
      _ = 256 ^ (k + 1) := by ring

theorem natLE_lt (a : Digest) : natLE a < 2 ^ 256 := by
  have := sum_lt 32 (fun i => a[i.1].toNat) (fun i => UInt8.toNat_lt _)
  unfold natLE; simpa using this

theorem idxOf_full (a : Digest) : idxOf 256 a 0 = natLE a := by
  unfold idxOf; rw [zero_mul, pow_zero, Nat.div_one]; exact Nat.mod_eq_of_lt (natLE_lt a)

/-- (b) Even at a fixed honest width ℓ, ⌈256/ℓ⌉ calls on ONE answer give every bit. -/
theorem idxOf_all_bits (ℓ : ℕ) (a : Digest) (i : ℕ) :
    idxOf ℓ a i = natLE a / 2 ^ (i * ℓ) % 2 ^ ℓ := rfl

/-- (c) The shape the type admits: a parametric, computable `V`-fragment that compares an
    interface output (in `ℕ`) with a number `V` computed itself (`loc`, standing for any
    function `V` evaluates on bytes it knows). Nothing in the Candidate-E type excludes it. -/
def cmpNat {D F : Type} (ops : ChallengeOps D F) (a : D) (loc : ℕ) : Bool :=
  decide (ops.idx a 256 0 = loc)

/-- (d) The same in `F` using only `CommRing F` and `DecidableEq F`: a prover-supplied element
    `β : F` (e.g. `squeezeF` of a proof digest slot) and a number `n` that `V` computed
    locally give an `F`-value `Σ bitᵢ(n) βⁱ`, compared with a challenge `x`. -/
def encodeF {F : Type} [CommRing F] (β : F) (n k : ℕ) : F :=
  ∑ i ∈ Finset.range k, (if n.testBit i then β ^ i else 0)

def cmpF {D F : Type} [CommRing F] [DecidableEq F] (ops : ChallengeOps D F)
    (a slot : D) (n : ℕ) : Bool :=
  decide (ops.squeezeF a = encodeF (ops.squeezeF slot) n 192)

/-- (e) A check that pins a prover-supplied `β` up to Galois conjugacy, written with the ring
    constants 0 and 1 only (here a toy degree-2 polynomial over GF(2)). -/
def pinned {F : Type} [CommRing F] [DecidableEq F] (β : F) : Bool :=
  decide (β ^ 2 + β + 1 = 0)

/-- (f) In a prime field, `Nat.cast` alone names every element: no prover help needed. -/
example : ((7 : ℕ) : ZMod 5) = (2 : ZMod 5) := by decide

end O25P1

#print axioms O25P1.idxOf_full
#eval O25P1.pinned (F := ZMod 7) 2   -- 4+2+1 = 7 = 0 : true

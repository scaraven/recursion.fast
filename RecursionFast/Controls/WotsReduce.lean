/-
# Controls: the reduction of EUF-CMA to a collision or a chain inversion (`Library/WotsReduce.lean`)

Positive (the inversion outcome is reached, for every secret function `sk`, symbolically: no hash
is evaluated). The forger that knows `sk` signs a fresh message `m` with the reference signer:
* at an unused index (`reduce_unused`: the record is empty) and at an index the record used for
  another message (`reduce_used`: key `0` signed `0x00…00`, the forger signs `0xFF…FF` with it),
  `wotsReduce` returns an inversion;
* at the used index, the chain the reduction compares is computed (`pick_used`, `decide
  +kernel`): chain `131`, the first whose digit of `0xFF…FF` (`3` on the 128 message chains, `0`
  on the checksum chains) is below the digit of `0x00…00` (`0` on the message chains,
  `0, 0, 0, 2, 1` on the checksum chains), so the forger's value there is the honest value at
  position `0`, below the revealed position `2`.

Negative (the inversion outcome is not satisfiable by revealed values).
* `not_inversion_of_revealed`: against a record holding `(σ.idx, m₀)`, a forgery on a message
  whose every digit is at least `m₀`'s (whose chain values are all computable forward from the
  issued signature) has no inversion outcome: every `WotsBreak` of it is a collision. By
  `wotsDigits_dominates` such a message is `m₀` itself (`not_inversion_issued`), which
  `wotsReduce` never sees (its forgeries are on fresh messages): the control is on the type, that
  `unrevealed` excludes every position the signer revealed. That a revealed value placed in a
  forgery on a fresh message fails `value` is no kernel fact: it needs the hash.
* `not_inversion_twice`: one index used for two messages (`0x00…00` and `0xFF…FF`) reveals every
  position of every chain of the key (one of their digits is `0` on every chain), so no forgery
  with that index has an inversion outcome: the reduction needs one index per message.

Negative (what the type does not say). `wotsBreak_nonempty`: `WotsBreak sk R m σ` is inhabited for
every forgery, by a pigeonhole collision (`Controls/Compose.lean`, `collision_nonempty`), so the
collision branch's content is the compiled `wotsReduce`; `collision_ne`, `no_self_collision`: a
`Collision` carries two different preimages.
-/
import RecursionFast.Library.WotsReduce
import RecursionFast.Controls.Signature
import RecursionFast.Controls.Compose

namespace RecursionFast.Controls.WotsReduce
open RecursionFast RecursionFast.Signer RecursionFast.WotsReduce

variable (sk : ℕ → ℕ → Digest)

/-- The all-`0x00` message. -/
def m0 : Digest := Vector.replicate 32 0

/-- The all-`0xFF` message. -/
def mF : Digest := Vector.replicate 32 0xFF

/-! ## Positive: a forger that knows the key is reduced to an inversion -/

/-- At an unused index (the record is empty), the honest signature of a fresh message reduces to
an inversion. -/
theorem reduce_unused (m : Digest) :
    (wotsReduce sk [] List.nodup_nil m (sign sk 0 m) (sigOk_sign sk 0 (by decide) m)
      (by simp)).IsInversion :=
  wotsReduce_sign sk [] _ (by decide) m _

theorem mF_ne_m0 : mF ≠ m0 := by decide

/-- At an index the record used for `0x00…00`, the honest signature of `0xFF…FF` with it reduces
to an inversion. -/
theorem reduce_used :
    (wotsReduce sk [(0, m0)] (by simp) mF (sign sk 0 mF) (sigOk_sign sk 0 (by decide) mF)
      (by simpa using mF_ne_m0.symm)).IsInversion :=
  wotsReduce_sign sk _ _ (by decide) mF _

/-- The chain compared at the used index: chain `131`, the first whose digit of the forged
`0xFF…FF` is below the signed `0x00…00`'s (`0 < 2`). -/
theorem pick_used :
    (pick [(0, m0)] (by simp) 0 mF (by simpa using mF_ne_m0.symm)).val = 131 := by
  decide +kernel

/-! ## Negative: revealed values are no inversion -/

/-- **A forgery computed forward from an issued signature is no inversion**: if the record holds
`(σ.idx, m₀)` and every digit of `m` is at least `m₀`'s, every outcome is a collision. -/
theorem not_inversion_of_revealed {R : List (ℕ × Digest)} {m m₀ : Digest} {σ : Sig}
    (hmem : (σ.idx, m₀) ∈ R) (hle : ∀ i, (wotsDigits m₀).getD i 0 ≤ (wotsDigits m).getD i 0)
    (b : WotsBreak sk R m σ) : b.IsCollision := by
  cases b with
  | collision => trivial
  | inversion i _ _ _ hu => exact absurd (hu m₀ hmem) (Nat.not_lt.mpr (hle i))

/-- **The issued signature is no inversion**: a forgery on a message the record signed with its
index has only collision outcomes. -/
theorem not_inversion_issued {R : List (ℕ × Digest)} {m : Digest} {σ : Sig}
    (hmem : (σ.idx, m) ∈ R) (b : WotsBreak sk R m σ) : b.IsCollision :=
  not_inversion_of_revealed sk hmem (fun _ => le_rfl) b

/-- One of the digits of `0x00…00` and `0xFF…FF` is `0` on every chain. -/
theorem digits_m0_mF (i : ℕ) : (wotsDigits m0).getD i 0 = 0 ∨ (wotsDigits mF).getD i 0 = 0 := by
  rw [m0, mF, Controls.Signature.wotsDigits_zero, Controls.Signature.wotsDigits_ff]
  by_cases hi : i < 133
  · have : ∀ i < 133, (List.replicate 128 0 ++ [0, 0, 0, 2, 1]).getD i 0 = 0 ∨
        (List.replicate 128 3 ++ [0, 0, 0, 0, 0]).getD i 0 = 0 := by decide
    exact this i hi
  · left; rw [List.getD_eq_default]; simp; omega

/-- **One index, two messages: no inversion.** If key `σ.idx` signed both `0x00…00` and
`0xFF…FF`, every position of every chain is revealed, and every outcome is a collision. -/
theorem not_inversion_twice {m : Digest} {σ : Sig}
    (b : WotsBreak sk [(σ.idx, m0), (σ.idx, mF)] m σ) : b.IsCollision := by
  cases b with
  | collision => trivial
  | inversion i _ _ _ hu =>
    rcases digits_m0_mF i with h | h
    · exact absurd (hu m0 (by simp)) (by rw [h]; omega)
    · exact absurd (hu mF (by simp)) (by rw [h]; omega)

/-! ## Negative: what the type does not say -/

/-- **The type is inhabited for every forgery**, by a pigeonhole collision: the collision
branch's content is the compiled `wotsReduce`. -/
theorem wotsBreak_nonempty (R : List (ℕ × Digest)) (m : Digest) (σ : Sig) :
    Nonempty (WotsBreak sk R m σ) :=
  Controls.Compose.collision_nonempty.map .collision

/-- A collision's two preimages differ. -/
theorem collision_ne (c : Collision) : c.x ≠ c.y := c.ne

/-- No byte string collides with itself. -/
theorem no_self_collision (x : List UInt8) : ¬ ∃ c : Collision, c.x = x ∧ c.y = x :=
  fun ⟨c, hx, hy⟩ => c.ne (hx.trans hy.symm)

end RecursionFast.Controls.WotsReduce

/-
# Baseline submission: negative control for the extractor's fuel split            (UNTRUSTED)

The declared split `![8, 0]` of `trivExtractor` is not decoration: `Secure` is stated about the
extractor with that split, and the call before round 0 must return a witness in `relK k`
(`KSF.empty` pins the state before round 0 to `relK`). `split0_not_secure`: the same protocol
with the same image and the same total, but with its 8 steps moved to the output call (`![0, 8]`),
is **not** secure at any class in range. The starved call returns `[]`, which is never in `relK`
(`nil_not_relK`), and completeness provides an accepted transcript on which the `next` law needs it.

The instance of `relK` is the one-chip, no-constraint layout `zeroLayout` with the all-zero
statement and a one-row table: a copy of the organiser's `triv`/`triv_relK`
(`RecursionFast/Controls/Negative.lean`), since a submission does not import the controls. This
negative control is the review's `S7Probe.split0_not_secure` (`probes/s7/Baseline.lean`, S7-m3).
-/
import RecursionFastCandidate.Protocol

namespace RecursionFastCandidate
open RecursionFast

/-- One public chip of 32 columns and no constraint (the organiser's `Controls.triv`). -/
def zeroLayout : Layout K :=
  ⟨[⟨32, ⟨0, 0, Fin.elim0, 0, Fin.elim0, Fin.elim0⟩, [], none⟩], fun _ => .eq, 0⟩

/-- The all-zero statement with the one-row all-zero table is in `relK k`, for every `k ≥ 5`. -/
theorem zeroLayout_relK (k : ℕ) (hk : 5 ≤ k) :
    ((zeroLayout, fun _ => 0), [⟨1, fun _ _ => 0⟩]) ∈ relK k := by
  have h32 : 32 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  refine ⟨⟨by decide, by decide, by simp [zeroLayout, Chip.entries],
    by simp [zeroLayout, Chip.fixedCells], by decide⟩, ?_⟩
  exact ⟨rfl, by simp [zeroLayout], by simp [zeroLayout, Gadget.holds],
    fun b => by simp [traffic, zeroLayout, balanced_zero], ⟨_, rfl, le_refl _, fun _ => rfl⟩,
    by simpa [zeroLayout] using h32⟩

section
variable (k : ℕ) (hk : 20 ≤ k ∧ k ≤ 28)

/-- `firstMsgImg` with all of its 8 steps moved to the output call. -/
def split0 : ExtractorImage k 1 where
  img := firstMsgImg
  img_le := by decide
  fuel := ![0, 8]
  fuel_le := by
    show 0 + (8 + 0) ≤ 2 ^ (2 * k + 16)
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 3 (2 * k + 13)))

/-- `P_triv` with the starved split. -/
abbrev P_split0 : Protocol k := { P_triv k hk with extractor := split0 k }

/-- **Negative control**: starving the call before round 0 breaks `Secure`, at every class in
range, whatever the errors. -/
theorem split0_not_secure : ¬ (P_split0 k hk).Secure := by
  rintro ⟨hc, ⟨kSF, -⟩, -⟩
  let s0 : Layout K × Stmt := (zeroLayout, fun _ => 0)
  have hacc := (hc s0 [⟨1, fun _ _ => 0⟩] (zeroLayout_relK k (by omega))
    (fun c => (triv_noChal k c).elim)).1
  have hfull := kSF.full s0 _ () () hacc (Set.mem_univ _)
  have h0 := (kSF.empty s0 _).mpr (kSF.next ⟨0, rfl⟩ s0 (Transcript.empty _) _ _ hfull)
  exact nil_not_relK k s0 h0

end

end RecursionFastCandidate

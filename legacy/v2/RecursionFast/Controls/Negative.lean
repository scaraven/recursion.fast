/-
# Controls (negative): trivial verifiers fail; the error cap is load-bearing

Carried over from v0.3 (`contract-v03/RecursionFast/Controls/Negative.lean`) to `relK k`. The
unsatisfiable statement is the layout `unsat` (`Controls/Layout.lean`: a public chip whose gadget
is `1 = 0`), which is admissible at every class; the satisfiable one is `triv` (a public
chip of 32 columns with no constraint), in `relK k` for every `k ≥ 5`.

* `acceptAll_no_KSF`: on a one-message schedule the accept-all verifier has no knowledge state
  function for `relK k` (the unsatisfiable statement is admissible, `unsat_admissible_of`, so
  this is not an artefact of inadmissible inputs).
* `rejectAll_not_complete`: the reject-all verifier is not perfectly complete (any schedule,
  any `k ≥ 5`); `rejectAll_not_secure`: no `Protocol k` (so `20 ≤ k ≤ 28`) whose verifier
  rejects everything is `Secure`.
* Cap control: on a one-challenge schedule the accept-all verifier is complete and has an RBR-KS
  state function at error **1** (`acceptAllChal_rbr_one`), but none at any error below 1, hence
  none at the cap (`acceptAllChal_not_secure`): `ε ≤ 2^-128` is what rejects it.

v0.3's A2-C1 control (an image that `Agrees` with the spec) is gone with `Agrees` (DESIGN §10).
-/
import RecursionFast.Contract.Protocol
import RecursionFast.Controls.Layout
import RecursionFast.Library.Challenges

open scoped NNReal

namespace RecursionFast.Controls
open RecursionFast

/-! ### Witnesses for `relK`: an unsatisfiable and a satisfiable statement -/

/-- `unsat` is admissible at every class. -/
theorem unsat_admissible_of (k : ℕ) : unsat.Admissible k :=
  ⟨by decide, by decide, by simp [unsat, Chip.entries, unsatGadget],
    by simp [unsat, Chip.fixedCells], by decide⟩

/-- `(unsat, x)` has no witness. -/
theorem unsat_not_relK (k : ℕ) (x : Stmt) (w : List (Table K)) : ((unsat, x), w) ∉ relK k :=
  fun h => unsat_neg k x w h.2

/-- One public chip of 32 columns, no constraint. -/
def triv : Layout K := ⟨[⟨32, freeGadget _, [], none⟩], fun _ => .eq, 0⟩

/-- The all-zero statement with the one-row all-zero table is in `relK k`, for every `k ≥ 5`. -/
theorem triv_relK (k : ℕ) (hk : 5 ≤ k) :
    ((triv, fun _ => 0), [⟨1, fun _ _ => 0⟩]) ∈ relK k := by
  have h32 : 32 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
  refine ⟨⟨by decide, by decide, by simp [triv, Chip.entries, freeGadget],
    by simp [triv, Chip.fixedCells], by decide⟩, ?_⟩
  exact ⟨rfl, by simp [triv], by simp [triv, Gadget.holds, freeGadget],
    fun b => by simp [traffic, triv, balanced_zero], ⟨_, rfl, le_refl _, fun _ => rfl⟩,
    by simpa [triv] using h32⟩

/-! ### Accept-all and reject-all -/

/-- A one-message schedule. -/
def oneMsg (o : OShape) : Fin 1 → Round := fun _ => .msg o

theorem acceptAll_no_KSF (k : ℕ) (o : OShape) {WitMid : Fin 2 → Type}
    (E : Extractor (oneMsg o) (Layout K × Stmt) (List (Table K)) Unit WitMid) :
    ¬ Nonempty (KSF (relK k) Set.univ (fun _ _ => some ()) E) := by
  rintro ⟨kSF⟩
  let s0 : Layout K × Stmt := (unsat, fun _ => 0)
  let v0 : OVal o := fun _ => 0
  let tr : Transcript (oneMsg o) (0 : Fin 1).succ :=
    (Transcript.empty (oneMsg o)).concat (m := 0) v0
  have hfull := kSF.full s0 tr () () rfl (Set.mem_univ _)
  have hnext := kSF.next ⟨0, rfl⟩ s0 (Transcript.empty _) v0 _ hfull
  exact unsat_not_relK k _ _ ((kSF.empty s0 _).mpr hnext)

theorem rejectAll_not_complete (k : ℕ) (hk : 5 ≤ k) {n : ℕ} (sh : Fin n → Round)
    (P : Strategy sh (Layout K × Stmt) (List (Table K)) Unit Unit) :
    ¬ PerfectComplete (relK k) Set.univ P (fun _ _ => none) :=
  fun h => by simpa using (h _ _ (triv_relK k hk) (fun _ => Classical.arbitrary _)).1

/-- **A protocol whose verifier accepts nothing is not secure** (its class is in range): no
query program run returns `true`. -/
theorem rejectAll_not_secure {k : ℕ} (P : Protocol k)
    (hrej : ∀ vk x ρ os, (P.verify vk x ρ).eval os ≠ some true) : ¬ P.Secure := fun h => by
  simpa [Protocol.specVerifier, hrej] using (h.complete _ _
    (triv_relK k ((by norm_num : 5 ≤ 20).trans P.k_range.1)) (fun _ => Classical.arbitrary _)).1

/-! ### The error cap is load-bearing -/

/-- One challenge round of one E element. -/
def oneChal : Fin 1 → Round := fun _ => .chal 1 []

/-- The only round is a challenge round. -/
def oneChalIdx : ChallengeIdx oneChal := ⟨0, rfl⟩

/-- The trivial extractor (keeps the witness, outputs the empty witness). -/
def keepE : Extractor oneChal (Layout K × Stmt) (List (Table K)) Unit (fun _ => List (Table K)) :=
  { eqIn := rfl, extractMid := fun _ _ _ w => w, extractOut := fun _ _ _ => [] }

/-- State "the statement is true" before the challenge, "true" after it. -/
def acceptAllKSF (k : ℕ) : KSF (relK k) Set.univ (fun _ _ => some ()) keepE where
  toFun := fun m s _ w => if m = 0 then (s, w) ∈ relK k else True
  empty := fun _ _ => by simp
  next := fun m => absurd m.2 (by simp [oneChal, Round.isMsg])
  full := fun _ _ _ _ _ _ => by simp

/-- Accept-all on one challenge is RBR-KS **at error 1**. -/
theorem acceptAllChal_rbr_one (k : ℕ) : RbrKS (acceptAllKSF k) (fun _ => 1) := by
  intro s c tr
  rw [one_mul]
  exact_mod_cast Finite.card_subtype_le _

/-- ... and complete (there is nothing to send). -/
theorem acceptAllChal_complete (k : ℕ) :
    PerfectComplete (relK k) Set.univ
      ({ next := fun _ _ m _ => absurd m.2 (by simp [oneChal, Round.isMsg]),
         output := fun _ _ _ => ((), ()) } : Strategy oneChal _ _ Unit Unit) (fun _ _ => some ()) :=
  fun _ _ _ _ => ⟨rfl, Set.mem_univ _⟩

theorem errorCap_lt_one : errorCap < 1 := by
  unfold errorCap
  exact pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)

/-- **No** state function for accept-all on one challenge has error `< 1`: on an unsatisfiable
statement every challenge is bad. So accept-all fails `SecureWith` exactly by the cap. -/
theorem acceptAllChal_err_ge_one (k : ℕ) {WitMid : Fin 2 → Type}
    {E : Extractor oneChal (Layout K × Stmt) (List (Table K)) Unit WitMid}
    (kSF : KSF (relK k) Set.univ (fun _ _ => some ()) E) (ε : ChallengeIdx oneChal → ℝ≥0)
    (h : RbrKS kSF ε) : 1 ≤ ε oneChalIdx := by
  let s0 : Layout K × Stmt := (unsat, fun _ => 0)
  have hall : ∀ ch, kSF.Bad oneChalIdx s0 (Transcript.empty _) ch := fun ch =>
    ⟨_, fun h0 => unsat_not_relK k _ _ ((kSF.empty s0 _).mpr h0),
      kSF.full s0 ((Transcript.empty oneChal).concat (m := 0) ch) () () rfl (Set.mem_univ _)⟩
  have hc := h s0 oneChalIdx (Transcript.empty _)
  have hcard : Nat.card {ch // kSF.Bad oneChalIdx s0 (Transcript.empty _) ch} =
      Nat.card (oneChal 0).Ty :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  rw [hcard] at hc
  have hpos : (0 : ℝ≥0) < Nat.card (oneChal 0).Ty := by exact_mod_cast natCard_pos _
  exact le_of_mul_le_mul_right ((one_mul _).trans_le hc) hpos

theorem acceptAllChal_not_secure (k : ℕ) {WitMid : Fin 2 → Type}
    (P : Strategy oneChal (Layout K × Stmt) (List (Table K)) Unit Unit)
    (E : Extractor oneChal (Layout K × Stmt) (List (Table K)) Unit WitMid)
    (ε : ChallengeIdx oneChal → ℝ≥0) :
    ¬ SecureWith (relK k) Set.univ P (fun _ _ => some ()) E ε := by
  rintro ⟨_, ⟨kSF, hk⟩, hcap⟩
  have h1 := acceptAllChal_err_ge_one k kSF ε hk
  exact absurd (lt_of_le_of_lt (hcap _) errorCap_lt_one) (not_lt.mpr h1)

end RecursionFast.Controls

/-
# Exploration: the paper theorem with certification moves                         (UNTRUSTED)

Probe P2, beyond the brief (W2 §A.6 says the extension is "one line"; this checks it). The
library's paper theorem (`Library/PaperTheorem.lean`) bounds the failure probability of a
contract game by `n · ε`. Here a game against the attested oracle (`Game`) may also **certify**
lists (the service checks `Valid` on the log so far; a valid list is recorded and the game goes
on with `true`, an invalid one leaves the log unchanged and goes on with `false`) and **attest**
hashes (answered by the log). Fresh queries are lazily sampled as in the library.

* `prob B G L`, `pot k G L`, `DepthLE G nq nc` (at most `nq` queries and `nc` certifications on
  every path): the library's definitions with the two new moves.
* `pot_le`: the stopped capped potential rises by at most `ε` per **query** and not at all per
  certification (the `cert` law). `prob_le_pot`: failure on a well-formed log within `logCap`
  forces the potential to `1`; every log the game reaches is well formed (`WF.snoc_ans`,
  `WF.snoc_cert`), which is what discharges `final`'s `WF` hypothesis.
* **`paper`**: the probability that the verifier accepts on the final log and the extractor
  returns no sound output is at most `nq · ε`, for `nq + nc ≤ logCap`: certifications are free.
* **`paper_tree`**: the probability that the root is accepted while its tree is neither extracted
  to every depth nor ends in a returned collision (`compose_all`) is at most `nq · ε`: one bound
  for every level of the tree.

Not covered, as in the library: lazy sampling against a uniformly random function, randomised
adversaries, and (here) the deployment's PRF in place of the random oracle (W2 §A.7, paper).
-/
import RecursionFast.Explore.Attested.Compose

open scoped NNReal

namespace RecursionFast.Explore.Attested.Paper

open Relativized PaperTheorem

/-- A game against the attested oracle: oracle queries, attestation requests, certifications. -/
inductive Game (α : Type) where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Ask the oracle `q`, continue with its answer. -/
  | query (q : ByteArray) (k : Digest → Game α)
  /-- Ask whether `h` is attested, continue with the bit. -/
  | attest (h : Digest) (k : Bool → Game α)
  /-- Ask the service to certify `xs`, continue with whether it accepted. -/
  | certify (xs : List Item) (k : Bool → Game α)

variable {α : Type} {V : Digest → Proof → AProg Bool} {E : Digest → Proof → ALog → Option Out}
  {ε : ℝ≥0}

local notation "N" => ((2 : ℝ≥0) ^ 256)

/-- At most `nq` queries and `nc` certifications on every path. -/
def DepthLE : Game α → ℕ → ℕ → Prop
  | .ret _, _, _ => True
  | .query _ _, 0, _ => False
  | .query _ c, nq + 1, nc => ∀ a, DepthLE (c a) nq nc
  | .attest _ c, nq, nc => ∀ b, DepthLE (c b) nq nc
  | .certify _ _, _, 0 => False
  | .certify _ c, nq, nc + 1 => ∀ b, DepthLE (c b) nq nc

open Classical in
/-- Lazy-sampling probability of ending in a leaf satisfying `B`, with the service's semantics
for attestation and certification. -/
noncomputable def prob (B : α → ALog → Prop) : Game α → ALog → ℝ≥0
  | .ret x, L => if B x L then 1 else 0
  | .query q c, L =>
    match firstAns L q with
    | some a => prob B (c a) L
    | none => N⁻¹ * ∑ a : Digest, prob B (c a) (L ++ [.ans q a])
  | .attest h c, L => prob B (c (attested L h)) L
  | .certify xs c, L =>
    if Valid L xs then prob B (c true) (L ++ [.cert xs]) else prob B (c false) L

open Classical in
/-- The capped potential, stopped at `1` before a query, in expectation at the end of the run. -/
noncomputable def pot (k : KStateA V E ε) : Game α → ALog → ℝ≥0
  | .ret _, L => min 1 (k.μ L)
  | .query q c, L =>
    if 1 ≤ k.μ L then 1 else
    match firstAns L q with
    | some a => pot k (c a) L
    | none => N⁻¹ * ∑ a : Digest, pot k (c a) (L ++ [.ans q a])
  | .attest h c, L => pot k (c (attested L h)) L
  | .certify xs c, L =>
    if Valid L xs then pot k (c true) (L ++ [.cert xs]) else pot k (c false) L

theorem prob_le_one (B : α → ALog → Prop) : ∀ (p : Game α) (L : ALog), prob B p L ≤ 1
  | .ret x, L => by classical simp only [prob]; split_ifs <;> simp
  | .query q c, L => by
    simp only [prob]
    split
    · exact prob_le_one B _ _
    · exact avg_le fun a => prob_le_one B _ _
  | .attest h c, L => by simp only [prob]; exact prob_le_one B _ _
  | .certify xs c, L => by
    classical simp only [prob]; split_ifs <;> exact prob_le_one B _ _

/-- **The stopped capped potential is a supermartingale** with drift `ε` per query and none per
certification. -/
theorem pot_le (k : KStateA V E ε) :
    ∀ (p : Game α) (nq nc : ℕ) (L : ALog), DepthLE p nq nc → L.length + nq + nc ≤ logCap →
      pot k p L ≤ min 1 (k.μ L) + nq * ε
  | .ret _, _, _, L, _, _ => by simp [pot]
  | .query _ _, 0, _, _, h, _ => h.elim
  | .query q c, nq + 1, nc, L, h, hlen => by
    simp only [pot]
    split_ifs with h1
    · simp [h1]
    · push Not at h1
      have hmin : min 1 (k.μ L) = k.μ L := min_eq_right h1.le
      split
      · calc pot k (c _) L ≤ min 1 (k.μ L) + nq * ε := pot_le k _ nq nc L (h _) (by omega)
          _ ≤ min 1 (k.μ L) + (nq + 1 : ℕ) * ε := by gcongr; omega
      · rename_i hf
        have hstep := k.step L q (by omega) h1 hf
        have hrec : ∀ a, pot k (c a) (L ++ [.ans q a]) ≤ k.μ (L ++ [.ans q a]) + nq * ε :=
          fun a => (pot_le k (c a) nq nc (L ++ [.ans q a]) (h a) (by simp; omega)).trans
            (by gcongr; exact min_le_right _ _)
        calc N⁻¹ * ∑ a, pot k (c a) (L ++ [.ans q a])
            ≤ N⁻¹ * ∑ a, (k.μ (L ++ [.ans q a]) + nq * ε) := by
              exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hrec a) bot_le
          _ = N⁻¹ * ∑ a, k.μ (L ++ [.ans q a]) + nq * ε := by
              rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ,
                nsmul_eq_mul, fintype_card_digest, Nat.cast_pow, Nat.cast_ofNat]
              congr 1
              rw [← mul_assoc, inv_mul_cancel₀ N_pos.ne', one_mul]
          _ ≤ N⁻¹ * ((k.μ L + ε) * N) + nq * ε := by
              have h2 := mul_le_mul_of_nonneg_left hstep (bot_le : (0 : ℝ≥0) ≤ N⁻¹)
              exact add_le_add h2 le_rfl
          _ = min 1 (k.μ L) + (nq + 1 : ℕ) * ε := by
              rw [hmin, mul_comm _ N, ← mul_assoc, inv_mul_cancel₀ N_pos.ne', one_mul]
              push_cast; ring
  | .attest h c, nq, nc, L, hd, hlen => by simp only [pot]; exact pot_le k _ nq nc L (hd _) hlen
  | .certify _ _, _, 0, _, h, _ => h.elim
  | .certify xs c, nq, nc + 1, L, h, hlen => by
    classical
    simp only [pot]
    split_ifs with hv
    · calc pot k (c true) (L ++ [.cert xs]) ≤ min 1 (k.μ (L ++ [.cert xs])) + nq * ε :=
            pot_le k (c true) nq nc (L ++ [.cert xs]) (h true) (by simp; omega)
        _ ≤ min 1 (k.μ L) + nq * ε := by gcongr; exact k.cert L xs (by omega) hv
    · exact pot_le k _ nq nc L (h false) (by omega)

/-- **Failure is below the stopped potential**, when failure at a well-formed leaf within
`logCap` forces the potential to `1`. Every log the game reaches from a well-formed one is well
formed. -/
theorem prob_le_pot (k : KStateA V E ε) (B : α → ALog → Prop)
    (hB : ∀ x L, B x L → WF L → L.length ≤ logCap → 1 ≤ k.μ L) :
    ∀ (p : Game α) (nq nc : ℕ) (L : ALog), WF L → DepthLE p nq nc →
      L.length + nq + nc ≤ logCap → prob B p L ≤ pot k p L
  | .ret x, _, _, L, hW, _, hlen => by
    classical
    simp only [prob, pot]
    split_ifs with hb
    · exact le_min le_rfl (hB x L hb hW (by omega))
    · exact bot_le
  | .query _ _, 0, _, _, _, h, _ => h.elim
  | .query q c, nq + 1, nc, L, hW, h, hlen => by
    simp only [prob, pot]
    split_ifs with h1
    · split
      · exact prob_le_one B _ _
      · exact avg_le fun a => prob_le_one B _ _
    · split
      · exact prob_le_pot k B hB _ nq nc L hW (h _) (by omega)
      · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
          prob_le_pot k B hB _ nq nc _ (hW.snoc_ans q a) (h a) (by simp; omega)) bot_le
  | .attest h c, nq, nc, L, hW, hd, hlen => by
    simp only [prob, pot]; exact prob_le_pot k B hB _ nq nc L hW (hd _) hlen
  | .certify _ _, _, 0, _, _, h, _ => h.elim
  | .certify xs c, nq, nc + 1, L, hW, h, hlen => by
    classical
    simp only [prob, pot]
    split_ifs with hv
    · exact prob_le_pot k B hB _ nq nc _ (hW.snoc_cert hv) (h true) (by simp; omega)
    · exact prob_le_pot k B hB _ nq nc L hW (h false) (by omega)

/-- **The paper theorem for any event below potential `1`**: an event that never holds on a
well-formed log within `logCap` of potential below `1` has probability at most `nq · ε` in a game
of at most `nq` queries and `nc` certifications, `nq + nc ≤ logCap`. -/
theorem paper_of (k : KStateA V E ε) (B : Digest × Proof → ALog → Prop)
    (hB : ∀ x L, B x L → WF L → L.length ≤ logCap → k.μ L < 1 → False)
    (G : Game (Digest × Proof)) (nq nc : ℕ) (hG : DepthLE G nq nc) (hn : nq + nc ≤ logCap) :
    prob B G [] ≤ nq * ε :=
  calc prob B G [] ≤ pot k G [] :=
        prob_le_pot k B (fun x L h hW hl => not_lt.mp (hB x L h hW hl)) G nq nc [] WF.nil hG
          (by simpa using hn)
    _ ≤ min 1 (k.μ []) + nq * ε := pot_le k G nq nc [] hG (by simpa using hn)
    _ = nq * ε := by simp [k.empty]

/-- **The attested paper theorem**: the probability that the verifier accepts on the final log
and the extractor returns no sound output is at most `nq · ε`; certifications cost nothing. -/
theorem paper (k : KStateA V E ε) (G : Game (Digest × Proof)) (nq nc : ℕ)
    (hG : DepthLE G nq nc) (hn : nq + nc ≤ logCap) :
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧
      ¬ ∃ o, E x.1 x.2 L = some o ∧ Sound V L x.1 o) G [] ≤ nq * ε :=
  paper_of k _ (fun x L h hW hl hμ => h.2 (k.final L x.1 x.2 hW hl hμ h.1)) G nq nc hG hn

/-- **The whole-tree attested paper theorem**: the probability that the root is accepted while
its tree is neither extracted to every depth nor ends in a returned list-hash collision is at
most `nq · ε`. -/
theorem paper_tree (k : KStateA V E ε) (G : Game (Digest × Proof)) (nq nc : ℕ)
    (hG : DepthLE G nq nc) (hn : nq + nc ≤ logCap) :
    prob (fun x L => (V x.1 x.2).runLog L = some true ∧
      ¬ ((∀ d, TreeOKA E L d x.1 x.2) ∨
        ∃ d a b, collAt E L d x.1 x.2 = some (a, b) ∧ IsColl a b)) G [] ≤ nq * ε :=
  paper_of k _ (fun _ _ h hW hl hμ => h.2 (compose_all k hW hl hμ h.1)) G nq nc hG hn

end RecursionFast.Explore.Attested.Paper

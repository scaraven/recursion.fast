/-
  RecursionFast.Explore.SeamsT1  (UNTRUSTED; audit probe for docs/audit/recursive-ks/seams-T1.md)

  * `outputs_escape_le`: the union bound over **every checked output** of a run (the stream's `M`
    outputs and its re-timed ones), each with its own root and its own finite set of paths:
    `Σ |Pᵢ| · (Q + qV) · ε`, from `KS.union` exactly as `escape_prob_le` does for one root.
  * `tape_out_of_domain`: a log of at least `2^62` entries puts the extractor's tape above
    `2^64` words, outside `Computes`'s domain (each entry takes at least 5 words).
  * The error arithmetic at the audit's target (`Q = 2^64`, `qV ≤ 2^16`, `ε = 2^-120`).
-/
import RecursionFast.Library.Compose

open scoped NNReal

namespace RecursionFast.SeamsT1
open RecursionFast RecursionFast.Compose

variable {S : Submission} {vk : Digest} {ε : ℝ≥0} {qV : ℕ}

/-- **The union bound over several roots**: `A` outputs `x`; root `i` is `root x i` (statement,
signed proof); `I` lists pairs (root index, path). The probability that some listed member of
some root's extraction tree escapes on `A`'s final log is at most `|I| · (Q + qV) · ε`. -/
theorem outputs_escape_le (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) {α : Type}
    (A : OProg α) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap)
    (root : α → ℕ → Digest × Signed) (I : Finset (ℕ × List Bool)) :
    prob (fun x L => ∃ ib ∈ I, ∃ c q, InTree S L (root x ib.1).1 (root x ib.1).2 ib.2 c q ∧
      Escape S vk L c q) A [] ≤ I.card * ((Q + qV) * ε) := by
  refine (prob_mono_of_inv Log.Functional (fun _ _ _ => functional_append)
    (B' := fun x L => ∃ ib ∈ I, Wins (Rel (S.acc vk)) (S.V vk) S.E
      (memberAt S (root x ib.1).1 ib.2 (root x ib.1).2 L) L)
    (fun x L hL ⟨ib, hib, c, q, hmem, he⟩ => ⟨ib, hib, ?_⟩) A
    (fun _ h => absurd h List.not_mem_nil)).trans
    (hks.union A hA hQ I fun ib x L => memberAt S (root x ib.1).1 ib.2 (root x ib.1).2 L)
  simp only [memberAt, hmem.follow_eq]
  exact he.wins hL

/-- Each log entry takes at least 5 tape words (length word, packed query, 4-word answer). -/
theorem logWords_length_ge (L : Log) : 5 * L.length ≤ (logWords L).length := by
  have h : ∀ L : Log, 5 * L.length ≤
      (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).length := by
    intro L
    induction L with
    | nil => simp
    | cons e L ih =>
      have h4 : (packBytes e.2.toList).length = 4 := by simp [packBytes]
      rw [List.flatMap_cons, List.length_append, List.length_append, h4, List.length_cons]
      have : 1 ≤ (bytesWords e.1.data.toList).length := by simp [bytesWords]
      omega
  exact (h L).trans (by simp [logWords])

/-- **A log of `2^62` entries is outside `Computes`'s domain**: its tape exceeds `2^64` words. -/
theorem tape_out_of_domain (c : Digest) (π : Proof) (L : Log) (h : 2 ^ 62 ≤ L.length) :
    2 ^ 64 < (extractorInput c π L).length := by
  have := logWords_length_ge L
  simp only [extractorInput, List.length_append]
  omega

/-! ## Arithmetic at the target (`Q = 2^64`, `qV = 2^16`, `ε = 2^-120`) -/

/-- Final output, `N = 2M + 1 = 193`: below `2^-48`. -/
theorem final_output_err : (193 : ℚ) * (2 ^ 64 + 2 ^ 16) / 2 ^ 120 ≤ 1 / 2 ^ 48 := by norm_num

/-- Every output, `N = M² + 2M = 9,408`: below `2^-42.5`, so below `2^-42`. -/
theorem every_output_err : (9408 : ℚ) * (2 ^ 64 + 2 ^ 16) / 2 ^ 120 ≤ 1 / 2 ^ 42 := by norm_num

/-- Every output plus the at most `⌊0.1 · 96⌋ = 9` re-timed ones (≤ 193 members each):
`9,408 + 1,737 = 11,145` members, still below `2^-42`. -/
theorem every_output_retime_err : (11145 : ℚ) * (2 ^ 64 + 2 ^ 16) / 2 ^ 120 ≤ 1 / 2 ^ 42 := by
  norm_num

/-- Not below `2^-43`: the margin to the target `2^-40` is between `2^2` and `2^3`. -/
theorem every_output_err_tight : 1 / 2 ^ 43 < (9408 : ℚ) * 2 ^ 64 / 2 ^ 120 := by norm_num

/-- The member count at which the target `2^-40` is reached at `Q = 2^64`: `2^16 = 65,536`
members (so `M ≤ 254` for every output, `M ≤ 2^15` for the final one). -/
theorem members_at_target : (65536 : ℚ) * 2 ^ 64 / 2 ^ 120 = 1 / 2 ^ 40 := by norm_num

/-- `2^64` maximal (`2^20`-byte) queries is `2^84` bytes; `2^47` of them already exceed a
`2^64`-word tape (each takes `1 + 2^17 + 4` words). -/
theorem max_queries_out_of_domain : 2 ^ 64 < 2 ^ 47 * (1 + 2 ^ 17 + 4) := by norm_num

end RecursionFast.SeamsT1

import RecursionFast.Contract
import RecursionFast.Library.RbrSound
/-! S9 (definitions lens), seam (a): admissibility sits inside `relK`, and `Secure`'s RBR knowledge
soundness quantifies over every statement `(L, x)`, admissible or not. So `Secure` obliges the
verifier to reject (up to the per-round errors) every layout that is not admissible at class `k`,
through `VK L`/`IDX L` alone: it is not "knowledge soundness for admissible layouts" but
"knowledge soundness for the language {(L, x) | L admissible ∧ ∃ w, rel}". Kernel-checked here for
the case without challenge rounds (no error to spend): such a secure protocol accepts no transcript
of a non-admissible layout. -/
open RecursionFast

theorem nonadmissible_rejected {k : ℕ} (P : Protocol k) (hP : P.Secure)
    (hmsg : ∀ j, (P.shape j).isMsg = true) (L : Layout K) (hL : ¬ L.Admissible k) (x : Stmt)
    (tr : FullTranscript P.shape) : P.specVerifier (L, x) tr = none := by
  obtain ⟨kSF, -⟩ := hP.sound
  cases h : P.specVerifier (L, x) tr with
  | none => rfl
  | some u =>
    have hx := chain_extracts kSF (L, x) tr u () h (Set.mem_univ _)
      (fun c => absurd (hmsg c.1) (by simp [c.2]))
    exact absurd hx.1 hL

/-! Non-vacuity of the obligation: a layout can be satisfiable and still not admissible (e.g. one
chip with a zero-coefficient gadget whose matrix has `2^(k+4) + 1` entries: `rel` holds for any
statement whose public row carries it, `Admissible` fails; `Controls/Layout.lean`, `entries_neg`,
is the cap's boundary control at class 0). For such a layout a secure protocol must still reject,
so its key `VK L` (or the index oracle) has to carry enough to decide admissibility. -/

#print axioms nonadmissible_rejected

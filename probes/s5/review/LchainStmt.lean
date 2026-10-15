/-
S5 review probe (tag binding is benchmark-level): the statement of the benchmark layout `Lchain`
(L_chain(16), `Controls/ChainData.lean`) has `x₄ = 16` and `x₅ … x₃₁ = 0`, by its public chip
alone. A node statement has `d1 = D(vkL)` in `x₄ … x₇` and `d2 = H(x₁ ‖ x₂)` in `x₈ … x₁₁`, so it
is an `Lchain` statement only if 24 bytes of `D(vkL)` and all 32 bytes of `d2` are zero. This is
what keeps a node statement from being proved as a leaf child under `vkL` (tags are not bound by
the contract).
-/
import RecursionFast.Controls.ChainData
import RecursionFast.Library.Field

namespace RecursionFast.Probes.S5Review
open RecursionFast RecursionFast.Controls.Chain

theorem pub_holds (k : ℕ) (x : Fin 32 → K) (w : List (Table K)) (h : Lchain.rel k x w) :
    ∃ T, Lchain_chip0.gadget.holds (view Lchain_chip0 T 0) ∧ ∀ i : Fin 32, T.cell 0 i = x i := by
  obtain ⟨hlen, -, hg, -, ⟨T, hT, hrows, hx⟩, -⟩ := h
  refine ⟨T, hg (Lchain_chip0, T) ?_ 0 hrows, hx⟩
  have h0 : w[0]? = some T := by simpa [Lchain] using hT
  cases w with
  | nil => simp at h0
  | cons T' w' => simp at h0; subst h0; simp [Lchain]

theorem row_eq (T : Table K) (hg : Lchain_chip0.gadget.holds (view Lchain_chip0 T 0))
    (r : ℕ) (hr : r < 33) :
    (List.ofFn fun i : Fin 1 => Lchain_chip0.gadget.c i * ((Lchain_chip0.gadget.S i).map
      fun j => rowDot (Lchain_chip0.gadget.M j) (view Lchain_chip0 T 0) ⟨r, hr⟩).prod).sum = 0 :=
  hg ⟨r, hr⟩

theorem kx1 : kx 1 = (1 : K) := rfl

theorem Lchain_stmt (k : ℕ) (x : Fin 32 → K) (w : List (Table K)) (h : Lchain.rel k x w) :
    x 4 = kx 16 ∧ ∀ i : Fin 32, 5 ≤ i.val → x i = 0 := by
  obtain ⟨T, hg, hx⟩ := pub_holds k x w h
  refine ⟨?_, fun i hi => ?_⟩
  · have := row_eq T hg 5 (by decide)
    simp [Lchain_chip0, rowDot, view, List.filter, kx1] at this
    rw [← hx 4]; exact eq_of_sub_eq_zero this
  · have H : ∀ r : Fin 33, 6 ≤ r.val → T.cell 0 (r.val - 1) = 0 := by
      intro r hr
      have := row_eq T hg r.val r.isLt
      clear hx hg h
      fin_cases r <;> simp at hr <;> simpa [Lchain_chip0, rowDot, view, List.filter, kx1] using this
    rw [← hx i, show i.val = (i.val + 1) - 1 by omega]
    exact H ⟨i.val + 1, by omega⟩ (by simp; omega)

/-- So a statement whose `d1` limbs 1–3 or whose `d2` are not all zero is no `Lchain`
statement: in particular no node statement unless 56 bytes of two hash outputs are zero. -/
theorem node_not_Lchain (k : ℕ) (x : Fin 32 → K) (w : List (Table K))
    (h : ∃ i : Fin 32, 5 ≤ i.val ∧ i.val < 12 ∧ x i ≠ 0) : ¬ Lchain.rel k x w :=
  fun hr => let ⟨i, h5, _, hne⟩ := h; hne ((Lchain_stmt k x w hr).2 i h5)

end RecursionFast.Probes.S5Review

#print axioms RecursionFast.Probes.S5Review.Lchain_stmt

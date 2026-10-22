/-
  RecursionFast.Library.Tree  (UNTRUSTED, kernel-checked; unchanged from v3)

  Facts about the tree root (`Contract/Tree.lean`) that justify its docstring.

  * `length_treeLevel`: a level has `⌈n / 2⌉` digests.
  * `length_iterate_length_le_one`: `|cs|` levels leave at most one digest, and
    `iterate_treeLevel_of_length_le_one`: further levels change nothing.
  * `treeRoot_cons_cons`: **until one remains**: the root of two or more digests is the root of
    the level above; with `treeRoot [c] = c` (by `rfl`) this is the recursive reading of
    `treeRoot`.
-/
import RecursionFast.Contract.Tree

namespace RecursionFast

theorem length_treeLevel : ∀ cs : List Digest, (treeLevel cs).length = (cs.length + 1) / 2
  | [] => rfl
  | [_] => by simp [treeLevel]
  | _ :: _ :: cs => by simp [treeLevel, length_treeLevel cs]; omega

theorem treeLevel_of_length_le_one {cs : List Digest} (h : cs.length ≤ 1) : treeLevel cs = cs := by
  match cs, h with
  | [], _ => rfl
  | [_], _ => rfl

theorem iterate_treeLevel_of_length_le_one {l : List Digest} (h : l.length ≤ 1) (m : ℕ) :
    treeLevel^[m] l = l := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, treeLevel_of_length_le_one h, ih]

theorem length_iterate_treeLevel (cs : List Digest) (k : ℕ) :
    (treeLevel^[k] cs).length ≤ max 1 (cs.length - k) := by
  induction k with
  | zero => simp; omega
  | succ k ih => rw [Function.iterate_succ_apply', length_treeLevel]; omega

/-- `|cs|` levels leave at most one digest. -/
theorem length_iterate_length_le_one (cs : List Digest) :
    (treeLevel^[cs.length] cs).length ≤ 1 := by
  have := length_iterate_treeLevel cs cs.length; omega

/-- **Until one remains**: the root of two or more digests is the root of the level above. -/
theorem treeRoot_cons_cons (a b : Digest) (cs : List Digest) :
    treeRoot (a :: b :: cs) = treeRoot (treeLevel (a :: b :: cs)) := by
  have hl := length_treeLevel (a :: b :: cs)
  simp only [List.length_cons] at hl
  obtain ⟨m, hm⟩ : ∃ m, (a :: b :: cs).length = m + (treeLevel (a :: b :: cs)).length + 1 :=
    ⟨cs.length + 1 - (cs.length + 3) / 2, by simp only [List.length_cons, hl]; omega⟩
  unfold treeRoot
  rw [hm, Function.iterate_succ_apply, Function.iterate_add_apply,
    iterate_treeLevel_of_length_le_one (length_iterate_length_le_one _)]

end RecursionFast

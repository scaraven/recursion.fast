/-
  RecursionFast.Library.Tree  (UNTRUSTED, kernel-checked)

  Facts about the contract's two trees, the tree root (`Contract/Tree.lean`, `treeLevel`,
  `treeRoot`) and a leaf's data tree (`Contract/Relation.lean`, `dataLevel`, `dataRoot`), that
  justify their docstrings. The contract keeps two copies of one shape (`Tree.lean` imports
  `Relation.lean`, and `Rel` needs `dataRoot`); the lemmas are proved once, for the generic level
  `level f` of a tree whose nodes are hashed by `f`, and both copies are instances of it
  (`treeLevel_eq`, `dataLevel_eq`, `treeRoot_eq`, `dataRoot_eq`).

  * `length_level`: a level has `⌈n / 2⌉` digests; `length_iterate_level_eq`: the lengths after
    `k` levels depend only on the length before (one shape for every list of one length).
  * `length_iterate_length_le_one'`: `|cs|` levels leave at most one digest, and
    `iterate_level_of_length_le_one`: further levels change nothing (one digest is a fixed point).
  * `root_of_iterate`, `root_eq_iterate`: a digest that some number of levels reaches alone is the
    root, and any number of levels from `|cs|` on gives it; `root_cons_cons`: **until one
    remains**: the root of two or more digests is the root of the level above; with
    `root f [c] = c` (by `rfl`) this is the recursive reading of the root.
  * The same facts for `treeLevel`/`treeRoot` under their earlier names (`length_treeLevel`,
    `iterate_treeLevel_of_length_le_one`, `length_iterate_length_le_one`, `treeRoot_cons_cons`),
    and `length_dataLevel`, `dataRoot_nil`, `dataRoot_singleton`, `dataRoot_cons_cons` for the
    data tree.
-/
import RecursionFast.Contract.Tree

namespace RecursionFast

/-! ## The generic level -/

/-- One level up a tree whose nodes are hashed by `f`: adjacent digests paired by `f`; an odd last
digest is carried up. -/
def level (f : Digest → Digest → Digest) : List Digest → List Digest
  | a :: b :: t => f a b :: level f t
  | t => t

/-- The root of the tree over `cs` whose nodes are hashed by `f`: `level f`, `|cs|` times, then
the first digest; the zero digest if `cs = []`. -/
def root (f : Digest → Digest → Digest) (cs : List Digest) : Digest :=
  ((level f)^[cs.length] cs).headD (Vector.replicate 32 0)

theorem level_cons_cons (f : Digest → Digest → Digest) (a b : Digest) (t : List Digest) :
    level f (a :: b :: t) = f a b :: level f t := rfl

theorem length_level (f : Digest → Digest → Digest) :
    ∀ cs : List Digest, (level f cs).length = (cs.length + 1) / 2
  | [] => rfl
  | [_] => by simp [level]
  | _ :: _ :: cs => by simp [level, length_level f cs]; omega

theorem level_of_length_le_one (f : Digest → Digest → Digest) {cs : List Digest}
    (h : cs.length ≤ 1) : level f cs = cs := by
  match cs, h with
  | [], _ => rfl
  | [_], _ => rfl

theorem iterate_level_of_length_le_one (f : Digest → Digest → Digest) {l : List Digest}
    (h : l.length ≤ 1) (m : ℕ) : (level f)^[m] l = l := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, level_of_length_le_one f h, ih]

theorem length_iterate_level (f : Digest → Digest → Digest) (cs : List Digest) (k : ℕ) :
    ((level f)^[k] cs).length ≤ max 1 (cs.length - k) := by
  induction k with
  | zero => simp; omega
  | succ k ih => rw [Function.iterate_succ_apply', length_level]; omega

/-- The length after `k` levels depends only on the length before. -/
theorem length_iterate_level_eq (f g : Digest → Digest → Digest) {cs ds : List Digest}
    (h : cs.length = ds.length) (k : ℕ) :
    ((level f)^[k] cs).length = ((level g)^[k] ds).length := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', length_level, length_level, ih]

/-- `|cs|` levels leave at most one digest. -/
theorem length_iterate_length_le_one' (f : Digest → Digest → Digest) (cs : List Digest) :
    ((level f)^[cs.length] cs).length ≤ 1 :=
  Nat.le_trans (length_iterate_level f cs cs.length) (by simp)

/-- A digest that some number of levels reaches alone is the root. -/
theorem root_of_iterate (f : Digest → Digest → Digest) {cs : List Digest} {x : Digest} (k : ℕ)
    (h : (level f)^[k] cs = [x]) : root f cs = x := by
  -- `k` more levels change nothing after `|cs|`, and `|cs|` more change nothing after `k`.
  rw [root, ← iterate_level_of_length_le_one f (length_iterate_length_le_one' f cs) k,
    ← Function.iterate_add_apply, Nat.add_comm k, Function.iterate_add_apply, h,
    iterate_level_of_length_le_one f (by simp), List.headD_cons]

/-- Any number of levels from `|cs|` on gives the root. -/
theorem root_eq_iterate (f : Digest → Digest → Digest) (cs : List Digest) {k : ℕ}
    (hk : cs.length ≤ k) : root f cs = ((level f)^[k] cs).headD (Vector.replicate 32 0) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [root, Nat.add_comm, Function.iterate_add_apply,
    iterate_level_of_length_le_one f (length_iterate_length_le_one' f cs)]

/-- **Until one remains**: the root of two or more digests is the root of the level above. -/
theorem root_cons_cons (f : Digest → Digest → Digest) (a b : Digest) (cs : List Digest) :
    root f (a :: b :: cs) = root f (level f (a :: b :: cs)) := by
  have hl := length_level f (a :: b :: cs)
  simp only [List.length_cons] at hl
  rw [root, List.length_cons, Function.iterate_succ_apply,
    ← root_eq_iterate f _ (by simp only [hl, List.length_cons]; omega)]

/-! ## The two instances -/

theorem treeLevel_eq : ∀ cs, treeLevel cs = level nodeStmt cs
  | a :: b :: cs => by rw [treeLevel, level_cons_cons, treeLevel_eq cs]
  | [] => rfl
  | [_] => rfl

theorem dataLevel_eq : ∀ cs, dataLevel cs = level dataNode cs
  | a :: b :: cs => by rw [dataLevel, level_cons_cons, dataLevel_eq cs]
  | [] => rfl
  | [_] => rfl

theorem treeRoot_eq (cs : List Digest) : treeRoot cs = root nodeStmt cs := by
  rw [treeRoot, root, show treeLevel = level nodeStmt from funext treeLevel_eq]

/-- The data root is the generic root of the block hashes. -/
theorem dataRoot_eq (xs : List Digest) : dataRoot xs = root dataNode (xs.map leafItem) := by
  rw [dataRoot, root, List.length_map, show dataLevel = level dataNode from funext dataLevel_eq]

/-! ## The tree root (`Contract/Tree.lean`) -/

theorem length_treeLevel (cs : List Digest) : (treeLevel cs).length = (cs.length + 1) / 2 := by
  rw [treeLevel_eq, length_level]

theorem treeLevel_of_length_le_one {cs : List Digest} (h : cs.length ≤ 1) :
    treeLevel cs = cs := by
  rw [treeLevel_eq, level_of_length_le_one _ h]

theorem iterate_treeLevel_of_length_le_one {l : List Digest} (h : l.length ≤ 1) (m : ℕ) :
    treeLevel^[m] l = l := by
  rw [show treeLevel = level nodeStmt from funext treeLevel_eq,
    iterate_level_of_length_le_one _ h]

/-- `|cs|` levels leave at most one digest. -/
theorem length_iterate_length_le_one (cs : List Digest) :
    (treeLevel^[cs.length] cs).length ≤ 1 := by
  rw [show treeLevel = level nodeStmt from funext treeLevel_eq]
  exact length_iterate_length_le_one' _ cs

/-- **Until one remains**: the root of two or more digests is the root of the level above. -/
theorem treeRoot_cons_cons (a b : Digest) (cs : List Digest) :
    treeRoot (a :: b :: cs) = treeRoot (treeLevel (a :: b :: cs)) := by
  rw [treeRoot_eq, treeRoot_eq, treeLevel_eq, root_cons_cons]

/-! ## The data tree (`Contract/Relation.lean`) -/

theorem length_dataLevel (cs : List Digest) : (dataLevel cs).length = (cs.length + 1) / 2 := by
  rw [dataLevel_eq, length_level]

/-- No block: the zero digest. -/
theorem dataRoot_nil : dataRoot [] = Vector.replicate 32 0 := rfl

/-- One block: its hash. -/
theorem dataRoot_singleton (x : Digest) : dataRoot [x] = leafItem x := rfl

/-- **Until one remains**, for the data tree: the root of two or more blocks is the generic root of
the level above their hashes. -/
theorem dataRoot_cons_cons (a b : Digest) (xs : List Digest) :
    dataRoot (a :: b :: xs) = root dataNode (dataLevel ((a :: b :: xs).map leafItem)) := by
  rw [dataRoot_eq, List.map_cons, List.map_cons, root_cons_cons, dataLevel_eq]

end RecursionFast

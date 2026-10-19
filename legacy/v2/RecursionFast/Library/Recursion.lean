/-
  RecursionFast.Library.Recursion  (UNTRUSTED, kernel-checked)

  Facts about the recursion statement format and `aggOK` (`Contract/Recursion.lean`, DESIGN §5),
  for every protocol and configuration.

  Load-bearing:
  * `aggOK_iff`: what `aggOK` accepts, as a `Prop` in the §5.1 vocabulary: slot `d0` is the
    recursion key's digest, `d1` the leaf key's, `d2` the hash of the children's statements,
    `d3` the children's tags (`tagSlot`), `d4 … d7` are zero, both keys have a 32-byte root, and
    each child is accepted (`child_iff`: a node child carries the parent's `d0`, `d1` and verifies
    under `vkC`; a leaf child verifies under `vkL`). The form a recursion circuit `C_V` must force
    (§5.3).
  * Satisfiability (S1-A12(c)) and `RecursionEntry.live` (S5-A10): `aggOK_sat_of_complete` (from
    `narg_complete`: honest compiled proofs that the IOP verifier accepts on the Fiat–Shamir
    transcript give a node that `aggOK` accepts, at the aggregate statement, with the indexer's
    keys), `aggOK_sat_of_secure` (the same for a secure protocol on instances of `relK k`,
    whenever the honest tapes fit the cap), and `live_of_secure` (the field itself, from one
    instance). `aggOK_leaves` and `aggOK_nodes` are the two-leaf and two-node forms
    (`aggOK_nodeStmt_iff`: at its aggregate statement a node is accepted iff its roots and
    children are).
  * The statement tree and the root check: `rootOK_iff` (the recomputed tree), `treeRoot_one`,
    `treeRoot_two` (depths 1 and 2 unfolded), `treeRoot_node` (a root of depth `≥ 1` is an
    aggregate statement with the tree's keys), and `keys_of_root` (at a root that passes `rootOK`
    and `aggOK`, the node's keys have the digests of the indexer's keys for `C` and `L`).
  * The aggregate statement: `nodeStmt_slot`, `eq_nodeStmt_iff` (its slots are the two key
    digests, the children's hash, the tags and zeros), `tagSlot_inj` (the tag slot determines the
    tags).
  * Digest slots: `digestToSlot_bytes` and `bytes_digestToSlot` (the round trips with
    `K.bytes = K.toBytes` as `UInt8`s; `K.bytes_ofBytes`: every 8-byte string encodes an element),
    hence `digestToSlot_inj` on 32-byte digests: a slot determines the digest, so `aggOK`'s
    comparisons of slots are comparisons of digests.
  * Slots of a statement: `Stmt.slot_ofSlots`, `Stmt.ofSlots_slot`, `Stmt.ext_slot`,
    `Stmt.eq_ofSlots_iff`.
-/
import RecursionFast.Contract.Recursion
import RecursionFast.Library.Compile

namespace RecursionFast

/-! ## Slots of a statement -/

/-- The slots of `ofSlots s` are `s`. -/
theorem Stmt.slot_ofSlots (s : Fin 8 → Fin 4 → K) (i : Fin 8) : (Stmt.ofSlots s).slot i = s i := by
  funext j
  simp only [Stmt.slot, Stmt.ofSlots]
  congr 2 <;> omega

/-- A statement is the statement of its slots. -/
theorem Stmt.ofSlots_slot (x : Stmt) : Stmt.ofSlots x.slot = x :=
  funext fun i => congrArg x (Fin.ext (Nat.div_add_mod i 4))

/-- Two statements with the same slots are equal. -/
theorem Stmt.ext_slot {x y : Stmt} (h : ∀ i, x.slot i = y.slot i) : x = y := by
  rw [← Stmt.ofSlots_slot x, ← Stmt.ofSlots_slot y, funext h]

/-- A statement is `ofSlots s` iff its slots are `s`. -/
theorem Stmt.eq_ofSlots_iff (x : Stmt) (s : Fin 8 → Fin 4 → K) :
    x = Stmt.ofSlots s ↔ ∀ i, x.slot i = s i :=
  ⟨fun h i => h ▸ Stmt.slot_ofSlots s i, fun h => by rw [← funext h, Stmt.ofSlots_slot]⟩

/-! ## Digests as slots -/

/-- `K.ofBytes` inverts `K.bytes` on 8-byte strings (every 8-byte string encodes an element). -/
theorem K.bytes_ofBytes (b : List UInt8) (hb : b.length = 8) : (K.ofBytes b).bytes = b := by
  match b, hb with
  | [c0, c1, c2, c3, c4, c5, c6, c7], _ =>
    simp only [K.bytes_eq, K.ofBytes, wordOfBytes, List.take_succ_cons, List.take_zero,
      List.foldr_cons, List.foldr_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply UInt8.toBitVec_inj.mp
      ext i hi
      simp only [BitVec.getElem_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
      interval_cases i <;> simp [BitVec.getLsbD_of_ge]

/-- `K.ofBytes` inverts `K.bytes`. -/
theorem K.ofBytes_bytes' (a : K) : K.ofBytes a.bytes = a :=
  List.append_nil a.bytes ▸ K.ofBytes_bytes a []

/-- **Round trip, slot first**: the slot of the bytes of four elements is those elements. -/
theorem digestToSlot_bytes (s : Fin 4 → K) : digestToSlot ((List.ofFn s).flatMap K.bytes) = s := by
  funext j
  fin_cases j <;> simp [digestToSlot, List.ofFn_succ, List.drop_append, List.drop_eq_nil_of_le,
    K.bytes_length, K.ofBytes_bytes, K.ofBytes_bytes']

/-- `K.ofBytes` reads only the first 8 bytes. -/
theorem K.ofBytes_cons8 (c0 c1 c2 c3 c4 c5 c6 c7 : UInt8) (r : List UInt8) :
    K.ofBytes (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: r) =
      K.ofBytes [c0, c1, c2, c3, c4, c5, c6, c7] := rfl

/-- **Round trip, digest first**: the bytes of the slot of a 32-byte digest are the digest. -/
theorem bytes_digestToSlot (d : Digest) (hd : d.length = 32) :
    (List.ofFn (digestToSlot d)).flatMap K.bytes = d := by
  match d, hd with
  | [a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7,
     c0, c1, c2, c3, c4, c5, c6, c7, e0, e1, e2, e3, e4, e5, e6, e7], _ =>
    simp [digestToSlot, List.ofFn_succ, K.ofBytes_cons8, K.bytes_ofBytes]

/-- A slot determines a 32-byte digest. -/
theorem digestToSlot_inj {d e : Digest} (hd : d.length = 32) (he : e.length = 32) :
    digestToSlot d = digestToSlot e ↔ d = e :=
  ⟨fun h => by rw [← bytes_digestToSlot d hd, ← bytes_digestToSlot e he, h], fun h => h ▸ rfl⟩

/-! ## The aggregate statement -/

section Nodes
variable (cfg : Cfg)

/-- The slots of the aggregate statement: the two key digests, the children's hash, the tags,
zeros. -/
theorem nodeStmt_slot {vkLen : ℕ} (vkC vkL : VKc vkLen) (t₁ t₂ : Tag) (x₁ x₂ : Stmt) :
    (nodeStmt cfg vkC vkL t₁ t₂ x₁ x₂).slot 0 = digestToSlot (vkC.digest cfg) ∧
    (nodeStmt cfg vkC vkL t₁ t₂ x₁ x₂).slot 1 = digestToSlot (vkL.digest cfg) ∧
    (nodeStmt cfg vkC vkL t₁ t₂ x₁ x₂).slot 2 =
      digestToSlot (cfg.hash.run (stmtBytes x₁ ++ stmtBytes x₂)) ∧
    (nodeStmt cfg vkC vkL t₁ t₂ x₁ x₂).slot 3 = tagSlot t₁ t₂ ∧
    ∀ i : Fin 8, 4 ≤ i.val → (nodeStmt cfg vkC vkL t₁ t₂ x₁ x₂).slot i = 0 :=
  ⟨Stmt.slot_ofSlots _ 0, Stmt.slot_ofSlots _ 1, Stmt.slot_ofSlots _ 2, Stmt.slot_ofSlots _ 3,
    fun | ⟨_ + 4, _⟩, _ => Stmt.slot_ofSlots _ _⟩

/-- A statement is the aggregate statement iff its slots are the two key digests, the
children's hash, the tags and zeros. -/
theorem eq_nodeStmt_iff {vkLen : ℕ} (vkC vkL : VKc vkLen) (t₁ t₂ : Tag) (x₁ x₂ x' : Stmt) :
    x' = nodeStmt cfg vkC vkL t₁ t₂ x₁ x₂ ↔
      x'.slot 0 = digestToSlot (vkC.digest cfg) ∧ x'.slot 1 = digestToSlot (vkL.digest cfg) ∧
      x'.slot 2 = digestToSlot (cfg.hash.run (stmtBytes x₁ ++ stmtBytes x₂)) ∧
      x'.slot 3 = tagSlot t₁ t₂ ∧ ∀ i : Fin 8, 4 ≤ i.val → x'.slot i = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := nodeStmt_slot cfg vkC vkL t₁ t₂ x₁ x₂
  exact ⟨fun h => h ▸ ⟨h0, h1, h2, h3, h4⟩, fun ⟨e0, e1, e2, e3, e4⟩ => Stmt.ext_slot fun
    | ⟨0, _⟩ => e0.trans h0.symm | ⟨1, _⟩ => e1.trans h1.symm | ⟨2, _⟩ => e2.trans h2.symm
    | ⟨3, _⟩ => e3.trans h3.symm
    | ⟨_ + 4, _⟩ => (e4 _ (Nat.le_add_left _ _)).trans (h4 _ (Nat.le_add_left _ _)).symm⟩

/-- The tag slot determines the tags. -/
theorem tagSlot_inj {t₁ t₂ u₁ u₂ : Tag} : tagSlot t₁ t₂ = tagSlot u₁ u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩
  have h0 := congrFun h 0; have h1 := congrFun h 1
  cases t₁ <;> cases t₂ <;> cases u₁ <;> cases u₂ <;> revert h0 h1 <;> decide

/-! ## What `aggOK` accepts -/

variable {k : ℕ} (P : Protocol k)

/-- **A child is accepted**: a node child carries the parent's `d0`, `d1` and verifies under
`vkC`; a leaf child verifies under `vkL`. -/
theorem child_iff (vkC vkL : VKc P.vkLen) (x' : Stmt) (t : Tag) (x : Stmt) (π : Tape) :
    child cfg P vkC vkL x' t x π = true ↔
      (t = .node → x.slot 0 = x'.slot 0 ∧ x.slot 1 = x'.slot 1 ∧ NARG cfg P vkC x π = true) ∧
      (t = .leaf → NARG cfg P vkL x π = true) := by
  cases t <;> simp [child, and_assoc]

/-- **What `aggOK` accepts**, in the vocabulary of DESIGN §5.1: `d0`/`d1` are the digests of
the recursion and leaf keys, `d2` is the hash of the children's statements, `d3` holds the
children's tags, `d4 … d7` are zero, both keys have a 32-byte index root, and each child is
accepted under the key its tag names. -/
theorem aggOK_iff (x' : Stmt) (nw : NodeWitness P.vkLen) :
    aggOK cfg P x' nw = true ↔
      x'.slot 0 = digestToSlot (nw.vkC.digest cfg) ∧ x'.slot 1 = digestToSlot (nw.vkL.digest cfg) ∧
      x'.slot 2 = digestToSlot (cfg.hash.run (stmtBytes nw.x₁ ++ stmtBytes nw.x₂)) ∧
      x'.slot 3 = tagSlot nw.t₁ nw.t₂ ∧ (∀ i : Fin 8, 4 ≤ i.val → x'.slot i = 0) ∧
      nw.vkC.2.length = 32 ∧ nw.vkL.2.length = 32 ∧
      (nw.t₁ = .node → nw.x₁.slot 0 = x'.slot 0 ∧ nw.x₁.slot 1 = x'.slot 1 ∧
        NARG cfg P nw.vkC nw.x₁ nw.π₁ = true) ∧
      (nw.t₁ = .leaf → NARG cfg P nw.vkL nw.x₁ nw.π₁ = true) ∧
      (nw.t₂ = .node → nw.x₂.slot 0 = x'.slot 0 ∧ nw.x₂.slot 1 = x'.slot 1 ∧
        NARG cfg P nw.vkC nw.x₂ nw.π₂ = true) ∧
      (nw.t₂ = .leaf → NARG cfg P nw.vkL nw.x₂ nw.π₂ = true) := by
  simp only [aggOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, child_iff,
    eq_nodeStmt_iff, and_assoc]

/-- At its aggregate statement a node is accepted iff both keys have a 32-byte root and both
children are accepted. -/
theorem aggOK_nodeStmt_iff (nw : NodeWitness P.vkLen) :
    aggOK cfg P (nodeStmt cfg nw.vkC nw.vkL nw.t₁ nw.t₂ nw.x₁ nw.x₂) nw = true ↔
      nw.vkC.2.length = 32 ∧ nw.vkL.2.length = 32 ∧
      child cfg P nw.vkC nw.vkL (nodeStmt cfg nw.vkC nw.vkL nw.t₁ nw.t₂ nw.x₁ nw.x₂) nw.t₁ nw.x₁
        nw.π₁ = true ∧
      child cfg P nw.vkC nw.vkL (nodeStmt cfg nw.vkC nw.vkL nw.t₁ nw.t₂ nw.x₁ nw.x₂) nw.t₂ nw.x₂
        nw.π₂ = true := by
  simp [aggOK, and_assoc]

/-- **Two leaves**: proofs accepted under the leaf key, and a recursion key with a 32-byte root,
make a node that `aggOK` accepts at the aggregate statement. -/
theorem aggOK_leaves (vkC vkL : VKc P.vkLen) (hC : vkC.2.length = 32) (x₁ x₂ : Stmt)
    (π₁ π₂ : Tape) (h₁ : NARG cfg P vkL x₁ π₁ = true) (h₂ : NARG cfg P vkL x₂ π₂ = true) :
    aggOK cfg P (nodeStmt cfg vkC vkL .leaf .leaf x₁ x₂)
      ⟨vkC, vkL, .leaf, .leaf, x₁, x₂, π₁, π₂⟩ = true :=
  (aggOK_nodeStmt_iff cfg P ⟨vkC, vkL, .leaf, .leaf, x₁, x₂, π₁, π₂⟩).mpr
    ⟨hC, ((NARG_eq_true_iff cfg P vkL x₁ π₁).mp h₁).2.1, h₁, h₂⟩

/-- **Two nodes**: proofs, accepted under the recursion key, of two aggregate statements with
the same keys (any tags below) make a node that `aggOK` accepts at the aggregate statement. -/
theorem aggOK_nodes (vkC vkL : VKc P.vkLen) (hL : vkL.2.length = 32) (s₁ s₂ u₁ u₂ : Tag)
    (y₁ z₁ y₂ z₂ : Stmt) (π₁ π₂ : Tape)
    (h₁ : NARG cfg P vkC (nodeStmt cfg vkC vkL s₁ s₂ y₁ z₁) π₁ = true)
    (h₂ : NARG cfg P vkC (nodeStmt cfg vkC vkL u₁ u₂ y₂ z₂) π₂ = true) :
    aggOK cfg P (nodeStmt cfg vkC vkL .node .node (nodeStmt cfg vkC vkL s₁ s₂ y₁ z₁)
        (nodeStmt cfg vkC vkL u₁ u₂ y₂ z₂))
      ⟨vkC, vkL, .node, .node, nodeStmt cfg vkC vkL s₁ s₂ y₁ z₁, nodeStmt cfg vkC vkL u₁ u₂ y₂ z₂,
        π₁, π₂⟩ = true := by
  refine (aggOK_nodeStmt_iff cfg P ⟨vkC, vkL, .node, .node, nodeStmt cfg vkC vkL s₁ s₂ y₁ z₁,
    nodeStmt cfg vkC vkL u₁ u₂ y₂ z₂, π₁, π₂⟩).mpr
      ⟨((NARG_eq_true_iff cfg P vkC _ π₁).mp h₁).2.1, hL, ?_, ?_⟩ <;>
  simp only [child, Bool.and_eq_true, decide_eq_true_eq, nodeStmt_slot, h₁, h₂, and_self]

/-! ## Satisfiability (S1-A12(c)) and `live` (S5-A10) -/

/-- **Satisfiability of `aggOK` from compile completeness**: honest compiled proofs of two
statements of the leaf layout `L`, which the IOP verifier accepts on their Fiat–Shamir
transcripts, form with the indexer's keys for `C` and `L` a two-leaf node that `aggOK` accepts at
its aggregate statement. -/
theorem aggOK_sat_of_complete (C L : Layout K) (x₁ x₂ : Stmt) (w₁ w₂ : List (Table K))
    (π₁ π₂ : Tape) (hπ₁ : prove cfg P L x₁ w₁ = some π₁) (hπ₂ : prove cfg P L x₂ w₂ = some π₂)
    (h₁ : P.specVerifier (L, x₁) (fsTranscript cfg P L x₁ w₁) = some ())
    (h₂ : P.specVerifier (L, x₂) (fsTranscript cfg P L x₂ w₂) = some ()) :
    aggOK cfg P (nodeStmt cfg (index cfg P C) (index cfg P L) .leaf .leaf x₁ x₂)
      ⟨index cfg P C, index cfg P L, .leaf, .leaf, x₁, x₂, π₁, π₂⟩ = true :=
  aggOK_leaves cfg P _ _ (commit_length cfg _) x₁ x₂ π₁ π₂
    (narg_complete cfg P L x₁ w₁ π₁ hπ₁ h₁) (narg_complete cfg P L x₂ w₂ π₂ hπ₂ h₂)

/-- **Satisfiability of `aggOK` for a secure protocol**: on two instances of `relK k` for the leaf
layout `L`, the honest compiled proofs (when they fit the tape cap, `prove_isSome`) form with the
indexer's keys a two-leaf node that `aggOK` accepts at its aggregate statement. -/
theorem aggOK_sat_of_secure (hP : P.Secure) (C L : Layout K) (x₁ x₂ : Stmt)
    (w₁ w₂ : List (Table K)) (hw₁ : ((L, x₁), w₁) ∈ relK k) (hw₂ : ((L, x₂), w₂) ∈ relK k)
    (π₁ π₂ : Tape) (hπ₁ : prove cfg P L x₁ w₁ = some π₁) (hπ₂ : prove cfg P L x₂ w₂ = some π₂) :
    aggOK cfg P (nodeStmt cfg (index cfg P C) (index cfg P L) .leaf .leaf x₁ x₂)
      ⟨index cfg P C, index cfg P L, .leaf, .leaf, x₁, x₂, π₁, π₂⟩ = true :=
  aggOK_leaves cfg P _ _ (commit_length cfg _) x₁ x₂ π₁ π₂
    (narg_complete_of_secure cfg P L x₁ w₁ hP hw₁ π₁ hπ₁)
    (narg_complete_of_secure cfg P L x₂ w₂ hP hw₂ π₂ hπ₂)

/-- **`RecursionEntry.live` for a secure protocol**: one instance of `relK k` for some layout
`L` whose honest compiled proof fits the tape cap gives the field, for every `C`. -/
theorem live_of_secure (hP : P.Secure) (C L : Layout K) (x : Stmt) (w : List (Table K))
    (hw : ((L, x), w) ∈ relK k) (π : Tape) (hπ : prove cfg P L x w = some π) :
    ∃ L x' nw, nw.vkC = index cfg P C ∧ nw.vkL = index cfg P L ∧ aggOK cfg P x' nw = true :=
  ⟨L, _, _, rfl, rfl, aggOK_sat_of_secure cfg P hP C L x x w w hw hw π π hπ hπ⟩

/-! ## The statement tree and the root check -/

variable {vkLen : ℕ} (vkC vkL : VKc vkLen)

/-- Every statement one level of the tree outputs is an aggregate statement. -/
theorem mem_pairUp (t : Tag) : ∀ (xs ys : List Stmt), pairUp cfg vkC vkL t xs = some ys →
    ∀ y ∈ ys, ∃ a b, y = nodeStmt cfg vkC vkL t t a b
  | [], ys, h, y, hy => by simp [pairUp] at h; subst h; simp at hy
  | [_], _, h, _, _ => by simp [pairUp] at h
  | x₁ :: x₂ :: r, ys, h, y, hy => by
    simp only [pairUp, Option.map_eq_some_iff] at h
    obtain ⟨zs, hz, rfl⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x₁, x₂, rfl⟩
    · exact mem_pairUp t r zs hz y hy

/-- The root of a tree of depth `≥ 1` is an aggregate statement with the tree's keys. -/
theorem treeRoot_node (d : ℕ) (xs : List Stmt) (x : Stmt)
    (h : treeRoot cfg vkC vkL (d + 1) xs = some x) :
    ∃ t a b, x = nodeStmt cfg vkC vkL t t a b := by
  suffices ∀ d t xs, treeRoot.go cfg vkC vkL t (d + 1) xs = some x →
      ∃ t a b, x = nodeStmt cfg vkC vkL t t a b from this d .leaf xs h
  intro d
  induction d with
  | zero =>
    intro t xs h
    simp only [treeRoot.go, Option.bind_eq_some_iff] at h
    obtain ⟨ys, hys, hgo⟩ := h
    match ys, hgo with
    | [y], hgo =>
      simp only [treeRoot.go, Option.some.injEq] at hgo; subst hgo
      obtain ⟨a, b, e⟩ := mem_pairUp cfg vkC vkL t xs [y] hys y (List.mem_singleton_self y)
      exact ⟨t, a, b, e⟩
  | succ d ih =>
    intro t xs h
    have h' : (pairUp cfg vkC vkL t xs).bind (treeRoot.go cfg vkC vkL .node (d + 1)) = some x := h
    obtain ⟨ys, -, hgo⟩ := Option.bind_eq_some_iff.mp h'
    exact ih .node ys hgo

/-- What the organiser's root check accepts: the recomputed statement tree. -/
theorem rootOK_iff (C L : Layout K) (d : ℕ) (xs : List Stmt) (x : Stmt) :
    rootOK cfg P C L d xs x = true ↔
      treeRoot cfg (index cfg P C) (index cfg P L) d xs = some x := by
  simp [rootOK]

/-- A tree of depth 1 is one node over two leaves. -/
theorem treeRoot_one (x₁ x₂ : Stmt) :
    treeRoot cfg vkC vkL 1 [x₁, x₂] = some (nodeStmt cfg vkC vkL .leaf .leaf x₁ x₂) := rfl

/-- A tree of depth 2 is a node over two nodes over two leaves each, in order. -/
theorem treeRoot_two (a b c e : Stmt) :
    treeRoot cfg vkC vkL 2 [a, b, c, e] = some (nodeStmt cfg vkC vkL .node .node
      (nodeStmt cfg vkC vkL .leaf .leaf a b) (nodeStmt cfg vkC vkL .leaf .leaf c e)) := rfl

/-- **The root check pins the keys**: at a root of depth `≥ 1` that passes `rootOK` and `aggOK`,
the node's keys have the digests of the indexer's keys for `C` and `L`. -/
theorem keys_of_root (C L : Layout K) (d : ℕ) (xs : List Stmt) (x : Stmt)
    (nw : NodeWitness P.vkLen) (hagg : aggOK cfg P x nw = true)
    (hroot : rootOK cfg P C L (d + 1) xs x = true) :
    nw.vkC.digest cfg = (index cfg P C).digest cfg ∧
      nw.vkL.digest cfg = (index cfg P L).digest cfg := by
  obtain ⟨a0, a1, -⟩ := (aggOK_iff cfg P x nw).mp hagg
  obtain ⟨t, a, b, rfl⟩ := treeRoot_node cfg _ _ d xs x ((rootOK_iff cfg P C L _ xs x).mp hroot)
  obtain ⟨r0, r1, -⟩ := nodeStmt_slot cfg (index cfg P C) (index cfg P L) t t a b
  exact ⟨(digestToSlot_inj (HashId.run_length _ _) (HashId.run_length _ _)).mp (a0.symm.trans r0),
    (digestToSlot_inj (HashId.run_length _ _) (HashId.run_length _ _)).mp (a1.symm.trans r1)⟩

end Nodes

end RecursionFast

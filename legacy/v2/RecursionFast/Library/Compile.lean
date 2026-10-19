/-
  RecursionFast.Library.Compile  (UNTRUSTED, kernel-checked)

  The honest compiled prover (`prove`, a specification; moved here from the contract, S3-m5,
  since no trusted statement uses it) and facts about the organiser's compilation
  (`Contract/Compile.lean`), for every protocol, every configuration (hash, arity 2/4/8/16) and
  every instance.

  Load-bearing:
  * `narg_complete`: if the honest compiled prover `prove` outputs a tape and the IOP verifier
    accepts the honest transcript on the Fiat–Shamir challenges, `NARG` accepts the tape under
    the indexer's key. `narg_complete_of_perfect` / `narg_complete_of_secure`: for a perfectly
    complete (e.g. secure) protocol, on every instance of `relK k`, every tape `prove` outputs is
    accepted. `prove_isSome`: there `prove` fails only by exceeding `tapeCap`.
  * `NARG_eq_true_iff`: what `NARG` accepts, unfolded (cap, 32-byte index root, the Fiat–Shamir
    pass, the query run against the openings); the form a recursion circuit must force (Stage 5).
  * `narg_local` (`runQ_local`): an accepted tape determines the Fiat–Shamir challenges, and on
    them the query program accepts every oracle list consistent with the roots, the plain oracles
    and the tape's authenticated openings (`Consistent`, `opened`). This is the deterministic core
    of BCS soundness; the binding of the openings to the roots (collision resistance) is not a
    Lean statement.
  * `depth_spec`: the trusted closed form `Cfg.depth` is the least `d` with
    `2^(logLen - logLeaf) ≤ A^d`, the header's definition.
  * `narg_oversize`: a tape beyond the cap is rejected.

  Ingredients (each general): the byte round trips (`K.ofBytes_bytes`, `kList_flatMap`,
  `takeN_append'`, `readMany_flatten`); Merkle path correctness for honest trees at every arity
  (`climb_pathOf`, `verifyPath_pathOf`, `readOpening_honest`); query replay (`runQ_record`: on the
  honest openings `runQ` is `QProg.eval`); the Fiat–Shamir transcript is the prover's honest
  transcript on its own challenges (`fsTranscript_eq`), and the verifier's pass over the honest
  rounds section re-derives those challenges (`pass_honest`, `chals_honest`, `views_honest`).
-/
import RecursionFast.Contract.Compile
import RecursionFast.Library.Blake2s
import RecursionFast.Library.RbrSound

namespace RecursionFast

/-! ## The dense Merkle tree (the header's definition)

The trusted `commit` computes the root sparsely (`nodeS`, S9F-M4); `commit_eq_commitDense` proves
it equal to this dense recursion, which hashes every node. -/

/-- Node `p` at height `h` of the Merkle tree of `o`, densely: at height 0 the digest of leaf `p`
(the zero digest beyond the last leaf), above it the hash of its `A` children
`A·p, …, A·p + A - 1`. -/
def node (cfg : Cfg) (o : Oracle) : ℕ → ℕ → Digest
  | 0, p => if p < o.shape.leaves then leafHash cfg (o.leaf p) else zeroDigest
  | h + 1, p =>
    cfg.hash.run ((List.range cfg.arity).flatMap fun i => node cfg o h (cfg.arity * p + i))

/-- The Merkle root of an oracle, densely: node 0 at height `depth`. -/
def commitDense (cfg : Cfg) (o : Oracle) : Digest := node cfg o (cfg.depth o.shape) 0

/-! ## The honest compiled prover (a specification)

Moved here from `Contract/Compile.lean` (S3-m5): no trusted statement uses it. -/

/-- The bytes a round puts in the rounds section: a prover round's plain elements or root. -/
def Round.tapeBytes (cfg : Cfg) : (r : Round) → r.Ty → List UInt8
  | .msg o, v => if o.plain then (List.ofFn v).flatMap K.bytes else commit cfg ⟨o, v⟩
  | .chal _ _, _ => []

/-- The honest transcript prefixes and sponge states under Fiat–Shamir: a prover round is the
prover's message, absorbed; a challenge round is decoded from the squeezed bytes. -/
def fsPrefixes (cfg : Cfg) {k : ℕ} (P : Protocol k) (L : Layout K) (x : Stmt)
    (w : List (Table K)) : (m : Fin (P.n + 1)) → Transcript P.shape m × Digest :=
  Fin.induction (Transcript.empty P.shape, seed cfg (index cfg P L) x) fun j acc =>
    if h : (P.shape j).isMsg then
      let v := P.prover.next (L, x) w ⟨j, h⟩ acc.1
      (acc.1.concat v, absorb cfg acc.2 ((P.shape j).tapeBytes cfg v))
    else
      let c := squeeze cfg acc.2 (P.shape j).chalLen
      (acc.1.concat ((P.shape j).decode c.1), c.2)

/-- The honest transcript under Fiat–Shamir. -/
def fsTranscript (cfg : Cfg) {k : ℕ} (P : Protocol k) (L : Layout K) (x : Stmt)
    (w : List (Table K)) : FullTranscript P.shape :=
  (fsPrefixes cfg P L x w (Fin.last P.n)).1

/-- The authentication path of leaf `l` of `o`: at each height `h`, the `A` children of the parent
of the current node `p = l / A^h`, with `p` itself removed (computed sparsely, as `commit`). -/
def pathOf (cfg : Cfg) (o : Oracle) (l : ℕ) : List (List Digest) :=
  let d := cfg.depth o.shape
  let tE := tower cfg (leafHash cfg (List.replicate (2 ^ o.shape.logLeaf) 0)) (d + 1)
  let tZ := tower cfg zeroDigest (d + 1)
  (List.range d).map fun h =>
    ((List.range cfg.arity).map fun i =>
      (nodeS cfg o tE tZ h (cfg.arity * (l / cfg.arity ^ h / cfg.arity) + i)).1).eraseIdx
      (l / cfg.arity ^ h % cfg.arity)

/-- The openings section of the honest run of `p` on the oracles `os`: per query, nothing for a
plain prover oracle, otherwise the leaf's bytes and its path. -/
def record (cfg : Cfg) (os : List Oracle) : QProg Bool → Option Tape
  | .done _ => some []
  | .query j l cont => match os[j]? with
    | some o =>
      if l < o.shape.leaves then
        (record cfg os (cont (o.leaf l))).map fun t =>
          (if j != 0 && o.shape.plain then []
            else (o.leaf l).flatMap K.bytes ++ (pathOf cfg o l).flatten.flatten) ++ t
      else none
    | none => none

/-- **The honest compiled prover**: the rounds section of the Fiat–Shamir transcript, then the
openings of the verifier's run on it; `none` if that run fails or the tape exceeds the cap. -/
def prove (cfg : Cfg) {k : ℕ} (P : Protocol k) (L : Layout K) (x : Stmt) (w : List (Table K)) :
    Option Tape :=
  let tr := fsTranscript cfg P L x w
  match record cfg (⟨P.idxShape, P.IDX L⟩ :: tr.oracles) (P.verify (P.VK L) x (chalOf tr)) with
  | some op =>
    let t := (List.ofFn fun i => (P.shape i).tapeBytes cfg (tr i)).flatten ++ op
    if t.length ≤ tapeCap then some t else none
  | none => none

/-! ## Bytes -/

theorem HashId.run_length (h : HashId) (m : List UInt8) : (h.run m).length = 32 := by
  cases h; exact blake2s256_length m

theorem K.bytes_length (a : K) : a.bytes.length = 8 := by
  simp [K.bytes, K.toBytes]

theorem K.bytes_eq (a : K) : a.bytes = [UInt8.ofBitVec (a.bits.setWidth 8),
    UInt8.ofBitVec ((a.bits >>> 8).setWidth 8), UInt8.ofBitVec ((a.bits >>> 16).setWidth 8),
    UInt8.ofBitVec ((a.bits >>> 24).setWidth 8), UInt8.ofBitVec ((a.bits >>> 32).setWidth 8),
    UInt8.ofBitVec ((a.bits >>> 40).setWidth 8), UInt8.ofBitVec ((a.bits >>> 48).setWidth 8),
    UInt8.ofBitVec ((a.bits >>> 56).setWidth 8)] := by
  simp [K.bytes, K.toBytes, List.ofFn_succ]

/-- The little-endian bytes of a word read back to the word. -/
theorem wordOfBytes_bytes (a : K) (r : List UInt8) : wordOfBytes (a.bytes ++ r) = a.bits := by
  have step (y : Word) (s : ℕ) :
      (y >>> (s + 8)) <<< 8 ||| ((y >>> s).setWidth 8).setWidth 64 = y >>> s := by
    ext i hi
    by_cases h : i < 8
    · simp [h, BitVec.getLsbD_eq_getElem]
    · simp [h, Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_not_lt h)]
  simp only [K.bytes_eq, wordOfBytes, List.cons_append, List.nil_append, List.take_succ_cons,
    List.take_zero, List.foldr_cons, List.foldr_nil]
  rw [show (0 : Word) = a.bits >>> 64 from (BitVec.ushiftRight_eq_zero le_rfl).symm]
  simp only [step]
  exact step a.bits 0

theorem K.ofBytes_bytes (a : K) (r : List UInt8) : K.ofBytes (a.bytes ++ r) = a := by
  simp [K.ofBytes, wordOfBytes_bytes]

private theorem kList_go (as : List K) (acc : List K) :
    kList.go (as.flatMap K.bytes) acc = acc.reverse ++ as := by
  induction as generalizing acc with
  | nil => simp [kList.go]
  | cons a as ih =>
    have h := K.ofBytes_bytes a []
    simp only [K.bytes_eq, List.append_nil] at h
    simp [K.bytes_eq, kList.go, h, ih]

/-- The elements of a list read back from its bytes. -/
theorem kList_flatMap (as : List K) : kList (as.flatMap K.bytes) = as := by
  simp [kList, kList_go]

theorem takeN_append (b t acc : List UInt8) :
    takeN b.length (b ++ t) acc = some (acc.reverse ++ b, t) := by
  induction b generalizing acc with
  | nil => simp [takeN]
  | cons c b ih => simp [takeN, ih]

theorem takeN_append' {n : ℕ} (b t : List UInt8) (h : b.length = n) :
    takeN n (b ++ t) [] = some (b, t) := by
  subst h; simpa using takeN_append b t []

/-- `readMany` reads back `n` items written one after the other. -/
theorem readMany_flatten {α : Type} (r : Tape → Option (α × Tape)) (enc : α → List UInt8)
    (as : List α) (h : ∀ a ∈ as, ∀ t, r (enc a ++ t) = some (a, t)) (n : ℕ) (hn : as.length = n)
    (t : Tape) : readMany r n ((as.map enc).flatten ++ t) = some (as, t) := by
  subst hn
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [readMany, h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-! ## Merkle trees -/

section Merkle
variable (cfg : Cfg)

theorem Cfg.two_le_arity : 2 ≤ cfg.arity := by
  rcases cfg.arity_ok with h | h | h | h <;> omega

theorem node_length (o : Oracle) (h p : ℕ) : (node cfg o h p).length = 32 := by
  cases h <;> simp [node, leafHash, HashId.run_length, zeroDigest, apply_ite List.length]

theorem Cfg.arity_eq : cfg.arity = 2 ^ cfg.logArity ∧ 1 ≤ cfg.logArity := by
  rcases cfg.arity_ok with h | h | h | h <;> simp [Cfg.logArity, h]

/-- **The depth is the least `d` with `2^(logLen - logLeaf) ≤ A^d`** (the header's definition;
the trusted `Cfg.depth` is the closed form `⌈(logLen - logLeaf) / log₂ A⌉`). -/
theorem depth_spec (o : OShape) :
    2 ^ (o.logLen - o.logLeaf) ≤ cfg.arity ^ cfg.depth o ∧
      ∀ d, 2 ^ (o.logLen - o.logLeaf) ≤ cfg.arity ^ d → cfg.depth o ≤ d := by
  obtain ⟨hA, ha⟩ := cfg.arity_eq
  set m := o.logLen - o.logLeaf
  set a := cfg.logArity
  have hq := Nat.div_add_mod (m + a - 1) a
  have hr := Nat.mod_lt (m + a - 1) (show 0 < a by omega)
  have hd : cfg.depth o = (m + a - 1) / a := rfl
  rw [hd, hA]
  refine ⟨?_, fun d h => ?_⟩
  · rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [← pow_mul] at h
  have h' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  by_contra hlt
  have := Nat.mul_le_mul_left a (show d + 1 ≤ (m + a - 1) / a by omega)
  rw [Nat.mul_succ] at this
  omega

theorem leaves_le_pow_depth (o : OShape) : o.leaves ≤ cfg.arity ^ cfg.depth o :=
  (depth_spec cfg o).1

/-- The parent of `A` equal children `d`. -/
def up (d : Digest) : Digest := cfg.hash.run (List.replicate cfg.arity d).flatten

theorem tower_getD (d : Digest) (n h : ℕ) (hh : h < n) :
    (tower cfg d n)[h]?.getD [] = (up cfg)^[h] d := by
  induction n generalizing d h with
  | zero => omega
  | succ n ih =>
    cases h with
    | zero => rfl
    | succ h =>
      rw [Function.iterate_succ_apply]
      exact ih (up cfg d) h (by omega)

/-- A dense subtree made of padding positions only is the tower of the zero digest. -/
theorem node_padding (o : Oracle) (h p : ℕ) (hp : o.shape.leaves ≤ cfg.arity ^ h * p) :
    node cfg o h p = (up cfg)^[h] zeroDigest := by
  induction h generalizing p with
  | zero => simp [node, show ¬ p < o.shape.leaves by simpa using hp]
  | succ h ih =>
    have hc : ∀ i, node cfg o h (cfg.arity * p + i) = (up cfg)^[h] zeroDigest := fun i =>
      ih _ (hp.trans (by rw [pow_succ, Nat.mul_assoc, Nat.mul_add]; omega))
    simp [node, List.flatMap_def, hc, Function.iterate_succ_apply', up, List.map_const']

/-- A leaf all of whose elements are zero is the all-zero leaf. -/
theorem leaf_eq_zero (o : Oracle) (p : ℕ) (h : (o.leaf p).all (· == 0) = true) :
    o.leaf p = List.replicate (2 ^ o.shape.logLeaf) 0 := by
  refine List.eq_replicate_iff.mpr ⟨by simp [Oracle.leaf], fun a ha => ?_⟩
  simpa using List.all_eq_true.mp h a ha

/-- **The sparse node is the dense node** (and an empty node is the tower of the all-zero leaf's
digest), at every height up to the towers' length. -/
theorem nodeS_eq (o : Oracle) (n : ℕ) (h p : ℕ) (hh : h < n) :
    let E0 := leafHash cfg (List.replicate (2 ^ o.shape.logLeaf) 0)
    (nodeS cfg o (tower cfg E0 n) (tower cfg zeroDigest n) h p).1 = node cfg o h p ∧
      ((nodeS cfg o (tower cfg E0 n) (tower cfg zeroDigest n) h p).2 = true →
        node cfg o h p = (up cfg)^[h] E0) := by
  intro E0
  induction h generalizing p with
  | zero =>
    by_cases hp : p < o.shape.leaves
    · by_cases hz : (o.leaf p).all (· == 0) = true
      · simp [nodeS, node, hp, tower_getD cfg _ n 0 hh, leaf_eq_zero o p hz, E0]
      · simp [nodeS, node, hp, hz]
    · simp [nodeS, node, hp, tower_getD cfg _ n 0 hh]
  | succ h ih =>
    by_cases hpad : o.shape.leaves ≤ cfg.arity ^ (h + 1) * p
    · simp [nodeS, hpad, tower_getD cfg _ n _ hh, node_padding cfg o _ _ hpad]
    have ihc := fun i => ih (cfg.arity * p + i) (by omega)
    have hmap : ((List.range cfg.arity).map fun i =>
        (nodeS cfg o (tower cfg E0 n) (tower cfg zeroDigest n) h (cfg.arity * p + i)).1) =
        (List.range cfg.arity).map fun i => node cfg o h (cfg.arity * p + i) :=
      List.map_congr_left fun i _ => (ihc i).1
    by_cases hall : ((List.range cfg.arity).map fun i =>
        nodeS cfg o (tower cfg E0 n) (tower cfg zeroDigest n) h (cfg.arity * p + i)).all (·.2)
    · have hch : ∀ i ∈ List.range cfg.arity,
          node cfg o h (cfg.arity * p + i) = (up cfg)^[h] E0 := fun i hi =>
        (ihc i).2 (by simpa using List.all_eq_true.mp hall _ (List.mem_map_of_mem hi))
      have hnode : node cfg o (h + 1) p = (up cfg)^[h + 1] E0 := by
        simp only [node, List.flatMap_def, List.map_congr_left hch, List.map_const',
          List.length_range, Function.iterate_succ_apply', up]
      simp only [nodeS, hpad, ↓reduceIte, hall, List.getD_eq_getElem?_getD,
        tower_getD cfg _ n _ hh, hnode, and_self, implies_true]
    · refine ⟨?_, fun h' => by simp [nodeS, hpad, hall] at h'⟩
      simp only [nodeS, hpad, ↓reduceIte, hall, Bool.false_eq_true, List.map_map,
        Function.comp_def]
      rw [hmap, node, List.flatMap_def]

/-- **The trusted sparse `commit` computes the dense Merkle root** (S9F-M4: same root, same
paths, same tapes). -/
theorem commit_eq_commitDense (o : Oracle) : commit cfg o = commitDense cfg o :=
  (nodeS_eq cfg o _ _ 0 (Nat.lt_succ_self _)).1

theorem commit_length (o : Oracle) : (commit cfg o).length = 32 := by
  rw [commit_eq_commitDense]; exact node_length cfg o _ _

/-- The honest path, with the dense tree's nodes. -/
theorem pathOf_eq_dense (o : Oracle) (l : ℕ) :
    pathOf cfg o l = (List.range (cfg.depth o.shape)).map fun h =>
      ((List.range cfg.arity).map fun i =>
        node cfg o h (cfg.arity * (l / cfg.arity ^ h / cfg.arity) + i)).eraseIdx
        (l / cfg.arity ^ h % cfg.arity) :=
  List.map_congr_left fun h hh => by
    rw [List.map_congr_left fun i _ =>
      (nodeS_eq cfg o _ h _ (Nat.lt_succ_of_lt (List.mem_range.mp hh))).1]

/-- Insert the node back among its siblings: the parent's children. -/
private theorem insert_eraseIdx {α : Type} (l : List α) (r : ℕ) (hr : r < l.length) :
    (l.eraseIdx r).take r ++ l[r] :: (l.eraseIdx r).drop r = l := by
  rw [List.eraseIdx_eq_take_drop_succ, List.take_append_of_le_length (by simp; omega),
    List.drop_append_of_le_length (by simp; omega)]
  simp [List.getElem_cons_drop, List.take_take]

/-- Climbing the honest path from height `h` reaches the root. -/
private theorem climb_honest (o : Oracle) (l : ℕ) (hl : l < cfg.arity ^ cfg.depth o.shape) :
    ∀ j h, h + j = cfg.depth o.shape →
      climb cfg (node cfg o h (l / cfg.arity ^ h)) (l / cfg.arity ^ h)
        ((List.range' h j).map fun h =>
          ((List.range cfg.arity).map fun i =>
            node cfg o h (cfg.arity * (l / cfg.arity ^ h / cfg.arity) + i)).eraseIdx
            (l / cfg.arity ^ h % cfg.arity)) = commit cfg o := by
  have hA := cfg.two_le_arity
  intro j
  induction j with
  | zero =>
    rintro h (rfl : h = _)
    simp [climb, commit_eq_commitDense, commitDense, Nat.div_eq_of_lt hl]
  | succ j ih =>
    intro h hh
    rw [List.range'_succ, List.map_cons, climb]
    have hr : l / cfg.arity ^ h % cfg.arity < cfg.arity := Nat.mod_lt _ (by omega)
    have key := insert_eraseIdx ((List.range cfg.arity).map fun i =>
      node cfg o h (cfg.arity * (l / cfg.arity ^ h / cfg.arity) + i)) _ (by simpa using hr)
    simp only [List.getElem_map, List.getElem_range, Nat.div_add_mod] at key
    rw [key, ← ih (h + 1) (by omega)]
    congr 1
    · simp [node, List.flatMap_def, Nat.div_div_eq_div_mul, pow_succ]
    · rw [Nat.div_div_eq_div_mul, ← pow_succ]

/-- **Merkle path correctness**: the honest path of a leaf climbs to the root. -/
theorem climb_pathOf (o : Oracle) (l : ℕ) (hl : l < o.shape.leaves) :
    climb cfg (leafHash cfg (o.leaf l)) l (pathOf cfg o l) = commit cfg o := by
  simpa [node, hl, pathOf_eq_dense, List.range_eq_range'] using
    climb_honest cfg o l (hl.trans_le (leaves_le_pow_depth cfg o.shape)) _ 0 (Nat.zero_add _)

theorem verifyPath_pathOf (o : Oracle) (l : ℕ) (hl : l < o.shape.leaves) :
    verifyPath cfg (commit cfg o) l (o.leaf l) (pathOf cfg o l) = true := by
  simp [verifyPath, climb_pathOf cfg o l hl]

end Merkle

/-! ## Openings and query replay -/

section Replay
variable (cfg : Cfg)

theorem Oracle.leaf_length (o : Oracle) (l : ℕ) : (o.leaf l).length = 2 ^ o.shape.logLeaf := by
  simp [Oracle.leaf]

theorem flatMap_bytes_length (as : List K) : (as.flatMap K.bytes).length = 8 * as.length := by
  simp [K.bytes_length, mul_comm]

/-- The honest opening of leaf `l` parses back to the leaf and its path. -/
theorem readOpening_honest (o : Oracle) (l : ℕ) (t : Tape) :
    readOpening cfg o.shape
        ((o.leaf l).flatMap K.bytes ++ ((pathOf cfg o l).flatten.flatten ++ t)) =
      some (o.leaf l, pathOf cfg o l, t) := by
  have hA := cfg.two_le_arity
  have hlev : ∀ lev ∈ pathOf cfg o l, ∀ t, readMany (fun t => takeN 32 t []) (cfg.arity - 1)
      (lev.flatten ++ t) = some (lev, t) := by
    intro lev hlev t
    rw [pathOf_eq_dense] at hlev
    obtain ⟨h, -, rfl⟩ := List.mem_map.mp hlev
    have hlen := List.length_eraseIdx_of_lt (l := (List.range cfg.arity).map fun i =>
      node cfg o h (cfg.arity * (l / cfg.arity ^ h / cfg.arity) + i))
      (i := l / cfg.arity ^ h % cfg.arity) (by simpa using Nat.mod_lt _ (by omega))
    simp only [List.length_map, List.length_range] at hlen
    have := readMany_flatten (fun t => takeN 32 t []) id _ (fun d hd t => takeN_append' d t (by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_eraseIdx hd)
      exact node_length cfg o h _)) _ hlen t
    simpa using this
  have hpath := readMany_flatten _ List.flatten (pathOf cfg o l) hlev (cfg.depth o.shape)
    (by simp [pathOf_eq_dense]) t
  rw [List.flatten_flatten, readOpening,
    takeN_append' _ _ (by rw [flatMap_bytes_length, Oracle.leaf_length])]
  simp [hpath, kList_flatMap]

/-- What the honest compiled verifier holds of oracle `o` (`idx`: it is the index oracle). -/
def viewOf (idx : Bool) (o : Oracle) : View :=
  if !idx && o.shape.plain then .plain o.shape (List.ofFn o.data) else .root o.shape (commit cfg o)

theorem leaf_of_plain (o : Oracle) (h : o.shape.plain = true) (l : ℕ) (hl : l < o.shape.leaves) :
    o.leaf l = List.ofFn o.data := by
  obtain ⟨⟨len, lf⟩, data⟩ := o
  obtain rfl : lf = len := by simpa [OShape.plain] using h
  obtain rfl : l = 0 := by
    simpa only [OShape.leaves, Nat.sub_self, pow_zero, Nat.lt_one_iff] using hl
  simp [Oracle.leaf, Oracle.get]

/-- **Query replay**: on the openings the honest prover records, the compiled run of a query
program agrees with its evaluation on the oracles. -/
theorem runQ_record (os : List Oracle) (vs : Array View)
    (hvs : ∀ j o, os[j]? = some o → vs[j]? = some (viewOf cfg (j == 0) o)) (p : QProg Bool)
    (op : Tape) (h : record cfg os p = some op) : runQ cfg vs p op = p.eval os := by
  induction p generalizing op with
  | done b => cases h; rfl
  | query j l cont ih =>
    rcases hj : os[j]? with _ | o
    · simp [record, hj] at h
    simp only [record, hj, Option.ite_none_right_eq_some, Option.map_eq_some_iff] at h
    obtain ⟨hl, op', hrec, rfl⟩ := h
    have hv := hvs j o hj
    simp only [QProg.eval, hj, hl, ↓reduceIte, ← ih _ op' hrec]
    by_cases hp : (j != 0 && o.shape.plain) = true
    · have hv' : vs[j]? = some (.plain o.shape (o.leaf l)) := by
        rw [hv, viewOf, leaf_of_plain o (Bool.and_elim_right hp) l hl]; simp_all
      simp [runQ, hv', hp, hl]
    · have hv' : vs[j]? = some (.root o.shape (commit cfg o)) := by
        rw [hv, viewOf]; simp_all
      simp [runQ, hv', hp, hl, readOpening_honest, verifyPath_pathOf cfg o l hl]

end Replay

/-! ## The Fiat–Shamir transcript -/

section FS

/-- Prefixes built by appending one value per round are the prefixes of the last one. -/
theorem prefixes_eq_pre {n : ℕ} {sh : Fin n → Round} (F : (m : Fin (n + 1)) → Transcript sh m)
    (hF : ∀ j : Fin n, ∃ a, F j.succ = (F j.castSucc).concat a) (m : Fin (n + 1)) :
    F m = pre (F (Fin.last n)) m := by
  induction m using Fin.reverseInduction with
  | last => rfl
  | cast j ih =>
    obtain ⟨a, ha⟩ := hF j
    funext i
    have h1 := congrFun ha i.castSucc
    rw [Transcript.concat_castSucc] at h1
    rw [← h1, ih]; rfl

variable (cfg : Cfg) {k : ℕ} (P : Protocol k) (L : Layout K) (x : Stmt) (w : List (Table K))

theorem fsPrefixes_zero :
    fsPrefixes cfg P L x w 0 = (Transcript.empty P.shape, seed cfg (index cfg P L) x) := rfl

theorem fsPrefixes_msg (j : Fin P.n) (h : (P.shape j).isMsg = true) :
    fsPrefixes cfg P L x w j.succ =
      let v := P.prover.next (L, x) w ⟨j, h⟩ (fsPrefixes cfg P L x w j.castSucc).1
      ((fsPrefixes cfg P L x w j.castSucc).1.concat v,
        absorb cfg (fsPrefixes cfg P L x w j.castSucc).2 ((P.shape j).tapeBytes cfg v)) :=
  (Fin.induction_succ _ _ _).trans (dite_eq_left h)

theorem fsPrefixes_chal (j : Fin P.n) (h : (P.shape j).isMsg = false) :
    fsPrefixes cfg P L x w j.succ =
      let c := squeeze cfg (fsPrefixes cfg P L x w j.castSucc).2 (P.shape j).chalLen
      ((fsPrefixes cfg P L x w j.castSucc).1.concat ((P.shape j).decode c.1), c.2) :=
  (Fin.induction_succ _ _ _).trans (dite_eq_right (Bool.ne_true_of_eq_false h))

theorem fsPrefixes_eq_pre (m : Fin (P.n + 1)) :
    (fsPrefixes cfg P L x w m).1 = pre (fsTranscript cfg P L x w) m := by
  refine prefixes_eq_pre (fun m => (fsPrefixes cfg P L x w m).1) (fun j => ?_) m
  cases h : (P.shape j).isMsg
  · exact ⟨_, by rw [fsPrefixes_chal cfg P L x w j h]⟩
  · exact ⟨_, by rw [fsPrefixes_msg cfg P L x w j h]⟩

/-- Round `j` of the Fiat–Shamir transcript is the value appended at step `j`. -/
theorem fsTranscript_apply (j : Fin P.n) :
    fsTranscript cfg P L x w j = (fsPrefixes cfg P L x w j.succ).1 (Fin.last j) := by
  rw [fsPrefixes_eq_pre]; rfl

theorem fsTranscript_msg (j : Fin P.n) (h : (P.shape j).isMsg = true) :
    fsTranscript cfg P L x w j =
      P.prover.next (L, x) w ⟨j, h⟩ (fsPrefixes cfg P L x w j.castSucc).1 := by
  rw [fsTranscript_apply, fsPrefixes_msg cfg P L x w j h]; exact Transcript.concat_last _ _

theorem fsTranscript_chal (j : Fin P.n) (h : (P.shape j).isMsg = false) :
    fsTranscript cfg P L x w j = (P.shape j).decode
      (squeeze cfg (fsPrefixes cfg P L x w j.castSucc).2 (P.shape j).chalLen).1 := by
  rw [fsTranscript_apply, fsPrefixes_chal cfg P L x w j h]; exact Transcript.concat_last _ _

/-- The Fiat–Shamir transcript is the prover's honest transcript on its own challenges. -/
theorem fsTranscript_eq :
    fsTranscript cfg P L x w =
      P.prover.transcript (L, x) w (chalOf (fsTranscript cfg P L x w)) := by
  have hpre (m : Fin (P.n + 1)) : (fsPrefixes cfg P L x w m).1 =
      P.prover.prefixes (L, x) w (chalOf (fsTranscript cfg P L x w)) m := by
    induction m using Fin.induction with
    | zero => exact funext fun i => i.elim0
    | succ j ih =>
      rw [Strategy.prefixes, Fin.induction_succ, ← Strategy.prefixes, ← ih]
      by_cases h : (P.shape j).isMsg = true
      · rw [dite_eq_left h, fsPrefixes_msg cfg P L x w j h]
      · have h' := Bool.eq_false_of_ne_true h
        rw [dite_eq_right h, fsPrefixes_chal cfg P L x w j h']
        exact congrArg (Transcript.concat _) (fsTranscript_chal cfg P L x w j h').symm
  exact hpre (Fin.last P.n)

end FS

/-! ## The Fiat–Shamir pass -/

section Pass
variable (cfg : Cfg)

/-- One honest round: from state `s`, the round puts bytes `b` on the tape, the pass records `e`
and moves to state `s'`. -/
def StepOK : Round → Digest → List UInt8 → List UInt8 → Digest → Prop
  | .msg o, s, b, e, s' => b.length = msgLen o ∧ e = b ∧ s' = absorb cfg s b
  | .chal nE idx, s, b, e, s' => b = [] ∧ squeeze cfg s (Round.chal nE idx).chalLen = (e, s')

/-- The pass over a chain of honest rounds reads their bytes and records their entries. -/
theorem pass_chain (rs : List Round) (σ : ℕ → Digest) (B E : ℕ → List UInt8)
    (h : ∀ i (hi : i < rs.length), StepOK cfg rs[i] (σ i) (B i) (E i) (σ (i + 1)))
    (t : Tape) (acc : Array (List UInt8)) :
    pass cfg rs (σ 0) (((List.range rs.length).map B).flatten ++ t) acc =
      some (acc ++ ((List.range rs.length).map E).toArray, t) := by
  induction rs generalizing σ B E acc with
  | nil => simp [pass]
  | cons r rs ih =>
    have h0 := h 0 (by simp)
    have ih' := ih (fun i => σ (i + 1)) (fun i => B (i + 1)) (fun i => E (i + 1))
      (fun i hi => h (i + 1) (by simpa using hi))
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.flatten_cons, List.append_assoc] at ih' ⊢
    cases r with
    | msg o =>
      obtain ⟨hlen, hE, hσ⟩ := h0
      simp only [pass, takeN_append' _ _ hlen]
      rw [← hσ, Function.comp_def, ih' (acc.push (B 0)), ← hE]
      simp [Function.comp_def]
    | chal nE idx =>
      obtain ⟨hB, hsq⟩ := h0
      simp only [pass, hB, List.nil_append, hsq]
      rw [Function.comp_def, ih' (acc.push (E 0))]
      simp [Function.comp_def]

end Pass

/-! ## Completeness of the compilation -/

section Complete
variable (cfg : Cfg)

private theorem ofFn_eq_map_range {α : Type} {n : ℕ} (f : Fin n → α) (d : α) :
    List.ofFn f = (List.range n).map fun i => if h : i < n then f ⟨i, h⟩ else d :=
  List.ext_getElem (by simp) fun i h1 _ => by simp [show i < n by simpa using h1]

theorem msgLen_tapeBytes (o : OShape) (v : OVal o) :
    ((Round.msg o).tapeBytes cfg v).length = msgLen o := by
  simp only [Round.tapeBytes, msgLen, apply_ite List.length, flatMap_bytes_length, List.length_ofFn,
    commit_length]

theorem stepOK_of (r : Round) (v : r.Ty) (s s' : Digest) (e : List UInt8)
    (hm : r.isMsg = true → e = r.tapeBytes cfg v ∧ s' = absorb cfg s (r.tapeBytes cfg v))
    (hc : r.isMsg = false → squeeze cfg s r.chalLen = (e, s')) :
    StepOK cfg r s (r.tapeBytes cfg v) e s' := by
  cases r with
  | msg o => exact ⟨msgLen_tapeBytes cfg o v, (hm rfl).1, (hm rfl).2⟩
  | chal nE idx => exact ⟨rfl, hc rfl⟩

theorem roundViews_tapeBytes (r : Round) (v : r.Ty) (e : List UInt8)
    (he : r.isMsg = true → e = r.tapeBytes cfg v) :
    roundViews r e = (r.oracles v).map (viewOf cfg false) := by
  cases r with
  | msg o =>
    rw [he rfl]
    simp only [roundViews, Round.tapeBytes, Round.oracles, viewOf, List.map_cons, List.map_nil]
    split <;> simp_all [kList_flatMap]
  | chal nE idx => rfl

variable {k : ℕ} (P : Protocol k) (L : Layout K) (x : Stmt) (w : List (Table K))

/-- What the Fiat–Shamir pass records for round `j` of the honest run. -/
def fsEntry (j : Fin P.n) : List UInt8 :=
  if (P.shape j).isMsg then (P.shape j).tapeBytes cfg (fsTranscript cfg P L x w j)
  else (squeeze cfg (fsPrefixes cfg P L x w j.castSucc).2 (P.shape j).chalLen).1

/-- **The Fiat–Shamir pass on the honest tape** reads the rounds section and records the honest
entries. -/
theorem pass_honest (op : Tape) :
    pass cfg (List.ofFn P.shape) (seed cfg (index cfg P L) x)
      ((List.ofFn fun i => (P.shape i).tapeBytes cfg (fsTranscript cfg P L x w i)).flatten ++ op)
      #[] =
      some ((List.ofFn (fsEntry cfg P L x w)).toArray, op) := by
  let σ : ℕ → Digest := fun i => if h : i < P.n + 1 then (fsPrefixes cfg P L x w ⟨i, h⟩).2 else []
  have := pass_chain cfg (List.ofFn P.shape) σ
    (fun i => if h : i < P.n then (P.shape ⟨i, h⟩).tapeBytes cfg (fsTranscript cfg P L x w ⟨i, h⟩)
      else [])
    (fun i => if h : i < P.n then fsEntry cfg P L x w ⟨i, h⟩ else []) (fun i hi => by
      simp only [List.length_ofFn] at hi
      have hσ0 : σ i = (fsPrefixes cfg P L x w (Fin.castSucc ⟨i, hi⟩)).2 :=
        dite_eq_left (Nat.lt_succ_of_lt hi)
      have hσ1 : σ (i + 1) = (fsPrefixes cfg P L x w (Fin.succ ⟨i, hi⟩)).2 :=
        dite_eq_left (Nat.succ_lt_succ hi)
      simp only [List.getElem_ofFn, hi, ↓reduceDIte, hσ0, hσ1]
      refine stepOK_of cfg _ _ _ _ _ (fun hm => ?_) (fun hc => ?_)
      · refine ⟨by simp [fsEntry, hm], ?_⟩
        rw [fsPrefixes_msg cfg P L x w _ hm, fsTranscript_msg cfg P L x w _ hm]
      · rw [fsPrefixes_chal cfg P L x w _ hc]
        simp [fsEntry, hc]) op #[]
  have hσ : σ 0 = seed cfg (index cfg P L) x := congrArg Prod.snd (fsPrefixes_zero cfg P L x w)
  rw [ofFn_eq_map_range (fun i => (P.shape i).tapeBytes cfg (fsTranscript cfg P L x w i)) [],
    ofFn_eq_map_range (fsEntry cfg P L x w) []]
  simpa [hσ] using this

theorem chals_honest :
    chals P.shape ((List.ofFn (fsEntry cfg P L x w)).toArray.map fun b => (kList b).toArray) =
      chalOf (fsTranscript cfg P L x w) := by
  funext c
  simp [chals, chalOf, fsEntry, c.2, fsTranscript_chal cfg P L x w c.1 c.2, Round.decode]

theorem views_honest :
    views P (commit cfg ⟨P.idxShape, P.IDX L⟩) (List.ofFn (fsEntry cfg P L x w)).toArray =
      (viewOf cfg true ⟨P.idxShape, P.IDX L⟩ ::
        (fsTranscript cfg P L x w).oracles.map (viewOf cfg false)).toArray := by
  simp only [views, FullTranscript.oracles, List.map_flatten, List.map_ofFn]
  congr 3
  refine congrArg List.ofFn (funext fun i => roundViews_tapeBytes cfg _ _ _ fun hm => ?_)
  simp [fsEntry, hm]

/-- **Completeness of the compilation.** If the honest compiled prover outputs a tape and the
IOP verifier accepts the honest transcript on the Fiat–Shamir challenges, the compiled verifier
accepts the tape under the indexer's key. -/
theorem narg_complete (t : Tape) (ht : prove cfg P L x w = some t)
    (hacc : P.specVerifier (L, x) (fsTranscript cfg P L x w) = some ()) :
    NARG cfg P (index cfg P L) x t = true := by
  set tr := fsTranscript cfg P L x w
  set os : List Oracle := ⟨P.idxShape, P.IDX L⟩ :: tr.oracles
  have heval : (P.verify (P.VK L) x (chalOf tr)).eval os = some true := by
    simpa only [Protocol.specVerifier, Option.ite_none_right_eq_some, and_true] using hacc
  simp only [prove] at ht
  split at ht
  · rename_i op hrec
    obtain ⟨hcap, ⟨⟩⟩ := Option.ite_none_right_eq_some.mp ht
    have hvs : ∀ j o, os[j]? = some o →
        ((viewOf cfg true ⟨P.idxShape, P.IDX L⟩ :: tr.oracles.map (viewOf cfg false)).toArray)[j]? =
          some (viewOf cfg (j == 0) o) := by
      rintro (_ | j) o hj <;> simp_all [os]
    have hroot : (index cfg P L).2.length = 32 := commit_length cfg _
    rw [NARG, decide_eq_true hcap, hroot, pass_honest]
    dsimp only
    rw [index, chals_honest, views_honest, runQ_record cfg os _ hvs _ op hrec, heval]; rfl
  · simp at ht

/-- Completeness of the compilation for a perfectly complete protocol: on every instance of the
relation, a tape the honest compiled prover outputs is accepted. -/
theorem narg_complete_of_perfect
    (hP : PerfectComplete (relK k) Set.univ P.prover P.specVerifier) (hrel : ((L, x), w) ∈ relK k)
    (t : Tape) (ht : prove cfg P L x w = some t) : NARG cfg P (index cfg P L) x t = true :=
  narg_complete cfg P L x w t ht (fsTranscript_eq cfg P L x w ▸ (hP (L, x) w hrel _).1)

/-- **Completeness of the compilation for a secure protocol.** -/
theorem narg_complete_of_secure (hP : P.Secure) (hrel : ((L, x), w) ∈ relK k) (t : Tape)
    (ht : prove cfg P L x w = some t) : NARG cfg P (index cfg P L) x t = true :=
  narg_complete_of_perfect cfg P L x w hP.complete hrel t ht

end Complete

/-! ## Totality of the honest openings -/

/-- The honest prover records openings whenever the query program's run terminates. -/
theorem record_isSome (cfg : Cfg) (os : List Oracle) (p : QProg Bool) (b : Bool)
    (h : p.eval os = some b) : ∃ op, record cfg os p = some op := by
  induction p with
  | done a => exact ⟨[], rfl⟩
  | query j l cont ih =>
    cases hj : os[j]? with
    | none => simp [QProg.eval, hj] at h
    | some o =>
      by_cases hl : l < o.shape.leaves
      · obtain ⟨op, hop⟩ := ih _ (by simpa only [QProg.eval, hj, hl, ↓reduceIte] using h)
        simp only [record, hj, hl, ↓reduceIte, hop, Option.map_some, Option.some.injEq, exists_eq']
      · simp [QProg.eval, hj, hl] at h

/-- For a perfectly complete protocol, on the relation the honest compiled prover fails only by
exceeding the tape cap. -/
theorem prove_isSome {k : ℕ} (cfg : Cfg) (P : Protocol k) (L : Layout K) (x : Stmt)
    (w : List (Table K)) (hP : PerfectComplete (relK k) Set.univ P.prover P.specVerifier)
    (hrel : ((L, x), w) ∈ relK k) :
    ∃ op, record cfg (⟨P.idxShape, P.IDX L⟩ :: (fsTranscript cfg P L x w).oracles)
      (P.verify (P.VK L) x (chalOf (fsTranscript cfg P L x w))) = some op ∧
      prove cfg P L x w =
        let t := (List.ofFn fun i =>
          (P.shape i).tapeBytes cfg (fsTranscript cfg P L x w i)).flatten ++ op
        if t.length ≤ tapeCap then some t else none := by
  have h := (hP (L, x) w hrel (chalOf (fsTranscript cfg P L x w))).1
  rw [← fsTranscript_eq] at h
  simp only [Protocol.specVerifier, Option.ite_none_right_eq_some, and_true] at h
  obtain ⟨op, hop⟩ := record_isSome cfg _ _ _ h
  exact ⟨op, hop, by simp only [prove, hop]⟩

/-! ## Locality: an accepted tape is accepted by the IOP verifier on consistent oracles -/

/-- The leaves a compiled run opens and authenticates, in order: oracle, position, leaf. -/
def opened (cfg : Cfg) (vs : Array View) : QProg Bool → Tape → List (ℕ × ℕ × List K)
  | .done _, _ => []
  | .query j l cont, t => match vs[j]? with
    | some (.plain o ws) => if l < o.leaves then opened cfg vs (cont ws) t else []
    | some (.root o r) =>
      if l < o.leaves then
        match readOpening cfg o t with
        | some (leaf, path, t) =>
          if verifyPath cfg r l leaf path then (j, l, leaf) :: opened cfg vs (cont leaf) t else []
        | none => []
      else []
    | none => []

/-- The shape of the oracle a view stands for. -/
def View.shape : View → OShape
  | .root o _ => o
  | .plain o _ => o

/-- Oracles `os` agree with the views `vs` (shapes; plain contents) and with the opened leaves. -/
def Consistent (vs : Array View) (os : List Oracle) (ops : List (ℕ × ℕ × List K)) : Prop :=
  (∀ j : ℕ, (os[j]?).map Oracle.shape = (vs[j]?).map View.shape) ∧
  (∀ (j : ℕ) (o : OShape) (ws : List K) (o' : Oracle), vs[j]? = some (View.plain o ws) →
    os[j]? = some o' → ∀ l < o.leaves, o'.leaf l = ws) ∧
  (∀ op ∈ ops, (os[op.1]?).map (·.leaf op.2.1) = some op.2.2)

/-- **Locality** (the compiled mirror of `probes/s1/VerifyNotLocal.lean`): the verdict of an
accepted compiled run is the verdict of the query program on every oracle list consistent with
the views and the opened leaves. -/
theorem runQ_local (cfg : Cfg) (vs : Array View) (p : QProg Bool) (t : Tape) (b : Bool)
    (h : runQ cfg vs p t = some b) (os : List Oracle) (hc : Consistent vs os (opened cfg vs p t)) :
    p.eval os = some b := by
  induction p generalizing t with
  | done a => cases t <;> simp_all [runQ, QProg.eval]
  | query j l cont ih =>
    obtain ⟨hsh, hpl, hop⟩ := hc
    rcases hv : vs[j]? with _ | v
    · simp [runQ, hv] at h
    rcases ho : os[j]? with _ | o'
    · simpa [ho, hv] using hsh j
    have hj : o'.shape = v.shape := by simpa [ho, hv] using hsh j
    cases v with
    | plain o ws =>
      simp only [runQ, hv, Option.ite_none_right_eq_some] at h
      obtain ⟨hl, h⟩ := h
      simp only [QProg.eval, ho, hj, View.shape, hl, ↓reduceIte, hpl j o ws o' hv ho l hl]
      refine ih ws t h ⟨hsh, hpl, fun op hmem => hop op ?_⟩
      simp [opened, hv, hl, hmem]
    | root o r =>
      simp only [runQ, hv, Option.ite_none_right_eq_some] at h
      obtain ⟨hl, h⟩ := h
      rcases hr : readOpening cfg o t with _ | ⟨leaf, path, t'⟩
      · simp [hr] at h
      simp only [hr, Option.ite_none_right_eq_some] at h
      obtain ⟨hvp, h⟩ := h
      have hmem : (j, l, leaf) ∈ opened cfg vs (.query j l cont) t := by
        simp [opened, hv, hl, hr, hvp]
      have hleaf : o'.leaf l = leaf := by simpa [ho] using hop _ hmem
      simp only [QProg.eval, ho, hj, View.shape, hl, ↓reduceIte, hleaf]
      refine ih leaf t' h ⟨hsh, hpl, fun op hmem' => hop op ?_⟩
      simp [opened, hv, hl, hr, hvp, hmem']

/-- **What `NARG` accepts**, unfolded (the form a recursion circuit `C_V` must force, Stage 5):
the cap, a 32-byte index root, the Fiat–Shamir pass, and the query program's run against the
openings, with no bytes left over. -/
theorem NARG_eq_true_iff {k : ℕ} (cfg : Cfg) (P : Protocol k) (vkc : VKc P.vkLen) (x : Stmt)
    (t : Tape) :
    NARG cfg P vkc x t = true ↔ t.length ≤ tapeCap ∧ vkc.2.length = 32 ∧
      ∃ es rest, pass cfg (List.ofFn P.shape) (seed cfg vkc x) t #[] = some (es, rest) ∧
        runQ cfg (views P vkc.2 es)
          (P.verify vkc.1 x (chals P.shape (es.map fun b => (kList b).toArray))) rest =
            some true := by
  simp only [NARG, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  split
  · rename_i es rest hpass
    simp [hpass]
  · rename_i hpass
    simp [hpass]

/-- **An accepted tape is a BCS witness**: the Fiat–Shamir pass succeeds, and on its challenges
the IOP verifier accepts every oracle list consistent with the roots, the plain oracles and the
authenticated openings of the tape. -/
theorem narg_local {k : ℕ} (cfg : Cfg) (P : Protocol k) (vkc : VKc P.vkLen) (x : Stmt) (t : Tape)
    (h : NARG cfg P vkc x t = true) :
    t.length ≤ tapeCap ∧ vkc.2.length = 32 ∧
      ∃ es rest, pass cfg (List.ofFn P.shape) (seed cfg vkc x) t #[] = some (es, rest) ∧
      ∀ os, Consistent (views P vkc.2 es) os (opened cfg (views P vkc.2 es)
          (P.verify vkc.1 x (chals P.shape (es.map fun b => (kList b).toArray))) rest) →
        (P.verify vkc.1 x (chals P.shape (es.map fun b => (kList b).toArray))).eval os =
          some true := by
  obtain ⟨hcap, hroot, es, rest, hpass, hrun⟩ := (NARG_eq_true_iff cfg P vkc x t).mp h
  exact ⟨hcap, hroot, es, rest, hpass, runQ_local cfg _ _ _ _ hrun⟩

/-- A tape beyond the cap is rejected. -/
theorem narg_oversize {k : ℕ} (cfg : Cfg) (P : Protocol k) (vkc : VKc P.vkLen) (x : Stmt) (t : Tape)
    (h : tapeCap < t.length) : NARG cfg P vkc x t = false := by
  simp [NARG, Nat.not_le.mpr h]

/-! ## Merkle binding (S9D-m5)

From the S3 review (`probes/s3/RevBinding.lean`), now checked in CI: at the fixed depth the shape
gives, two openings that `runQ` accepts for the same root and position carry the same leaf unless
the hash has a collision (`opening_binding`). This is the binding argument the header of
`Contract/Compile.lean` cites for "no leaf/node tag" (S3-A2). -/

section Binding
variable (cfg : Cfg)

/-- A collision of the configured hash. -/
def Collision : Prop := ∃ m m' : List UInt8, m ≠ m' ∧ cfg.hash.run m = cfg.hash.run m'

/-- A well-formed path level: `A - 1` digests of 32 bytes. -/
def LevelOK (lev : List Digest) : Prop := lev.length = cfg.arity - 1 ∧ ∀ d ∈ lev, d.length = 32

theorem flatten_length_32 (s : List Digest) (hs : ∀ e ∈ s, e.length = 32) :
    s.flatten.length = 32 * s.length := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      hs a List.mem_cons_self, ih fun e he => hs e (List.mem_cons_of_mem _ he)]
    ring

/-- The inserted digest is recovered from the flattened level. -/
theorem flatten_insert (s : List Digest) (d : Digest) (q : ℕ)
    (hs : ∀ e ∈ s, e.length = 32) (hd : d.length = 32) :
    ((s.take q ++ d :: s.drop q).flatten.drop (32 * (s.take q).length)).take 32 = d := by
  have hl := flatten_length_32 (s.take q) fun e he => hs e (List.mem_of_mem_take he)
  rw [List.flatten_append, List.flatten_cons, ← hl, List.drop_left]
  simp [hd]

theorem climb_binding (path path' : List (List Digest)) (d d' : Digest) (p : ℕ)
    (hd : d.length = 32) (hd' : d'.length = 32) (hlen : path.length = path'.length)
    (hp : ∀ lev ∈ path, LevelOK cfg lev) (hp' : ∀ lev ∈ path', LevelOK cfg lev)
    (h : climb cfg d p path = climb cfg d' p path') : d = d' ∨ Collision cfg := by
  induction path generalizing path' d d' p with
  | nil =>
    cases path' with
    | nil => exact Or.inl (by simpa [climb] using h)
    | cons _ _ => simp at hlen
  | cons s path ih =>
    cases path' with
    | nil => simp at hlen
    | cons s' path' =>
      simp only [climb] at h
      have hA := cfg.two_le_arity
      have hs := hp s List.mem_cons_self
      have hs' := hp' s' List.mem_cons_self
      rcases ih path' _ _ (p / cfg.arity) (HashId.run_length _ _) (HashId.run_length _ _)
          (by simpa using hlen) (fun l hl => hp l (List.mem_cons_of_mem _ hl))
          (fun l hl => hp' l (List.mem_cons_of_mem _ hl)) h with he | hc
      · by_cases hm : (s.take (p % cfg.arity) ++ d :: s.drop (p % cfg.arity)).flatten =
            (s'.take (p % cfg.arity) ++ d' :: s'.drop (p % cfg.arity)).flatten
        · left
          have hq : p % cfg.arity ≤ s.length := by rw [hs.1]; have := Nat.mod_lt p (by omega : 0 < cfg.arity); omega
          have hq' : p % cfg.arity ≤ s'.length := by rw [hs'.1]; have := Nat.mod_lt p (by omega : 0 < cfg.arity); omega
          have e1 := flatten_insert s d (p % cfg.arity) hs.2 hd
          have e2 := flatten_insert s' d' (p % cfg.arity) hs'.2 hd'
          rw [List.length_take_of_le hq] at e1
          rw [List.length_take_of_le hq', ← hm] at e2
          rw [← e1, ← e2]
        · exact Or.inr ⟨_, _, hm, he⟩
      · exact Or.inr hc

theorem verifyPath_binding (r : Digest) (l : ℕ) (leaf leaf' : List K)
    (path path' : List (List Digest)) (hlen : path.length = path'.length)
    (hp : ∀ lev ∈ path, LevelOK cfg lev) (hp' : ∀ lev ∈ path', LevelOK cfg lev)
    (h : verifyPath cfg r l leaf path = true) (h' : verifyPath cfg r l leaf' path' = true) :
    leaf = leaf' ∨ Collision cfg := by
  simp only [verifyPath, beq_iff_eq] at h h'
  rcases climb_binding cfg path path' _ _ l (HashId.run_length _ _) (HashId.run_length _ _) hlen
      hp hp' (h.trans h'.symm) with he | hc
  · by_cases hb : leaf.flatMap K.bytes = leaf'.flatMap K.bytes
    · left; rw [← kList_flatMap leaf, ← kList_flatMap leaf', hb]
    · exact Or.inr ⟨_, _, hb, he⟩
  · exact Or.inr hc

theorem takeN_length : ∀ (n : ℕ) (t acc b t' : List UInt8),
    takeN n t acc = some (b, t') → b.length = n + acc.length
  | 0, t, acc, b, t', h => by simp [takeN] at h; obtain ⟨rfl, -⟩ := h; simp
  | n + 1, [], acc, b, t', h => by simp [takeN] at h
  | n + 1, c :: t, acc, b, t', h => by
    have := takeN_length n t (c :: acc) b t' h; simp at this; omega

theorem readMany_shape {α : Type} (r : Tape → Option (α × Tape)) (Q : α → Prop)
    (hr : ∀ t a t', r t = some (a, t') → Q a) :
    ∀ (n : ℕ) (t : Tape) (as : List α) (t' : Tape), readMany r n t = some (as, t') →
      as.length = n ∧ ∀ a ∈ as, Q a
  | 0, t, as, t', h => by simp [readMany] at h; obtain ⟨rfl, -⟩ := h; simp
  | n + 1, t, as, t', h => by
    simp only [readMany] at h
    split at h
    · rename_i a t1 hrt
      obtain ⟨⟨as', t''⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨hl, hq⟩ := readMany_shape r Q hr n t1 as' t'' h1
      refine ⟨by simp [hl], ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hr _ _ _ hrt
      · exact hq b hb
    · simp at h

/-- What `readOpening` returns has the fixed shape: `depth` levels of `A - 1` 32-byte digests. -/
theorem readOpening_shape (o : OShape) (t : Tape) (leaf : List K) (path : List (List Digest))
    (t' : Tape) (h : readOpening cfg o t = some (leaf, path, t')) :
    path.length = cfg.depth o ∧ ∀ lev ∈ path, LevelOK cfg lev := by
  simp only [readOpening] at h
  split at h
  · obtain ⟨⟨ps, t''⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨-, rfl, -⟩ := h2
    exact readMany_shape _ (LevelOK cfg) (fun t lev t' hlev =>
      readMany_shape _ (fun d : Digest => d.length = 32)
        (fun t d t' hd => by simpa using takeN_length 32 t [] d t' hd) _ t lev t' hlev) _ _ _ _ h1
  · simp at h

/-- **Merkle binding at a fixed depth, without a leaf/node tag (S3-A2).** Two openings that
`runQ` would accept for the same oracle shape, root and leaf position (read from any two tapes)
carry the same leaf, unless the configured hash has a collision. -/
theorem opening_binding (o : OShape) (r : Digest) (l : ℕ) (t u t' u' : Tape)
    (leaf leaf' : List K) (path path' : List (List Digest))
    (h1 : readOpening cfg o t = some (leaf, path, t'))
    (h2 : readOpening cfg o u = some (leaf', path', u'))
    (v1 : verifyPath cfg r l leaf path = true) (v2 : verifyPath cfg r l leaf' path' = true) :
    leaf = leaf' ∨ Collision cfg := by
  obtain ⟨hl1, hp1⟩ := readOpening_shape cfg o t leaf path t' h1
  obtain ⟨hl2, hp2⟩ := readOpening_shape cfg o u leaf' path' u' h2
  exact verifyPath_binding cfg r l leaf leaf' path path' (hl1.trans hl2.symm) hp1 hp2 v1 v2

end Binding

end RecursionFast

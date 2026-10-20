/-
# Exploration P3: a Merkle-commitment verifier in the two-channel model             (UNTRUSTED)

Probe P3, item 2 (`docs/explore/notes/P3-two-channel-lean.md`). A toy argument with the shape of
a hash-based IOP's query phase: commit with public BLAKE2s, draw a position from the secret
oracle, open it.

**The toy.** A statement `c` is a Merkle root over two leaves: leaf hashes
`leafH d = BLAKE2s(0x6C ‖ d)`, root `root d₀ d₁ = BLAKE2s(0x6E ‖ leafH d₀ ‖ leafH d₁)`. The
relation `MRel c (d₀, d₁)`: `c = root d₀ d₁` and both leaves are good (first byte zero). A
witness is a BLAKE2s preimage, so an efficient extractor cannot compute it from `c`; the natural
one reads it off the log. (A noncomputable choice extractor inverts BLAKE2s for free:
`Backdoor.kstate_of_total`.) `V c π` squeezes the secret oracle on `0x73 ‖ c`, reads the position `pos a` from
the low bit of the answer, and checks the opening `π = (d, s)`, the leaf and its sibling's hash,
**with `pub` queries**: `BLAKE2s(0x6C ‖ d) = h`, `BLAKE2s(0x6E ‖ h, s in position order) = c`,
`d` good. Knowledge error `1/2`: a tree with one good leaf is accepted on half the answers.

**Results (kernel).**
* `merkleState`: a `KState2` with escapes `colLate` at `ε = 1/2` for the natural extractor `E`,
  which decodes the tree under `c` from the first logged preimages (`treeWit`) or else searches
  the log for an escape. Its potential is `1` exactly when some squeeze was answered with a
  position that was known-good while the other was not (`bad`), for the log before the squeeze.
  **`pubStep` holds in the strong form, with equality** (`merkleState_pubStep`). `final`
  (`merkle_final`) is the content: an opening accepted after a squeeze either goes through the
  tree the log knew at the squeeze (both leaves known, extracted), or one of its two evaluations
  contradicts the log (a second preimage of `c` or of the leaf hash: `Esc.col`), or produces a
  digest that was used before any evaluation produced it (`c` itself, used in the squeeze, or the
  leaf hash, used in the root's input: `Esc.late`).
* `col_no_kstate`: with collisions as the only escape (W1 §7.1's `final`) there is **no** state
  at any `ε < 1`, even with the fallback `pubStep`, for the natural extractor, given three
  inequalities between BLAKE2s values (`col_no_kstate_blake2s` checks them in the kernel for two
  concrete leaves). The adversary squeezes on an honest root it has not logged, then logs the
  opened leaf and the root: `V` accepts, the other leaf is in no entry, the log has no collision.
  `col_extractor_inverts`: every extractor of such a state returns, on one of these logs, a
  Merkle preimage of `c` whose unopened leaf hash is a preimage absent from the log, or a BLAKE2s
  collision outside the log.
* `pure_no_kstate`: the same Merkle check with the hashing done **outside** the `pub` channel
  (`Vpure`, W1 §7.1's literal reading: `runLog` reads only `sec` entries) has no state for the
  natural extractor in either mode at any `ε < 1`; `pure_extractor_inverts`: every extractor
  returns a Merkle preimage from a log holding only the squeeze.
* Non-vacuity: `complete` (the honest prover is accepted under every secret oracle);
  `honest_accepts`, `honest_extracts` (on the honest prover's log, which evaluates the tree before
  the squeeze, `V` accepts and `E` returns a witness, not an escape, given two BLAKE2s
  inequalities; `honest_extracts_blake2s` for concrete leaves); **`merkle_eps_ge`**: the error
  `1/2` is tight, every state for the natural extractor has `ε ≥ 1/2` (a committed tree with one
  good and one bad leaf, all evaluated before the squeeze, is accepted on half the answers with
  no witness and no escape).

**What is BLAKE2s-specific.** The positive results (`merkleState`, `merkle_final`) and the
general negatives (`col_no_kstate`, `pure_no_kstate`) never unfold `blake2sDigest`. Four
theorems evaluate it in the kernel (`decide +kernel`): `kat` (three inequalities between two leaf
hashes and their root) and `kat_h0`, `kat_hb`, `kat_c` (three digests against `hashlib` values),
used by `col_no_kstate_blake2s`, `honest_extracts_blake2s` and `merkle_eps_ge`. They take about
12 of the file's 20 seconds.
-/
import RecursionFast.Explore.TwoChannel.Model

open scoped NNReal

namespace RecursionFast.Explore.TwoChannel.Merkle
open RecursionFast RecursionFast.Explore.TwoChannel

/-! ## The commitment -/

/-- Domain tag of a leaf hash's input. -/
def tagML : UInt8 := 0x6C

/-- Domain tag of a root's input. -/
def tagMN : UInt8 := 0x6E

/-- Domain tag of the squeeze. -/
def tagSq : UInt8 := 0x73

/-- The bytes hashed for the leaf `d`. -/
def leafIn (d : Digest) : List UInt8 := tagML :: d.toList

/-- The bytes hashed for a node with children `x`, `y`. -/
def nodeIn (x y : Digest) : List UInt8 := tagMN :: (x.toList ++ y.toList)

/-- The leaf hash of `d`. -/
def leafH (d : Digest) : Digest := blake2sDigest (leafIn d)

/-- The Merkle root of the two leaves `d₀`, `d₁`. -/
def root (d₀ d₁ : Digest) : Digest := blake2sDigest (nodeIn (leafH d₀) (leafH d₁))

/-- A good leaf: its first byte is zero. -/
def good (d : Digest) : Prop := d[0] = 0

instance : DecidablePred good := fun d => inferInstanceAs (Decidable (d[0] = 0))

/-- **The relation**: `c` is the Merkle root of two good leaves. -/
def MRel (c : Digest) (w : Digest × Digest) : Prop := root w.1 w.2 = c ∧ good w.1 ∧ good w.2

/-- The squeeze query for the statement `c`. -/
def sqQ (c : Digest) : List UInt8 := tagSq :: c.toList

/-- The position a secret answer selects: its first byte's low bit (`true` is the right leaf). -/
def pos (a : Digest) : Bool := a[0].toNat % 2 == 1

/-- An opening: the opened leaf and its sibling's leaf hash. -/
structure Opening where
  /-- The opened leaf. -/
  d : Digest
  /-- The sibling's leaf hash. -/
  s : Digest
  deriving DecidableEq

/-- The root's input with the leaf hash `h` at position `i` and the sibling hash `s` at the
other. -/
def nodeAt (i : Bool) (h s : Digest) : List UInt8 := if i then nodeIn s h else nodeIn h s

/-- **The verifier**: squeeze on `c`, then check the opening at the selected position with
BLAKE2s evaluations on the public channel. -/
def V (c : Digest) (π : Opening) : TProg Bool :=
  .sec (sqQ c) fun a =>
    .pub (leafIn π.d) fun h =>
      .pub (nodeAt (pos a) h π.s) fun r =>
        .ret (decide (r = c) && decide (good π.d))

/-- **The same check with BLAKE2s evaluated outside the public channel**: the log records only
the squeeze. -/
def Vpure (c : Digest) (π : Opening) : TProg Bool :=
  .sec (sqQ c) fun a =>
    .ret (decide (blake2sDigest (nodeAt (pos a) (leafH π.d) π.s) = c) && decide (good π.d))

/-- The honest prover: hash the leaves and the root on the public channel, squeeze, open. -/
def P (c : Digest) (w : Digest × Digest) : TProg Opening :=
  .pub (leafIn w.1) fun h₀ => .pub (leafIn w.2) fun h₁ => .pub (nodeIn h₀ h₁) fun _ =>
    .sec (sqQ c) fun a => .ret (if pos a then ⟨w.2, h₀⟩ else ⟨w.1, h₁⟩)

/-- **Completeness** under every secret oracle. -/
theorem complete (O : List UInt8 → Digest) {c : Digest} {w : Digest × Digest} (hw : MRel c w) :
    (V c ((P c w).run O)).run O = true := by
  obtain ⟨rfl, h₁, h₂⟩ := hw
  simp only [P, V, TProg.run]
  cases pos (O (sqQ (root w.1 w.2))) <;> simp [nodeAt, root, leafH, h₁, h₂]

/-- The verifier's decision read from a log. -/
theorem runLog_V {L : Log2} {c : Digest} {π : Opening} :
    (V c π).runLog L = some true ↔ ∃ a h, secAns L (sqQ c) = some a ∧
      pubAns L (leafIn π.d) = some h ∧ pubAns L (nodeAt (pos a) h π.s) = some c ∧ good π.d := by
  simp only [V, TProg.runLog, Option.bind_eq_some_iff, Option.some.injEq, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, h, hh, r, hr, rfl, hg⟩; exact ⟨a, h, ha, hh, hr, hg⟩
  · rintro ⟨a, h, ha, hh, hr, hg⟩; exact ⟨a, ha, h, hh, c, hr, rfl, hg⟩

/-! ## Decoding the log -/

/-- The digest whose bytes are `l`, if `l` has 32 bytes. -/
def ofList? (l : List UInt8) : Option Digest :=
  if h : l.length = 32 then some ⟨l.toArray, by simpa using h⟩ else none

theorem ofList?_toList (d : Digest) : ofList? d.toList = some d := by
  simp [ofList?, Vector.toList]

theorem toList_of_ofList? {l : List UInt8} {d : Digest} (h : ofList? l = some d) : d.toList = l := by
  unfold ofList? at h; split_ifs at h; cases h; simp

/-- The leaf a leaf hash's input encodes. -/
def parseLeaf : List UInt8 → Option Digest
  | t :: r => if t = tagML then ofList? r else none
  | [] => none

/-- The two children a node's input encodes. -/
def parseNode : List UInt8 → Option (Digest × Digest)
  | t :: r =>
    if t = tagMN then (ofList? (r.take 32)).bind fun x => (ofList? (r.drop 32)).map fun y => (x, y)
    else none
  | [] => none

theorem parseLeaf_leafIn (d : Digest) : parseLeaf (leafIn d) = some d := by
  simp [parseLeaf, leafIn, ofList?_toList]

theorem eq_of_parseLeaf {m : List UInt8} {d : Digest} (h : parseLeaf m = some d) :
    m = leafIn d := by
  match m, h with
  | t :: r, h =>
    simp only [parseLeaf] at h
    split_ifs at h with ht
    rw [leafIn, ht, toList_of_ofList? h]

theorem parseNode_nodeIn (x y : Digest) : parseNode (nodeIn x y) = some (x, y) := by
  simp [parseNode, nodeIn, ofList?_toList]

theorem eq_of_parseNode {m : List UInt8} {x y : Digest} (h : parseNode m = some (x, y)) :
    m = nodeIn x y := by
  match m, h with
  | t :: r, h =>
    simp only [parseNode] at h
    split_ifs at h with ht
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y', hy, h⟩ := Option.map_eq_some_iff.mp h
    cases h
    rw [nodeIn, ht, toList_of_ofList? hx, toList_of_ofList? hy, List.take_append_drop]

theorem nodeIn_inj {x y x' y' : Digest} (h : nodeIn x y = nodeIn x' y') : x = x' ∧ y = y' := by
  have := parseNode_nodeIn x y; rw [h, parseNode_nodeIn] at this; simpa [eq_comm] using this

theorem leafIn_inj {d d' : Digest} : leafIn d = leafIn d' ↔ d = d' := by
  simp [leafIn, Vector.toList_inj]

theorem leafIn_ne_nodeIn (d x y : Digest) : leafIn d ≠ nodeIn x y := by
  simp [leafIn, nodeIn, tagML, tagMN]

/-- The child at position `i`. -/
def sel (i : Bool) (xy : Digest × Digest) : Digest := if i then xy.2 else xy.1

theorem parseNode_nodeAt (i : Bool) (h s : Digest) :
    (parseNode (nodeAt i h s)).map (sel i) = some h := by
  cases i <;> simp [nodeAt, parseNode_nodeIn, sel]

/-- The leaf at position `i` of the tree under `c`, as the log knows it: the first preimage of
`c`, decoded as a node, then the first preimage of its `i`-th child, decoded as a leaf. -/
def leafAt (L : Log2) (c : Digest) (i : Bool) : Option Digest :=
  (pre L c).bind fun m => (parseNode m).bind fun xy => (pre L (sel i xy)).bind parseLeaf

/-- Position `i` of the tree under `c` is **known-good** in the log: its leaf is known and good. -/
def KG (L : Log2) (c : Digest) (i : Bool) : Prop := ∃ d, leafAt L c i = some d ∧ good d

/-- **The tree under `c` decoded from the log**, if both leaves are known and good. -/
def treeWit (L : Log2) (c : Digest) : Option (Digest × Digest) :=
  (leafAt L c false).bind fun d₀ => (leafAt L c true).bind fun d₁ =>
    if good d₀ ∧ good d₁ then some (d₀, d₁) else none

/-- **The natural extractor**: the decoded tree, or else an escape found in the log. -/
def E (mode : Mode) (c : Digest) (_ : Opening) (L : Log2) : Option ((Digest × Digest) ⊕ Esc) :=
  match treeWit L c with
  | some w => some (.inl w)
  | none => (escSearch mode L).map .inr

/-- What a prefix knows of the tree, the whole log knows. -/
theorem leafAt_append {A B : Log2} {c : Digest} {i : Bool} {d : Digest}
    (h : leafAt A c i = some d) : leafAt (A ++ B) c i = some d := by
  obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨xy, hxy, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨m', hm', h⟩ := Option.bind_eq_some_iff.mp h
  simp [leafAt, pre_append hm, hxy, pre_append hm', h]

theorem leafAt_of_pre {L : Log2} {c : Digest} {i : Bool} {h s : Digest}
    (hc : pre L c = some (nodeAt i h s)) : leafAt L c i = (pre L h).bind parseLeaf := by
  have := parseNode_nodeAt i h s
  obtain ⟨xy, hxy, hs⟩ := Option.map_eq_some_iff.mp this
  simp [leafAt, hc, hxy, hs]

/-- **The decoded tree is a witness** on a consistent log. -/
theorem treeWit_sound {L : Log2} (hL : pubConsistent L) {c : Digest} {w : Digest × Digest}
    (h : treeWit L c = some w) : MRel c w := by
  obtain ⟨d₀, h₀, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨d₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h with hg
  cases h
  obtain ⟨m, hm, h₀⟩ := Option.bind_eq_some_iff.mp h₀
  obtain ⟨⟨x, y⟩, hxy, h₀⟩ := Option.bind_eq_some_iff.mp h₀
  obtain ⟨mx, hmx, h₀⟩ := Option.bind_eq_some_iff.mp h₀
  simp only [leafAt, hm, hxy, Option.bind_some] at h₁
  obtain ⟨my, hmy, h₁⟩ := Option.bind_eq_some_iff.mp h₁
  simp only [sel, Bool.false_eq_true, ite_false, ite_true] at hmx hmy
  have ex : x = leafH d₀ := by rw [hL _ _ (pre_mem hmx), eq_of_parseLeaf h₀, leafH]
  have ey : y = leafH d₁ := by rw [hL _ _ (pre_mem hmy), eq_of_parseLeaf h₁, leafH]
  refine ⟨?_, hg⟩
  rw [hL _ _ (pre_mem hm), eq_of_parseNode hxy, root, ex, ey]

/-- Both positions known-good: the tree is decoded. -/
theorem treeWit_of_KG {L : Log2} {c : Digest} (h₀ : KG L c false) (h₁ : KG L c true) :
    ∃ w, treeWit L c = some w := by
  obtain ⟨d₀, hd₀, g₀⟩ := h₀
  obtain ⟨d₁, hd₁, g₁⟩ := h₁
  exact ⟨(d₀, d₁), by simp [treeWit, hd₀, hd₁, g₀, g₁]⟩

/-! ## The potential -/

/-- **A bad answer** to the squeeze on `c`: it selects a known-good position while the other is
not known-good. -/
def bad (L : Log2) (q : List UInt8) (a : Digest) : Prop :=
  ∃ c, q = sqQ c ∧ KG L c (pos a) ∧ ¬ KG L c (!pos a)

theorem sqQ_inj {c c' : Digest} (h : sqQ c = sqQ c') : c = c' :=
  Vector.toList_inj.mp (by simpa [sqQ] using h)

theorem card_fin (b : Bool) : Fintype.card {x : Fin 256 // (x.val % 2 == 1) = b} = 128 := by
  cases b <;> decide +kernel

/-- Half the answers select each position. -/
theorem card_pos (b : Bool) : Fintype.card {a : Digest // pos a = b} = 2 ^ 255 := by
  let Q : Fin 256 → Prop := fun x => (x.val % 2 == 1) = b
  have e : {a : Digest // pos a = b} ≃ {x : Fin 256 // Q x} × (Fin 31 → Fin 256) :=
    (digestEquiv.subtypeEquiv (q := fun f => Q (f 0)) fun a => by
      simp [Q, pos, digestEquiv]).trans
    (((Fin.consEquiv fun _ => Fin 256).symm.subtypeEquiv (q := fun p => Q p.1) fun f => by
      simp [Fin.consEquiv]).trans Equiv.prodSubtypeFstEquivSubtypeProd)
  rw [Fintype.card_congr e, Fintype.card_prod, card_fin]
  simp

/-- A set of answers that all select the same position has at most `2^255` elements. -/
theorem card_le_of_pos {S : Digest → Prop} [DecidablePred S] (b : Bool)
    (h : ∀ a, S a → pos a = b) : ((Finset.univ.filter S).card : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹ * 2 ^ 256 := by
  have hle : (Finset.univ.filter S).card ≤ 2 ^ 255 := by
    rw [← Fintype.card_subtype, ← card_pos b]
    exact Fintype.card_subtype_mono _ _ h
  calc ((Finset.univ.filter S).card : ℝ≥0) ≤ ((2 ^ 255 : ℕ) : ℝ≥0) := Nat.cast_le.mpr hle
    _ = (2 : ℝ≥0) ^ 255 := by rw [Nat.cast_pow, Nat.cast_ofNat]
    _ = (2 : ℝ≥0)⁻¹ * 2 ^ 256 := by
      rw [pow_succ' 2 255, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]

/-- **At most half the answers to any query are bad.** -/
theorem card_bad (L : Log2) (q : List UInt8) [DecidablePred (bad L q)] :
    ((Finset.univ.filter (bad L q)).card : ℝ≥0) ≤ (2 : ℝ≥0)⁻¹ * 2 ^ 256 := by
  by_cases hq : ∃ c, q = sqQ c
  · obtain ⟨c, rfl⟩ := hq
    by_cases hk : KG L c true
    · refine card_le_of_pos true fun a ⟨c', hc', h1, h2⟩ => ?_
      cases sqQ_inj hc'
      cases hp : pos a <;> simp_all
    · refine card_le_of_pos false fun a ⟨c', hc', h1, h2⟩ => ?_
      cases sqQ_inj hc'
      cases hp : pos a <;> simp_all
  · have : Finset.univ.filter (bad L q) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun a _ ⟨c, hc, _⟩ => hq ⟨c, hc⟩
    simp [this]

/-- An entry of `A ++ e :: B` that is neither in `A` nor `e` is in `B`. -/
theorem mem_right {A B : Log2} {e x : Entry} (h : x ∈ A ++ e :: B) (hA : x ∉ A) (he : x ≠ e) :
    x ∈ B := by
  simp only [List.mem_append, List.mem_cons] at h
  tauto

/-- **`final` for the Merkle verifier**: on a consistent log with no bad squeeze, an accepted
opening is extracted, or the log contains a collision or a late preimage. -/
theorem merkle_final {L : Log2} {c : Digest} {π : Opening} (hL : pubConsistent L)
    (hg : ¬ BadLog bad L) (hacc : (V c π).runLog L = some true) :
    ∃ o, E .colLate c π L = some o ∧ Valid .colLate MRel c L o := by
  obtain ⟨a, h, ha, hh, hr, hgood⟩ := runLog_V.mp hacc
  cases htw : treeWit L c with
  | some w => exact ⟨.inl w, by simp [E, htw], treeWit_sound hL htw⟩
  | none =>
  suffices ∃ e, EscValid .colLate L e by
    obtain ⟨e, he⟩ := this
    obtain ⟨e', he'⟩ := escSearch_complete he
    exact ⟨.inr e', by simp [E, htw, he'], escSearch_sound he'⟩
  have m₁ := pubAns_mem hh
  have m₂ := pubAns_mem hr
  have eh : h = leafH π.d := hL _ _ m₁
  obtain ⟨A, B, rfl⟩ := secAns_split ha
  -- At the squeeze, the selected position was not known-good.
  have hKG : ¬ KG A c (pos a) := by
    intro hk
    by_cases hk' : KG A c (!pos a)
    · have h01 : KG A c false ∧ KG A c true := by cases hp : pos a <;> simp_all
      obtain ⟨w, hw⟩ := treeWit_of_KG h01.1 h01.2
      obtain ⟨d₀, hd₀, g₀⟩ := h01.1
      obtain ⟨d₁, hd₁, g₁⟩ := h01.2
      simp [treeWit, leafAt_append hd₀, leafAt_append hd₁, g₀, g₁] at htw
    · exact hg ⟨A, _, a, B, rfl, c, rfl, hk, hk'⟩
  cases hpc : pre A c with
  | none =>
    -- `c` was used in the squeeze before any evaluation produced it.
    refine ⟨_, late_valid (e := .sec (sqQ c) a) ?_ (pre_eq_none.mp hpc) (by simp [Entry.out])
      (mem_right m₂ (fun hx => pre_eq_none.mp hpc _ hx rfl) (by simp))⟩
    exact (List.suffix_cons _ _).isInfix
  | some m₀ =>
    have hpcL := pre_append (B := .sec (sqQ c) a :: B) hpc
    by_cases hm : m₀ = nodeAt (pos a) h π.s
    · subst hm
      unfold KG at hKG
      rw [leafAt_of_pre hpc] at hKG
      cases hph : pre A h with
      | none =>
        -- The leaf hash `h` was used in the root's input before any evaluation produced it.
        obtain ⟨A₁, A₂, rfl, -⟩ := pre_split hpc
        have hA := pre_eq_none.mp hph
        have hne : c ≠ h := fun hch =>
          hA (.pub (nodeAt (pos a) h π.s) c) (by simp) (by simp [Entry.out, hch])
        refine ⟨.late A₁.length (leafIn π.d) h, ?_⟩
        rw [List.append_assoc, List.cons_append]
        refine late_valid ?_ (fun x hx => hA x (by simp [hx])) (by simp [Entry.out, hne]) ?_
        · cases pos a
          · exact (List.prefix_append _ _).isInfix.trans (List.infix_cons (List.infix_refl _))
          · exact (List.suffix_append _ _).isInfix.trans (List.infix_cons (List.infix_refl _))
        · rw [List.append_assoc, List.cons_append] at m₁
          exact mem_right m₁ (fun hx => hA (.pub (leafIn π.d) h) (by simp [hx]) rfl)
            (by simp [hne.symm])
      | some m₁' =>
        by_cases hm' : m₁' = leafIn π.d
        · subst hm'
          exact absurd ⟨π.d, by simp [hph, parseLeaf_leafIn], hgood⟩ hKG
        · exact ⟨.col m₁' (leafIn π.d) h, hm', pre_mem (pre_append hph), m₁⟩
    · exact ⟨.col m₀ (nodeAt (pos a) h π.s) c, hm, pre_mem hpcL, m₂⟩

/-- **The Merkle verifier's two-channel knowledge state**, at `ε = 1/2` with both escapes. -/
noncomputable def merkleState : KState2 .colLate MRel V (E .colLate) (2 : ℝ≥0)⁻¹ :=
  open Classical in
  KState2.ofHist bad (fun L q => card_bad L q) fun _ _ _ hL hg h => merkle_final hL hg h

/-- **`pubStep` holds in the strong form, with equality.** -/
theorem merkleState_pubStep (L : Log2) (m : List UInt8) (a : Digest) :
    merkleState.μ (L ++ [.pub m a]) = merkleState.μ L :=
  ofHist_pub L m a

/-! ## Non-vacuity: the honest log -/

section Honest
variable (d₀ d₁ : Digest)

/-- The honest prover's log for the tree `(d₀, d₁)` and the squeeze answer `a`: the two leaf
hashes and the root, evaluated before the squeeze. -/
def honestLog (a : Digest) : Log2 :=
  [.pub (leafIn d₀) (leafH d₀), .pub (leafIn d₁) (leafH d₁),
    .pub (nodeIn (leafH d₀) (leafH d₁)) (root d₀ d₁), .sec (sqQ (root d₀ d₁)) a]

/-- The honest opening for the squeeze answer `a`. -/
def honestOpen (a : Digest) : Opening :=
  if pos a then ⟨d₁, leafH d₀⟩ else ⟨d₀, leafH d₁⟩

variable {d₀ d₁}

theorem honestLog_consistent (a : Digest) : pubConsistent (honestLog d₀ d₁ a) := by
  intro m b hm
  simp only [honestLog, List.mem_cons, Entry.pub.injEq, reduceCtorEq, or_false,
    List.not_mem_nil] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- **On the honest log `V` accepts the honest opening.** -/
theorem honest_accepts (hg₀ : good d₀) (hg₁ : good d₁) (a : Digest) :
    (V (root d₀ d₁) (honestOpen d₀ d₁ a)).runLog (honestLog d₀ d₁ a) = some true := by
  rw [runLog_V]
  have hn : ∀ d, leafIn d ≠ nodeIn (leafH d₀) (leafH d₁) := fun d => leafIn_ne_nodeIn _ _ _
  cases hp : pos a
  · refine ⟨a, leafH d₀, ?_, ?_, ?_, ?_⟩ <;>
      simp [secAns, pubAns, honestLog, honestOpen, hp, secPick, pubPick, nodeAt, hn, hg₀,
        List.findSome?_cons]
  · refine ⟨a, leafH d₁, ?_, ?_, ?_, ?_⟩ <;>
      simp [secAns, pubAns, honestLog, honestOpen, hp, secPick, pubPick, nodeAt, hn, hg₁,
        List.findSome?_cons, leafIn_inj]
    by_cases h : d₀ = d₁ <;> simp [h]

/-- **On the honest log the extractor returns a witness, not an escape**, unless a leaf hash
equals the root (a BLAKE2s coincidence). -/
theorem honest_extracts (h0c : leafH d₀ ≠ root d₀ d₁) (h1c : leafH d₁ ≠ root d₀ d₁)
    (hg₀ : good d₀) (hg₁ : good d₁) (mode : Mode) (π : Opening) (a : Digest) :
    ∃ w, E mode (root d₀ d₁) π (honestLog d₀ d₁ a) = some (.inl w) := by
  have hc : pre (honestLog d₀ d₁ a) (root d₀ d₁) = some (nodeIn (leafH d₀) (leafH d₁)) := by
    simp [pre, honestLog, prePick, h0c, h1c]
  have h0 : leafAt (honestLog d₀ d₁ a) (root d₀ d₁) false = some d₀ := by
    rw [leafAt, hc]
    simp [parseNode_nodeIn, sel, pre, honestLog, prePick, parseLeaf_leafIn, List.findSome?_cons]
  by_cases h01 : leafH d₀ = leafH d₁
  · have h1 : leafAt (honestLog d₀ d₁ a) (root d₀ d₁) true = some d₀ := by
      rw [leafAt, hc]
      simp [parseNode_nodeIn, sel, pre, honestLog, prePick, parseLeaf_leafIn, h01,
        List.findSome?_cons]
    exact ⟨(d₀, d₀), by simp [E, treeWit, h0, h1, hg₀]⟩
  · have h1 : leafAt (honestLog d₀ d₁ a) (root d₀ d₁) true = some d₁ := by
      rw [leafAt, hc]
      simp [parseNode_nodeIn, sel, pre, honestLog, prePick, parseLeaf_leafIn, h01,
        List.findSome?_cons]
    exact ⟨(d₀, d₁), by simp [E, treeWit, h0, h1, hg₀, hg₁]⟩

end Honest

/-! ## Collisions alone are not enough (W1 §7.1's `final`) -/

section Late
variable (d₀ d₁ : Digest)

/-- The leaf at position `i`. -/
def dAt (i : Bool) : Digest := if i then d₁ else d₀

/-- What the adversary evaluates **after** squeezing on `root d₀ d₁`, having evaluated nothing
before: the selected leaf's hash and the root. -/
def lateTail (a : Digest) : Log2 :=
  [.pub (leafIn (dAt d₀ d₁ (pos a))) (leafH (dAt d₀ d₁ (pos a))),
    .pub (nodeIn (leafH d₀) (leafH d₁)) (root d₀ d₁)]

/-- The opening at the selected position. -/
def lateOpen (a : Digest) : Opening := ⟨dAt d₀ d₁ (pos a), leafH (dAt d₀ d₁ (!pos a))⟩

theorem nodeAt_dAt (i : Bool) :
    nodeAt i (leafH (dAt d₀ d₁ i)) (leafH (dAt d₀ d₁ (!i))) = nodeIn (leafH d₀) (leafH d₁) := by
  cases i <;> rfl

theorem lateTail_pub (a : Digest) : PubTail (lateTail d₀ d₁ a) := by
  intro x hx
  simp only [lateTail, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  exacts [⟨_, rfl⟩, ⟨_, rfl⟩]

variable {d₀ d₁}

theorem late_accepts (hg₀ : good d₀) (hg₁ : good d₁) (a : Digest) :
    (V (root d₀ d₁) (lateOpen d₀ d₁ a)).runLog (.sec (sqQ (root d₀ d₁)) a :: lateTail d₀ d₁ a) =
      some true := by
  rw [runLog_V]
  refine ⟨a, leafH (dAt d₀ d₁ (pos a)), ?_, ?_, ?_, ?_⟩
  · simp [secAns, secPick]
  · simp [pubAns, lateTail, pubPick, lateOpen, List.findSome?_cons]
  · rw [show (lateOpen d₀ d₁ a).s = leafH (dAt d₀ d₁ (!pos a)) from rfl, nodeAt_dAt]
    simp [pubAns, lateTail, pubPick, leafIn_ne_nodeIn, List.findSome?_cons]
  · by_cases hp : pos a <;> simp [lateOpen, dAt, hp, hg₀, hg₁]

theorem leafH_dAt_ne (h0c : leafH d₀ ≠ root d₀ d₁) (h1c : leafH d₁ ≠ root d₀ d₁) (i : Bool) :
    leafH (dAt d₀ d₁ i) ≠ root d₀ d₁ := by
  cases i <;> simpa [dAt]

/-- The late log has no collision: its two evaluations have distinct outputs. -/
theorem late_noCol (h0c : leafH d₀ ≠ root d₀ d₁) (h1c : leafH d₁ ≠ root d₀ d₁) (a : Digest) :
    ¬ Collision (.sec (sqQ (root d₀ d₁)) a :: lateTail d₀ d₁ a) := by
  rintro ⟨m, m', b, hne, h1, h2⟩
  have hd := leafH_dAt_ne h0c h1c (pos a)
  simp only [lateTail, List.mem_cons, reduceCtorEq, Entry.pub.injEq, List.not_mem_nil, or_false,
    false_or] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all

theorem late_noEsc (h0c : leafH d₀ ≠ root d₀ d₁) (h1c : leafH d₁ ≠ root d₀ d₁) (a : Digest)
    (e : Esc) : ¬ EscValid .col (.sec (sqQ (root d₀ d₁)) a :: lateTail d₀ d₁ a) e := by
  cases e with
  | col m m' b => exact fun h => late_noCol h0c h1c a ⟨m, m', b, h⟩
  | late j m b => exact fun h => absurd h.1 (by decide)

/-- On the late log the tree is not decoded: the unopened leaf's hash has no logged preimage. -/
theorem late_treeWit (h01 : leafH d₀ ≠ leafH d₁) (h0c : leafH d₀ ≠ root d₀ d₁)
    (h1c : leafH d₁ ≠ root d₀ d₁) (a : Digest) :
    treeWit (.sec (sqQ (root d₀ d₁)) a :: lateTail d₀ d₁ a) (root d₀ d₁) = none := by
  have hd := leafH_dAt_ne h0c h1c (pos a)
  have hc : pre (.sec (sqQ (root d₀ d₁)) a :: lateTail d₀ d₁ a) (root d₀ d₁) =
      some (nodeIn (leafH d₀) (leafH d₁)) := by
    simp [pre, lateTail, prePick, hd, List.findSome?_cons]
  have hne : leafH (dAt d₀ d₁ (pos a)) ≠ leafH (dAt d₀ d₁ (!pos a)) := by
    cases pos a <;> simp [dAt, h01, Ne.symm h01]
  have hnc : root d₀ d₁ ≠ leafH (dAt d₀ d₁ (!pos a)) := (leafH_dAt_ne h0c h1c _).symm
  have hl : leafAt (.sec (sqQ (root d₀ d₁)) a :: lateTail d₀ d₁ a) (root d₀ d₁) (!pos a) =
      none := by
    have hs : sel (!pos a) (leafH d₀, leafH d₁) = leafH (dAt d₀ d₁ (!pos a)) := by
      cases pos a <;> rfl
    rw [leafAt, hc]
    simp [parseNode_nodeIn, hs, pre, lateTail, prePick, hne, hnc, List.findSome?_cons]
  unfold treeWit
  cases hp : pos a <;> simp_all

/-- **No collision-only state for the natural extractor**: given three BLAKE2s inequalities,
the Merkle verifier has no `KState2W .col` at any error below `1`, even with the fallback
`pubStep`. -/
theorem col_no_kstate (hg₀ : good d₀) (hg₁ : good d₁) (h01 : leafH d₀ ≠ leafH d₁)
    (h0c : leafH d₀ ≠ root d₀ d₁) (h1c : leafH d₁ ≠ root d₀ d₁) {ε : ℝ≥0} (hε : ε < 1) :
    ¬ Nonempty (KState2W .col MRel V (E .col) ε) := by
  rintro ⟨k⟩
  refine absurd (k.one_le_of_fail (L₀ := []) k.empty (by simp [pubConsistent])
    (by simp [secCount, secQueries, logCap]) (q := sqQ (root d₀ d₁)) (by simp [secQueries])
    (root d₀ d₁) (lateOpen d₀ d₁) (lateTail d₀ d₁) (lateTail_pub d₀ d₁) (late_noCol h0c h1c)
    (late_accepts hg₀ hg₁) ?_) (not_le.mpr hε)
  intro a o ho hv
  simp only [List.nil_append, E, late_treeWit h01 h0c h1c] at ho
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp ho
  exact late_noEsc h0c h1c a e (escSearch_sound he)

/-- A Merkle preimage of `root d₀ d₁` agrees with `(d₀, d₁)` on the leaf hashes, or it is a
BLAKE2s collision with the root's input. -/
theorem inverts_or_collides {w : Digest × Digest} (hw : MRel (root d₀ d₁) w) :
    (leafH w.1 = leafH d₀ ∧ leafH w.2 = leafH d₁) ∨
      (nodeIn (leafH w.1) (leafH w.2) ≠ nodeIn (leafH d₀) (leafH d₁) ∧
        blake2sDigest (nodeIn (leafH w.1) (leafH w.2)) =
          blake2sDigest (nodeIn (leafH d₀) (leafH d₁))) := by
  by_cases h : nodeIn (leafH w.1) (leafH w.2) = nodeIn (leafH d₀) (leafH d₁)
  · exact .inl (nodeIn_inj h)
  · exact .inr ⟨h, hw.1⟩

/-- **Every extractor of a collision-only state inverts BLAKE2s**: on some late log it returns a
Merkle preimage of `root d₀ d₁`, so (`inverts_or_collides`) a preimage of the unopened leaf hash,
which no entry of that log evaluates, or a collision outside the log. -/
theorem col_extractor_inverts (hg₀ : good d₀) (hg₁ : good d₁) (h0c : leafH d₀ ≠ root d₀ d₁)
    (h1c : leafH d₁ ≠ root d₀ d₁) {ε : ℝ≥0} (hε : ε < 1)
    {E' : Digest → Opening → Log2 → Option ((Digest × Digest) ⊕ Esc)}
    (k : KState2W .col MRel V E' ε) :
    ∃ a w, E' (root d₀ d₁) (lateOpen d₀ d₁ a) (.sec (sqQ (root d₀ d₁)) a :: lateTail d₀ d₁ a) =
      some (.inl w) ∧ MRel (root d₀ d₁) w := by
  obtain ⟨a, o, ho, hv⟩ := k.exists_valid (L₀ := []) hε k.empty (by simp [pubConsistent])
    (by simp [secCount, secQueries, logCap]) (q := sqQ (root d₀ d₁)) (by simp [secQueries])
    (root d₀ d₁) (lateOpen d₀ d₁) (lateTail d₀ d₁) (lateTail_pub d₀ d₁) (late_noCol h0c h1c)
    (late_accepts hg₀ hg₁)
  rcases o with w | e
  · exact ⟨a, w, ho, hv⟩
  · exact absurd hv (late_noEsc h0c h1c a e)

end Late

/-- The all-zero digest: a good leaf. -/
def z₀ : Digest := Vector.replicate 32 0

/-- A second good leaf: zero but for a final `1`. -/
def z₁ : Digest := (Vector.replicate 32 0).set 31 1

/-- **Three BLAKE2s values, computed by the kernel**: the two leaf hashes differ, and neither is
the root. -/
theorem kat : leafH z₀ ≠ leafH z₁ ∧ leafH z₀ ≠ root z₀ z₁ ∧ leafH z₁ ≠ root z₀ z₁ := by
  decide +kernel

/-- **`col_no_kstate` for BLAKE2s**: the collision-only form has no state for the Merkle
verifier with its natural extractor, at any error below `1`. -/
theorem col_no_kstate_blake2s {ε : ℝ≥0} (hε : ε < 1) :
    ¬ Nonempty (KState2W .col MRel V (E .col) ε) :=
  col_no_kstate (d₀ := z₀) (d₁ := z₁) (by decide) (by decide) kat.1 kat.2.1 kat.2.2 hε

/-! ## Hashing outside the public channel (W1 §7.1's literal `runLog`) -/

theorem pure_accepts {d₀ d₁ : Digest} (hg₀ : good d₀) (hg₁ : good d₁) (a : Digest) :
    (Vpure (root d₀ d₁) (lateOpen d₀ d₁ a)).runLog [.sec (sqQ (root d₀ d₁)) a] = some true := by
  have hn := nodeAt_dAt d₀ d₁ (pos a)
  simp only [Vpure, TProg.runLog, secAns, List.findSome?_cons, secPick, ite_true,
    Option.bind_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by rw [show (lateOpen d₀ d₁ a).d = dAt d₀ d₁ (pos a) from rfl,
      show (lateOpen d₀ d₁ a).s = leafH (dAt d₀ d₁ (!pos a)) from rfl, hn]; rfl,
    by by_cases hp : pos a <;> simp [lateOpen, dAt, hp, hg₀, hg₁]⟩

theorem pure_noEsc (mode : Mode) (q : List UInt8) (a : Digest) (e : Esc) :
    ¬ EscValid mode [.sec q a] e := by
  cases e with
  | col m m' b => simp [EscValid]
  | late j m b => simp [EscValid]

/-- **The Merkle check with hashing outside the public channel has no state** in either mode, at
any error below `1`, for the natural extractor: the log of a squeeze holds no evaluation to read
the tree from. -/
theorem pure_no_kstate (mode : Mode) {ε : ℝ≥0} (hε : ε < 1) :
    ¬ Nonempty (KState2W mode MRel Vpure (E mode) ε) := by
  rintro ⟨k⟩
  have hg : good z₀ := by decide
  refine absurd (k.one_le_of_fail (L₀ := []) k.empty (by simp [pubConsistent])
    (by simp [secCount, secQueries, logCap]) (q := sqQ (root z₀ z₀)) (by simp [secQueries])
    (root z₀ z₀) (lateOpen z₀ z₀) (fun _ => []) (fun _ => by simp [PubTail])
    (fun a ⟨m, m', b, h⟩ => pure_noEsc .col _ a _ h) (pure_accepts hg hg) ?_) (not_le.mpr hε)
  intro a o ho hv
  have ht : treeWit [.sec (sqQ (root z₀ z₀)) a] (root z₀ z₀) = none := by
    simp [treeWit, leafAt, pre, prePick]
  simp only [List.nil_append, E, ht] at ho
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp ho
  exact pure_noEsc mode _ a e (escSearch_sound he)

/-- **Every extractor for the out-of-channel check inverts BLAKE2s**: for every tree of two good
leaves it returns, on some squeeze answer, a Merkle preimage of the root from the opening (one
leaf and the other leaf's hash) and a log that holds only the squeeze. -/
theorem pure_extractor_inverts (mode : Mode) {ε : ℝ≥0} (hε : ε < 1)
    {E' : Digest → Opening → Log2 → Option ((Digest × Digest) ⊕ Esc)}
    (k : KState2W mode MRel Vpure E' ε) {d₀ d₁ : Digest} (hg₀ : good d₀) (hg₁ : good d₁) :
    ∃ a w, E' (root d₀ d₁) (lateOpen d₀ d₁ a) [.sec (sqQ (root d₀ d₁)) a] = some (.inl w) ∧
      MRel (root d₀ d₁) w := by
  obtain ⟨a, o, ho, hv⟩ := k.exists_valid (L₀ := []) hε k.empty (by simp [pubConsistent])
    (by simp [secCount, secQueries, logCap]) (q := sqQ (root d₀ d₁)) (by simp [secQueries])
    (root d₀ d₁) (lateOpen d₀ d₁) (fun _ => []) (fun _ => by simp [PubTail])
    (fun a ⟨m, m', b, h⟩ => pure_noEsc .col _ a _ h) (pure_accepts hg₀ hg₁)
  rcases o with w | e
  · exact ⟨a, w, ho, hv⟩
  · exact absurd hv (pure_noEsc mode _ a e)

/-! ## The error `1/2` is tight -/

/-- A bad leaf: first byte `1`. -/
def zb : Digest := (Vector.replicate 32 0).set 0 1

/-- `BLAKE2s(0x6C ‖ z₀)`, as `hashlib.blake2s` prints it. -/
def lit0 : Digest := ⟨#[0x77, 0x51, 0xF8, 0xED, 0xD3, 0x6C, 0x34, 0x23, 0x7D, 0x64, 0x1A, 0xFC,
  0xBA, 0x3F, 0x3C, 0x58, 0x29, 0xD8, 0x55, 0x06, 0xD8, 0xEE, 0x44, 0x73, 0x72, 0xA2, 0x33, 0x96,
  0x64, 0xC1, 0xFC, 0x8D], rfl⟩

/-- `BLAKE2s(0x6C ‖ zb)`. -/
def litb : Digest := ⟨#[0x12, 0xB4, 0x86, 0xFF, 0xD2, 0xCA, 0x02, 0x21, 0x41, 0xDC, 0x25, 0x34,
  0x3F, 0x13, 0xD1, 0xC6, 0xEE, 0x2B, 0x1B, 0x34, 0x4D, 0xC0, 0xD8, 0x6D, 0xCF, 0x0C, 0xB9, 0xF0,
  0x5B, 0x28, 0xDA, 0xA8], rfl⟩

/-- `BLAKE2s(0x6E ‖ lit0 ‖ litb)`, the root over `z₀` and `zb`. -/
def litc : Digest := ⟨#[0xCD, 0xBC, 0x70, 0x8F, 0x74, 0xC6, 0x0E, 0x6F, 0xDB, 0xB6, 0x6A, 0xF8,
  0xF0, 0xBE, 0x26, 0x2D, 0x3B, 0xD1, 0xE7, 0x15, 0xF6, 0xC5, 0x3D, 0x16, 0x39, 0xD6, 0x52, 0x34,
  0xED, 0xA6, 0x92, 0x16], rfl⟩

theorem kat_h0 : leafH z₀ = lit0 := by decide +kernel

theorem kat_hb : leafH zb = litb := by decide +kernel

theorem kat_c : blake2sDigest (nodeIn lit0 litb) = litc := by decide +kernel

/-- An honest commitment to one good and one bad leaf: both leaf hashes and the root, evaluated
before any squeeze. -/
def tightLog : Log2 :=
  [.pub (leafIn z₀) lit0, .pub (leafIn zb) litb, .pub (nodeIn lit0 litb) litc]

theorem tightLog_pub : PubTail tightLog := by
  intro x hx
  simp only [tightLog, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨_, by rw [← kat_h0]; rfl⟩
  · exact ⟨_, by rw [← kat_hb]; rfl⟩
  · exact ⟨_, by rw [kat_c]⟩

/-- The commitment's log has no escape (decided by the kernel on the literal log). -/
theorem tight_esc : escSearch .colLate tightLog = none := by decide +kernel

theorem tight_noEsc (e : Esc) : ¬ EscValid .colLate tightLog e := fun h => by
  obtain ⟨e', he'⟩ := escSearch_complete h
  rw [tight_esc] at he'
  cases he'

/-- The tree is not a witness: its right leaf is bad. -/
theorem tight_treeWit : treeWit tightLog litc = none := by decide +kernel

theorem treeWit_snoc_sec (L : Log2) (q : List UInt8) (a c : Digest) :
    treeWit (L ++ [.sec q a]) c = treeWit L c := by
  simp [treeWit, leafAt, pre_snoc_sec]

/-- After the squeeze, an answer selecting the good leaf makes `V` accept its opening. -/
theorem tight_accepts {a : Digest} (hp : pos a = false) :
    (V litc ⟨z₀, litb⟩).runLog (tightLog ++ [.sec (sqQ litc) a]) = some true := by
  rw [runLog_V]
  refine ⟨a, lit0, ?_, ?_, ?_, by decide⟩
  · simp [secAns, tightLog, secPick, List.findSome?_cons]
  · simp [pubAns, tightLog, pubPick]
  · rw [hp]
    simp [nodeAt, pubAns, tightLog, pubPick, leafIn_ne_nodeIn]

/-- **The error `1/2` is tight**: every state of the Merkle verifier for the natural extractor,
even with the fallback `pubStep`, has error at least `1/2`. The answers selecting the good leaf
of a committed (good, bad) tree are accepted with nothing to extract or escape to. -/
theorem merkle_eps_ge {ε : ℝ≥0} (k : KState2W .colLate MRel V (E .colLate) ε) :
    (2 : ℝ≥0)⁻¹ ≤ ε := by
  have hnc : ¬ Collision tightLog := fun ⟨m, m', b, h⟩ => tight_noEsc (.col m m' b) h
  have hcons : pubConsistent tightLog := by
    simpa using pubConsistent_append (L := []) (by simp [pubConsistent]) tightLog_pub
  have h0 : k.μ tightLog = 0 := by
    have := k.le_of_pubTail (L := []) (T := tightLog) (by simp [pubConsistent]) tightLog_pub
      (by simpa using hnc)
    rw [List.nil_append, k.empty] at this
    exact le_antisymm this zero_le
  have hlen : secCount tightLog < logCap := by
    rw [show secCount tightLog = 0 from rfl]; exact Nat.pos_of_ne_zero (by simp [logCap])
  have hc := k.card_le h0 hcons hlen (q := sqQ litc) (by simp [tightLog, secQueries, secQ])
    (fun a => pos a = false) fun a hp => by
      by_contra hlt
      obtain ⟨o, ho, hv⟩ := k.final_tail (T := []) hcons hlen (by simp [PubTail])
        (fun ⟨m, m', b, h⟩ => hnc ⟨m, m', b, EscValid.of_snoc_sec h⟩) (not_le.mp hlt)
        (tight_accepts hp)
      simp only [E, treeWit_snoc_sec, tight_treeWit] at ho
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp ho
      exact tight_noEsc e (EscValid.of_snoc_sec (escSearch_sound he))
  rw [← Fintype.card_subtype, card_pos, Nat.cast_pow, Nat.cast_ofNat,
    show (2 : ℝ≥0) ^ 255 = 2⁻¹ * 2 ^ 256 by
      rw [pow_succ' 2 255, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]] at hc
  exact le_of_mul_le_mul_right hc (by positivity)

/-- `honest_extracts` for the two concrete leaves. -/
theorem honest_extracts_blake2s (mode : Mode) (π : Opening) (a : Digest) :
    ∃ w, E mode (root z₀ z₁) π (honestLog z₀ z₁ a) = some (.inl w) :=
  honest_extracts kat.2.1 kat.2.2 (by decide) (by decide) mode π a

end RecursionFast.Explore.TwoChannel.Merkle

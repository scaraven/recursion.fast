/-
# Exploration: witness-sending systems for the lift                               (UNTRUSTED)

Probe P4. Two `WSys` instances for `Lift/Basic.lean`'s lift.

* **The library's witness-sending format** (`wsSys`): `WitnessSending.check` and `decode` from
  `Library/WitnessSending.lean`, unchanged, with `wsProof t` the library encoding of the shape `t`
  (each node the canonical `encode` of its two children's statements and proofs). `check` bounds
  every child proof by `proofCap = 2^20` bytes, so the format sends only shapes whose sub-proofs
  fit (`WSFits`). A shape's proof has `136 · #leaves − 88` bytes (`size_wsProof`), so every shape
  of at most `7711` leaves fits (`wsFits_of_length_le`), a shape with a child of more than `7710`
  leaves does not (`not_wsFits`), and the lift over this format covers a flat shape whose halves
  have at most `7711` leaves each (`halvesFit_of_small`). For the perfect shapes of `Lift/Tree.lean`
  that is depth at most `14` (`2^14` leaves).
* **A cap-free witness-sending format** (`freeSys D`): the same decision (`freeChk`: a leaf
  witness of the leaf clause, or a node witness with accepted children, recursively) over P1's
  abstract `Codec` with no size cap; every shape fits (`freeSys_halvesFit`), so the lift over it
  has no side condition at all (`lift_free`). `Codec.unary` gives one (`witCodec`).
-/
import RecursionFast.Explore.Lift.Basic
import RecursionFast.Library.WitnessSending
import Mathlib.Tactic.DeriveCountable

open scoped NNReal

namespace RecursionFast.Explore.Lift
open Relativized

/-! ## Shapes -/

theorem length_leaves_pos : ∀ t : Shape, 0 < t.leaves.length
  | .leaf _ _ => by simp [Shape.leaves]
  | .node l r => by simp only [Shape.leaves, List.length_append]; have := length_leaves_pos l; omega

theorem mem_leaves_left {l r : Shape} {x : Digest × ℕ} (h : x ∈ l.leaves) :
    x ∈ (Shape.node l r).leaves := List.mem_append_left _ h

theorem mem_leaves_right {l r : Shape} {x : Digest × ℕ} (h : x ∈ r.leaves) :
    x ∈ (Shape.node l r).leaves := List.mem_append_right _ h

/-! ## The library's witness-sending format -/

/-- The library's witness-sending proof of a shape: a leaf's `encode (leaf s n)`; a node's
canonical `encode` of its children's statements and proofs. -/
def wsProof : Shape → Proof
  | .leaf s n => WitnessSending.encode (.leaf s n)
  | .node l r => WitnessSending.encode (.node l.root r.root (wsProof l) (wsProof r))

/-- The shapes the library's format can send: every child proof within `proofCap`. -/
def WSFits : Shape → Prop
  | .leaf _ _ => True
  | .node l r => (wsProof l).size ≤ proofCap ∧ (wsProof r).size ≤ proofCap ∧ WSFits l ∧ WSFits r

/-- **The library's check accepts the proof of every fitting flat shape** for its root. -/
theorem check_wsProof : ∀ {t : Shape}, WSFits t → (∀ x ∈ t.leaves, x.2 ≤ chainCap) →
    WitnessSending.check t.root (wsProof t) = true
  | .leaf s n, _, h => by
    have hn := h (s, n) (List.mem_singleton_self _)
    exact WitnessSending.check_encode ⟨hn, rfl⟩ (hn.trans_lt (by decide))
  | .node l r, ⟨hl, hr, fl, fr⟩, h => by
    have h₁ := check_wsProof fl fun x hx => h x (mem_leaves_left hx)
    have h₂ := check_wsProof fr fun x hx => h x (mem_leaves_right hx)
    refine WitnessSending.check_encode ⟨rfl, ?_, ?_⟩ ⟨hl, hr⟩ <;>
      simp [WitnessSending.Vb_eq, *]

/-- An accepted library proof sends a witness whose children `check` accepts. -/
theorem ws_sound {c : Digest} {π : Proof} (h : WitnessSending.check c π = true) :
    ∃ w, WitnessSending.decode π = some w ∧
      RelWith (fun c π => WitnessSending.check c π = true) c w := by
  obtain ⟨w, hd, hw⟩ := WitnessSending.check_sound h
  rw [rel_eq] at hw
  exact ⟨w, hd, hw.mono fun h => by
    rw [WitnessSending.Vb_eq, Bool.and_eq_true] at h; exact h.2⟩

/-- **The library's witness-sending system.** -/
def wsSys : WSys where
  chk := WitnessSending.check
  dec := WitnessSending.decode
  sound := ws_sound
  enc := wsProof
  Fits := WSFits
  complete := check_wsProof

/-- **The size of a shape's library proof**: `136 · #leaves − 88` bytes (48 a leaf, 88 more a node
than its children). -/
theorem size_wsProof : ∀ t : Shape, (wsProof t).size + 88 = 136 * t.leaves.length
  | .leaf s n => by rw [wsProof, WitnessSending.size_encode_leaf]; rfl
  | .node l r => by
    have hl := size_wsProof l
    have hr := size_wsProof r
    rw [wsProof, WitnessSending.size_encode]
    simp only [witWords, bytesWords, List.length_cons, List.length_append, packBytes_length,
      ← WitnessSending.size_eq_length, Vector.length_toList, Shape.leaves]
    omega

/-- **Every shape of at most `7711` leaves fits** the library's format. -/
theorem wsFits_of_length_le : ∀ {t : Shape}, t.leaves.length ≤ 7711 → WSFits t
  | .leaf _ _, _ => trivial
  | .node l r, h => by
    have := size_wsProof l; have := size_wsProof r
    have := length_leaves_pos l; have := length_leaves_pos r
    simp only [Shape.leaves, List.length_append] at h
    exact ⟨by unfold proofCap; omega, by unfold proofCap; omega, wsFits_of_length_le (by omega),
      wsFits_of_length_le (by omega)⟩

/-- **A shape with a child of more than `7710` leaves does not fit** the library's format: the
child's proof exceeds `proofCap`. -/
theorem not_wsFits {l r : Shape} (h : 7710 < l.leaves.length ∨ 7710 < r.leaves.length) :
    ¬ WSFits (.node l r) := by
  have := size_wsProof l; have := size_wsProof r
  rintro ⟨hl, hr, -⟩
  unfold proofCap at hl hr
  omega

/-- Both halves of a flat shape have at most `7711` leaves. -/
def SmallHalves : Shape → Prop
  | .leaf _ _ => True
  | .node l r => l.leaves.length ≤ 7711 ∧ r.leaves.length ≤ 7711

/-- A shape with small halves has fitting halves in the library's format. -/
theorem halvesFit_of_small : ∀ {t : Shape}, SmallHalves t → wsSys.HalvesFit t
  | .leaf _ _, _ => trivial
  | .node _ _, ⟨hl, hr⟩ => ⟨wsFits_of_length_le hl, wsFits_of_length_le hr⟩

variable {X : Type} {stmt : X → Digest} {V₀ : X → Proof → OProg Bool}
  {E₀ : X → Proof → Log → Option Shape} {R₀ : X → Shape → Prop} {ε : ℝ≥0}

/-- **The lift over the library's witness-sending format**, for flat shapes whose halves have at
most `7711` leaves each. -/
theorem lift_ws (C : LCodec X) (k : GKState R₀ V₀ E₀ ε)
    (hR : ∀ x t, R₀ x t → Flat (stmt x) t ∧ SmallHalves t) {qV : ℕ}
    (hq : ∀ H x π₀, ((V₀ x π₀).queries H).length ≤ qV) :
    KSRel (liftV C wsSys stmt V₀) (liftE C wsSys E₀) ε qV ∧
      (∀ c x π₀, stmt x = c → liftV C wsSys stmt V₀ c (C.enc (.snark x π₀)) = V₀ x π₀) ∧
      (∀ H c π, (liftV C wsSys stmt V₀ c (wrap C π)).queries H = []) :=
  lift C k (fun x t h => ⟨(hR x t h).1, halvesFit_of_small (hR x t h).2⟩) hq

/-! ## A cap-free witness-sending format -/

/-- The sub-proofs of a witness: a node's two child proofs. -/
def witSub : Wit → List Proof
  | .leaf _ _ => []
  | .node _ _ π₁ π₂ => [π₁, π₂]

variable (D : Codec Wit witSub)

/-- **The cap-free witness-sending check**: the proof decodes to a leaf witness of the leaf clause,
or to a node witness of `c` whose two children are accepted, recursively; no oracle query, no size
cap. -/
def freeChk (c : Digest) (π : Proof) : Bool :=
  match _h : D.dec π with
  | some (.leaf s n) => decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
  | some (.node c₁ c₂ π₁ π₂) => decide (c = nodeStmt c₁ c₂) && freeChk c₁ π₁ && freeChk c₂ π₂
  | none => false
termination_by π.size
decreasing_by all_goals exact D.lt _h _ (by simp [witSub])

/-- The cap-free proof of a shape. -/
def freeEnc : Shape → Proof
  | .leaf s n => D.enc (.leaf s n)
  | .node l r => D.enc (.node l.root r.root (freeEnc l) (freeEnc r))

theorem freeChk_sound {c : Digest} {π : Proof} (h : freeChk D c π = true) :
    ∃ w, D.dec π = some w ∧ RelWith (fun c π => freeChk D c π = true) c w := by
  rw [freeChk] at h
  split at h
  next s n hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨.leaf s n, hd, h⟩
  next c₁ c₂ π₁ π₂ hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨.node c₁ c₂ π₁ π₂, hd, h.1.1, h.1.2, h.2⟩
  next => cases h

theorem freeChk_freeEnc : ∀ {t : Shape}, (∀ x ∈ t.leaves, x.2 ≤ chainCap) →
    freeChk D t.root (freeEnc D t) = true
  | .leaf s n, h => by
    rw [freeChk]; split <;> simp_all [freeEnc, D.dec_enc, Shape.root, Shape.leaves]
  | .node l r, h => by
    have h₁ := freeChk_freeEnc (t := l) fun x hx => h x (mem_leaves_left hx)
    have h₂ := freeChk_freeEnc (t := r) fun x hx => h x (mem_leaves_right hx)
    rw [freeChk]; split <;> simp_all [freeEnc, D.dec_enc, Shape.root]

/-- **The cap-free witness-sending system**: every shape fits. -/
def freeSys : WSys where
  chk := freeChk D
  dec := D.dec
  sound := freeChk_sound D
  enc := freeEnc D
  Fits _ := True
  complete _ := freeChk_freeEnc D

theorem freeSys_halvesFit (t : Shape) : (freeSys D).HalvesFit t := by
  cases t with
  | leaf => trivial
  | node => exact ⟨trivial, trivial⟩

/-- **The lift with no side condition** (over the cap-free witness-sending format): from any knowledge
state of a flat argument whose witnesses are flat shapes of `stmt x`, the lifted verifier is
relativized knowledge-sound with the same error and query bound, is `V₀` on flat frames and asks
nothing on witness-sending frames. -/
theorem lift_free (C : LCodec X) (k : GKState R₀ V₀ E₀ ε) (hR : ∀ x t, R₀ x t → Flat (stmt x) t)
    {qV : ℕ} (hq : ∀ H x π₀, ((V₀ x π₀).queries H).length ≤ qV) :
    KSRel (liftV C (freeSys D) stmt V₀) (liftE C (freeSys D) E₀) ε qV ∧
      (∀ c x π₀, stmt x = c → liftV C (freeSys D) stmt V₀ c (C.enc (.snark x π₀)) = V₀ x π₀) ∧
      (∀ H c π, (liftV C (freeSys D) stmt V₀ c (wrap C π)).queries H = []) :=
  lift C k (fun x t h => ⟨hR x t h, freeSys_halvesFit D t⟩) hq

instance : Encodable Wit := Encodable.ofEquiv ((Digest × ℕ) ⊕ (Digest × Digest × Proof × Proof))
  { toFun := fun | .leaf s n => .inl (s, n) | .node c₁ c₂ π₁ π₂ => .inr (c₁, c₂, π₁, π₂)
    invFun := fun | .inl (s, n) => .leaf s n | .inr (c₁, c₂, π₁, π₂) => .node c₁ c₂ π₁ π₂
    left_inv := fun w => by cases w <;> rfl
    right_inv := fun w => by rcases w with ⟨_, _⟩ | ⟨_, _, _, _⟩ <;> rfl }

/-- A cap-free witness-sending codec exists (P1's unary codec). -/
def witCodec : Codec Wit witSub := Codec.unary witSub

deriving instance Countable for Shape

/-- Shapes are encodable (through countability; only non-vacuity uses it). -/
noncomputable instance : Encodable Shape := Encodable.ofCountable Shape

/-- **Non-vacuity**: the flat check (`flatState`, no query) lifted over the cap-free format and
unary codecs is relativized knowledge-sound at error `0` with no query. -/
theorem lift_flat_free :
    KSRel (liftV (LCodec.unary (Digest × Shape)) (freeSys witCodec) Prod.fst flatV)
      (liftE (LCodec.unary (Digest × Shape)) (freeSys witCodec) flatE) 0 0 :=
  (lift_free witCodec _ flatState (fun _ _ h => h) fun _ _ _ => le_rfl).1

/-- The lifted flat check accepts the flat frame of every flat statement, under every oracle. -/
theorem lift_flat_accepts {c : Digest} {t : Shape} (h : Flat c t) (π₀ : Proof)
    (H : ByteArray → Digest) :
    (liftV (LCodec.unary (Digest × Shape)) (freeSys witCodec) Prod.fst flatV c
      ((LCodec.unary _).enc (.snark (c, t) π₀))).run H = true := by
  simp [flatV, OProg.run, h]

end RecursionFast.Explore.Lift

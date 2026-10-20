/-
# Exploration: the lift. A flat argument is relativized-sound and never recurses  (UNTRUSTED)

Probe P4 (`docs/explore/notes/T1-impossibility.md` §4.1, Theorem 4.1; notes in
`docs/explore/notes/P4-lift-lean.md`). **The relativized requirement does not force recursion.**
Take any argument `V₀` for the oracle-free *flat* relation "the digest `c` is the `nodeStmt` tree
over these leaves" with a knowledge state of error `ε`. The lifted verifier `liftV` accepts a
witness-sending proof (no query) or a flat proof `(x, π₀)` checked by `V₀` itself. It has a
relativized knowledge state (`KStateRel`, `Relativized/Defs.lean`) with `V₀`'s own potential and
error (`liftState`), asks at most `V₀`'s queries (`queries_liftV_le`), *is* `V₀` on a flat frame
(`liftV_snark`, so its queries there are exactly `V₀`'s) and asks nothing on a witness-sending
frame (`queries_liftV_ws`). Its extractor answers a flat proof with the node witness whose two
children are **witness-sending proofs of the two subtrees**, which the lifted verifier accepts with
no query on every log, so the relativized node clause holds on every log; a one-leaf tree gets its
leaf witness. Headline: `lift`.

* `GKState R V E ε`: the contract's `KState` (same three laws, word for word) with the statement
  and witness types left open, so that a flat argument's statement can carry the leaves.
  `KState.toG`, `GKState.toKState` show that at `Digest`, `Wit` it is the contract's `KState`.
* `Flat c t`: the flat relation. `t : Shape` (`Relativized/Compose.lean`) is a binary tree whose
  leaves are chain starts with lengths; `Flat c t` says that folding `leafStmt (chainEnd s n) n`
  at the leaves with `nodeStmt` at the inner nodes gives `c`, and every chain is within `chainCap`.
  This is exactly `compose_flat`'s conclusion. Any shape is allowed; `Lift/Tree.lean` relates the
  perfect shape over `2^d` leaves to the runner's `treeRoot`.
* `WSys`: what the lift needs of a witness-sending system: an oracle-free check `chk` whose
  accepted proofs decode (`dec`) to a witness of the relation's clauses with `chk`-accepted
  children (`sound`), and an encoder of shapes that `chk` accepts on every flat shape satisfying a
  size predicate `Fits` (`complete`). `Lift/WS.lean` gives the library's witness-sending format
  (`Fits` = every sub-proof within `proofCap`) and a cap-free one (`Fits` = `True`).
* `LFrame X`: a lifted proof is a witness-sending frame `ws π` or a flat frame `snark x π₀`, where
  `x : X` is the flat argument's statement. `stmt x` is the tree digest `x` is about: for flat
  statements that carry the leaves in the clear, `X = Digest × Shape` and `stmt = Prod.fst` (the
  form `T1` §7 asks for); for a flat argument whose witness hides them, `X = Digest`, `stmt = id`.
  The byte format is P1's abstract `Codec` (no sub-proofs: `liftV` is not recursive).

**Hypothesis on `V₀`.** A `GKState R₀ V₀ E₀ ε` for any relation `R₀` whose witnesses are flat
shapes of `stmt x` (`hR`), with each half satisfying the witness-sending system's `Fits` (vacuous
for the cap-free system). Nothing else: no completeness, no succinctness, no bound on the shape.
`lift_paper` restates the result as the probability bound of `Library/PaperTheorem.lean`.
Non-vacuity: `flatState` (the flat check, a non-succinct `V₀` with no query) meets the hypothesis;
`Lift/WS.lean` lifts it (`lift_flat_free`, `lift_flat_accepts`).
-/
import RecursionFast.Explore.Relativized.Compose

open scoped NNReal

namespace RecursionFast.Explore.Lift
open Relativized

/-! ## Knowledge states over any statement type -/

/-- **A knowledge state** with per-query error `ε` for a relation `R` between statements `X` and
witnesses `W`, a verifier `V` and an extractor `E`: the contract's `KState` with its statement and
witness types left open (the laws are the contract's, word for word). -/
structure GKState {X W : Type} (R : X → W → Prop) (V : X → Proof → OProg Bool)
    (E : X → Proof → Log → Option W) (ε : ℝ≥0) where
  /-- The potential of a log; below `1`, no accepted proof escapes the extractor. -/
  μ : Log → ℝ≥0
  /-- The empty log has potential `0`. -/
  empty : μ [] = 0
  /-- Within `logCap` and below `1`, a fresh query raises the potential by at most `ε` on average
  over its `2^256` answers. -/
  step : ∀ L q, L.length < logCap → μ L < 1 → q ∉ L.map Prod.fst →
    ∑ a : Digest, μ (L ++ [(q, a)]) ≤ (μ L + ε) * 2 ^ 256
  /-- Within `logCap` and below `1`, every proof the verifier accepts on the log's answers is
  extracted to a witness. -/
  final : ∀ L x π, L.length ≤ logCap → μ L < 1 → (V x π).runLog L = some true →
    ∃ w, E x π L = some w ∧ R x w

variable {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
  {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0}

/-- A contract knowledge state is one over `Digest` and `Wit`. -/
def _root_.RecursionFast.KState.toG (k : KState R V E ε) : GKState R V E ε :=
  ⟨k.μ, k.empty, k.step, k.final⟩

/-- A knowledge state over `Digest` and `Wit` is a contract knowledge state. -/
def GKState.toKState (k : GKState R V E ε) : KState R V E ε := ⟨k.μ, k.empty, k.step, k.final⟩

/-- A knowledge state's extractor post-composed with a map of witnesses that carries `R` into
`R'` is a knowledge state for `R'`, with the same potential. -/
def GKState.map {X W W' : Type} {R : X → W → Prop} {R' : X → W' → Prop}
    {V : X → Proof → OProg Bool} {E : X → Proof → Log → Option W} (f : X → W → W')
    (hf : ∀ x w, R x w → R' x (f x w)) (k : GKState R V E ε) :
    GKState R' V (fun x π L => (E x π L).map (f x)) ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L x π hL hμ h :=
    let ⟨w, hw, hR⟩ := k.final L x π hL hμ h
    ⟨f x w, by simp [hw], hf x w hR⟩

/-! ## The flat relation and witness-sending systems -/

/-- **The flat relation**: the shape `t` folds to the digest `c` (`leafStmt (chainEnd s n) n` at
each leaf `(s, n)`, `nodeStmt` at each inner node) and every chain is within `chainCap`. -/
def Flat (c : Digest) (t : Shape) : Prop := t.root = c ∧ ∀ x ∈ t.leaves, x.2 ≤ chainCap

instance (c : Digest) (t : Shape) : Decidable (Flat c t) := by unfold Flat; infer_instance

/-- **A witness-sending system**: an oracle-free check, a decoder of its accepted proofs into
witnesses of the relation's clauses with accepted children, and an encoder of shapes accepted on
every flat shape that fits its size limit. -/
structure WSys where
  /-- The check: no oracle query. -/
  chk : Digest → Proof → Bool
  /-- The witness an accepted proof sends. -/
  dec : Proof → Option Wit
  /-- An accepted proof sends a leaf witness of the leaf clause, or a node witness of `c` whose
  two children are accepted. -/
  sound : ∀ {c π}, chk c π = true → ∃ w, dec π = some w ∧ RelWith (fun c π => chk c π = true) c w
  /-- The proof that sends a shape. -/
  enc : Shape → Proof
  /-- The shapes the format can send. -/
  Fits : Shape → Prop
  /-- The proof of a fitting shape whose chains are within `chainCap` is accepted for its root. -/
  complete : ∀ {t}, Fits t → (∀ x ∈ t.leaves, x.2 ≤ chainCap) → chk t.root (enc t) = true

/-- Both halves of a shape fit the format (a one-leaf shape has no halves). -/
def WSys.HalvesFit (W : WSys) : Shape → Prop
  | .leaf _ _ => True
  | .node l r => W.Fits l ∧ W.Fits r

/-- **A lifted proof**: a witness-sending proof, or a flat argument's statement `x` with its proof
`π₀`. -/
inductive LFrame (X : Type) where
  /-- A witness-sending proof. -/
  | ws (π : Proof)
  /-- A flat statement and a flat proof. -/
  | snark (x : X) (π₀ : Proof)

/-- The byte format of lifted proofs: P1's abstract codec, with no sub-proofs (the lifted verifier
does not recurse). -/
abbrev LCodec (X : Type) := Codec (LFrame X) fun _ => []

/-! ## The lift -/

variable {X : Type} (C : LCodec X) (W : WSys) (stmt : X → Digest) (V₀ : X → Proof → OProg Bool)
  (E₀ : X → Proof → Log → Option Shape)

/-- **The lifted verifier**: a witness-sending frame is judged by the witness-sending check, with
no query; a flat frame `(x, π₀)` is accepted when `x` is a statement about `c` and `V₀` accepts
`π₀` for `x`. Not recursive. -/
def liftV (c : Digest) (π : Proof) : OProg Bool :=
  match C.dec π with
  | some (.ws π') => .ret (W.chk c π')
  | some (.snark x π₀) => if stmt x = c then V₀ x π₀ else .ret false
  | none => .ret false

/-- A witness-sending proof as a lifted proof. -/
def wrap (π : Proof) : Proof := C.enc (.ws π)

/-- A witness-sending witness as a lifted one: its child proofs wrapped. -/
def rewrap : Wit → Wit
  | .leaf s n => .leaf s n
  | .node c₁ c₂ π₁ π₂ => .node c₁ c₂ (wrap C π₁) (wrap C π₂)

/-- **The witness the lifted extractor gives a flat shape**: its leaf witness if it is one leaf,
else the node witness whose children are the witness-sending proofs of its two halves. -/
def halves : Shape → Wit
  | .leaf s n => .leaf s n
  | .node l r => .node l.root r.root (wrap C (W.enc l)) (wrap C (W.enc r))

/-- **The lifted extractor**: on a witness-sending frame, the witness it sends (children wrapped);
on a flat frame, `halves` of the shape `E₀` extracts. -/
def liftE (_ : Digest) (π : Proof) (L : Log) : Option Wit :=
  match C.dec π with
  | some (.ws π') => (W.dec π').map (rewrap C)
  | some (.snark x π₀) => (E₀ x π₀ L).map (halves C W)
  | none => none

@[simp] theorem liftV_ws (c : Digest) (π : Proof) :
    liftV C W stmt V₀ c (wrap C π) = .ret (W.chk c π) := by
  simp [liftV, wrap, C.dec_enc]

/-- **On a flat frame the lifted verifier is `V₀`**, as a program (the same queries, in the same
order, with the same verdict on every oracle and every log). -/
@[simp] theorem liftV_snark (c : Digest) (x : X) (π₀ : Proof) :
    liftV C W stmt V₀ c (C.enc (.snark x π₀)) = if stmt x = c then V₀ x π₀ else .ret false := by
  simp [liftV, C.dec_enc]

/-- A wrapped witness-sending proof the check accepts is accepted on every log. -/
theorem runLog_wrap (L : Log) {c : Digest} {π : Proof} (h : W.chk c π = true) :
    (liftV C W stmt V₀ c (wrap C π)).runLog L = some true := by
  simp [OProg.runLog, h]

/-- **The halves of a flat shape are a relativized witness on every log**: a leaf witness of the
leaf clause, or a node witness of `c` whose wrapped witness-sending children are accepted with no
query. -/
theorem relL_halves (L : Log) {c : Digest} {t : Shape} (ht : Flat c t) (hf : W.HalvesFit t) :
    RelL (liftV C W stmt V₀) L c (halves C W t) := by
  obtain ⟨hroot, hcap⟩ := ht
  cases t with
  | leaf s n => exact ⟨hcap _ (List.mem_singleton_self _), hroot.symm⟩
  | node l r =>
    refine ⟨hroot.symm, runLog_wrap C W stmt V₀ L (W.complete hf.1 fun x hx => ?_),
      runLog_wrap C W stmt V₀ L (W.complete hf.2 fun x hx => ?_)⟩ <;>
      exact hcap x (by simp [Shape.leaves, hx])

/-- A witness the check's relation accepts, children wrapped, is a relativized witness on every
log. -/
theorem relL_rewrap (L : Log) {c : Digest} {w : Wit}
    (h : RelWith (fun c π => W.chk c π = true) c w) :
    RelL (liftV C W stmt V₀) L c (rewrap C w) := by
  cases w with
  | leaf s n => exact h
  | node c₁ c₂ π₁ π₂ =>
    exact ⟨h.1, runLog_wrap C W stmt V₀ L h.2.1, runLog_wrap C W stmt V₀ L h.2.2⟩

variable {W stmt V₀ E₀} {R₀ : X → Shape → Prop}

/-- **The lift's knowledge state**: a knowledge state of `V₀` for a relation whose witnesses are
flat shapes of `stmt x` with fitting halves gives the lifted verifier a relativized knowledge
state with **the same potential and the same error**. -/
def liftState (k : GKState R₀ V₀ E₀ ε) (hR : ∀ x t, R₀ x t → Flat (stmt x) t ∧ W.HalvesFit t) :
    KStateRel (liftV C W stmt V₀) (liftE C W E₀) ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L c π hL hμ h := by
    unfold liftV at h
    rcases hd : C.dec π with _ | _ | ⟨x, π₀⟩ <;> rw [hd] at h
    · simp [OProg.runLog] at h
    · obtain ⟨w, hw, hrel⟩ := W.sound (Option.some.inj h)
      exact ⟨rewrap C w, by simp [liftE, hd, hw], relL_rewrap C W stmt V₀ L hrel⟩
    · dsimp only at h
      split_ifs at h with hx
      · obtain ⟨t, ht, hrt⟩ := k.final L x π₀ hL hμ h
        obtain ⟨hflat, hfit⟩ := hR x t hrt
        exact ⟨halves C W t, by simp [liftE, hd, ht], relL_halves C W stmt V₀ L (hx ▸ hflat) hfit⟩
      · simp [OProg.runLog] at h

theorem liftState_μ (k : GKState R₀ V₀ E₀ ε)
    (hR : ∀ x t, R₀ x t → Flat (stmt x) t ∧ W.HalvesFit t) : (liftState C k hR).μ = k.μ := rfl

/-! ## Queries -/

variable (W stmt V₀)

/-- **No query on a witness-sending frame.** -/
theorem queries_liftV_ws (H : ByteArray → Digest) (c : Digest) (π : Proof) :
    (liftV C W stmt V₀ c (wrap C π)).queries H = [] := by
  simp [OProg.queries]

/-- **On a flat frame, exactly `V₀`'s queries.** -/
theorem queries_liftV_snark (H : ByteArray → Digest) {c : Digest} {x : X} (hx : stmt x = c)
    (π₀ : Proof) : (liftV C W stmt V₀ c (C.enc (.snark x π₀))).queries H = (V₀ x π₀).queries H := by
  simp [hx]

/-- **The lifted verifier asks at most what `V₀` asks.** -/
theorem queries_liftV_le {qV : ℕ} (hq : ∀ H x π₀, ((V₀ x π₀).queries H).length ≤ qV)
    (H : ByteArray → Digest) (c : Digest) (π : Proof) :
    ((liftV C W stmt V₀ c π).queries H).length ≤ qV := by
  unfold liftV
  rcases C.dec π with _ | _ | ⟨x, π₀⟩
  · simp [OProg.queries]
  · simp [OProg.queries]
  · dsimp only
    split_ifs
    · exact hq H x π₀
    · simp [OProg.queries]

/-! ## The lift theorem -/

variable {W stmt V₀}

/-- **The lift (T1 Theorem 4.1).** From a knowledge state of error `ε` for a flat argument `V₀`
asking at most `qV` queries: the lifted verifier is relativized knowledge-sound with the same
error and the same query bound; on a flat frame it is `V₀` itself; on a witness-sending frame it
asks nothing. It never runs itself or `V₀` on a sub-proof: nothing it accepts is checked by
recursion. -/
theorem lift (k : GKState R₀ V₀ E₀ ε) (hR : ∀ x t, R₀ x t → Flat (stmt x) t ∧ W.HalvesFit t)
    {qV : ℕ} (hq : ∀ H x π₀, ((V₀ x π₀).queries H).length ≤ qV) :
    KSRel (liftV C W stmt V₀) (liftE C W E₀) ε qV ∧
      (∀ c x π₀, stmt x = c → liftV C W stmt V₀ c (C.enc (.snark x π₀)) = V₀ x π₀) ∧
      (∀ H c π, (liftV C W stmt V₀ c (wrap C π)).queries H = []) :=
  ⟨⟨⟨liftState C k hR⟩, queries_liftV_le C W stmt V₀ hq⟩, fun c x π₀ hx => by simp [hx],
    queries_liftV_ws C W stmt V₀⟩

open PaperTheorem in
/-- **The lift's paper theorem**: in a game of at most `n ≤ logCap` lazily sampled queries, the
lifted verifier accepts on the final log while its extractor returns no relativized witness on that
log with probability at most `n · ε`, the flat argument's own bound. -/
theorem lift_paper (k : GKState R₀ V₀ E₀ ε) (hR : ∀ x t, R₀ x t → Flat (stmt x) t ∧ W.HalvesFit t)
    (G : OProg (Digest × Proof)) (n : ℕ) (hG : DepthLE G n) (hn : n ≤ logCap) :
    prob (fun y L => (liftV C W stmt V₀ y.1 y.2).runLog L = some true ∧
      ¬ ∃ w, liftE C W E₀ y.1 y.2 L = some w ∧ RelL (liftV C W stmt V₀) L y.1 w) G [] ≤ n * ε :=
  (liftState C k hR).paper G n hG hn

/-! ## The hypotheses can be met -/

/-- Every encodable statement type has a lifted byte format (P1's unary codec). -/
instance {X : Type} [Encodable X] : Encodable (LFrame X) := Encodable.ofEquiv (Proof ⊕ (X × Proof))
  { toFun := fun | .ws π => .inl π | .snark x π₀ => .inr (x, π₀)
    invFun := fun | .inl π => .ws π | .inr (x, π₀) => .snark x π₀
    left_inv := fun f => by cases f <;> rfl
    right_inv := fun f => by rcases f with _ | ⟨_, _⟩ <;> rfl }

/-- A lifted byte format exists for every encodable statement type. -/
def LCodec.unary (X : Type) [Encodable X] : LCodec X := Codec.unary _

/-- **The flat check** (a non-succinct flat argument, for non-vacuity): the statement carries the
shape in the clear, and the verifier decides `Flat` itself, with no query and no proof. -/
def flatV (x : Digest × Shape) (_ : Proof) : OProg Bool := .ret (decide (Flat x.1 x.2))

/-- The flat check's extractor: the shape the statement carries. -/
def flatE (x : Digest × Shape) (_ : Proof) (_ : Log) : Option Shape := some x.2

/-- The flat check has a knowledge state for the flat relation at potential `0` and error `0`. -/
def flatState : GKState (fun x t => Flat x.1 t) flatV flatE 0 where
  μ _ := 0
  empty := rfl
  step _ _ _ _ _ := by simp
  final _ x _ _ _ h := ⟨x.2, rfl, of_decide_eq_true (Option.some.inj h)⟩

end RecursionFast.Explore.Lift

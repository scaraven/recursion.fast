/-
# Exploration: a parent must re-ask its children's queries                       (UNTRUSTED)

Probe P1, item 5. A node proof may carry the oracle answers `Q` its children were judged against.
Whether the parent **asks** them decides soundness.

**(a) Lazy: judging children against unasked answers is unsound.** `lazyV C Vc` takes a node frame
`(c₁, c₂, π₁, π₂, Q)` and accepts when `c = nodeStmt c₁ c₂` and it accepts both children reading
`Q`, without querying the oracle. Its node proofs are accepted on the **empty** log, where the
potential is `0`, so `final` must open them there, and the relativized node clause then asks for
children accepted on the empty log. Over a base verifier `Vc` that asks a query on every input
(`hq`):
* `lazy_no_kstate`: with the natural extractor (`dE`: the node frame's fields) there is no
  relativized knowledge state at any error: the children it returns are base proofs, which need an
  answer the empty log does not have.
* `lazy_extractor_collides`: **every** extractor of a relativized knowledge state must, from two
  statements `c₁, c₂` with accepted base proofs, output on the empty log a preimage of
  `nodeStmt c₁ c₂` that is a leaf statement, or a node whose children are themselves lazy node
  statements (`Collides`). When `c₁` is a leaf statement, each case is a BLAKE2s collision
  between distinct inputs (`tagLeaf ‖ …` against `tagNode ‖ …`, or a second preimage of
  `nodeStmt c₁ c₂`), computed from the extractor's output.
  The brief asked for `¬ Nonempty (KStateRel …)` for **every** extractor. That is not provable
  here: an extractor may be any function, and whether one exists is a fact about BLAKE2s that no
  proof here decides. If every digest were the leaf statement of a chain of length `0`, **every**
  verifier would have a relativized knowledge state at error `0` (`kstate_of_leaf_surjective`,
  the analogue of `acceptAll_kstate_iff`), so `∀ E, ¬ Nonempty …` would refute that BLAKE2s
  property. `lazy_extractor_collides` is the corrected statement: certifying the lazy verifier
  means exhibiting an extractor that outputs BLAKE2s collisions on every such input.
* `W1` (witness-sending with one dummy query) is a base verifier meeting the hypotheses, with a
  relativized knowledge state at potential `0` (`w1State`); `lazy_W1_no_kstate`, `lazy_W1_collides`
  instantiate (a) for it.

**(b) Deferral: re-asking makes it sound.** `deferV C Vc` first asks every `(q, a)` in `Q` and
checks the answer is `a` (`checkAll`), then judges the children reading `Q`. If all checks pass,
`Q` agrees with the log, so by monotonicity (`runLog_of_agrees`, `Defs.lean`) the children are
accepted on the log itself. `deferState`: a relativized knowledge state for `Vc` gives one for
`deferV C Vc` with the same potential and error (`defer_W1` for `W1`). A node asks at most the
`|Q|` queries of `Q` (`queries_defer`), and an honest `Q` lists the children's queries, so a node
asks as many oracle queries as running its children would: deferral compresses only the parent's
**local** work, never its oracle calls.

**Abstraction.** The byte format is a `Codec DFrame DFrame.sub` (`Defs.lean`); `Codec.unary`
inhabits it (`lazy_unary_no_kstate` instantiates (a) with it, for non-vacuity).
-/
import RecursionFast.Explore.Relativized.Defs
import RecursionFast.Library.WitnessSending

open scoped NNReal

namespace RecursionFast.Explore.Relativized

variable (C : Codec DFrame DFrame.sub) (Vc : Digest → Proof → OProg Bool) {ε : ℝ≥0}

/-! ## The two node verifiers and their extractor -/

/-- **The lazy verifier**: a base frame is judged by `Vc`; a node frame `(c₁, c₂, π₁, π₂, Q)` is
accepted when `c` is the children's node statement and this verifier accepts both children
reading the unasked answers `Q`. No oracle query at a node. -/
def lazyV (c : Digest) (π : Proof) : OProg Bool :=
  match _h : C.dec π with
  | some (.base π') => Vc c π'
  | some (.defer c₁ c₂ π₁ π₂ Q) =>
    .ret (decide (c = nodeStmt c₁ c₂) && decide ((lazyV c₁ π₁).runLog Q = some true) &&
      decide ((lazyV c₂ π₂).runLog Q = some true))
  | none => .ret false
termination_by π.size
decreasing_by all_goals exact C.lt _h _ (by simp [DFrame.sub])

/-- Ask every query of `Q` and check its answer is the one `Q` records, then run `p`; reject at the
first mismatch. -/
def checkAll : Log → OProg Bool → OProg Bool
  | [], p => p
  | (q, a) :: Q, p => .query q fun a' => if a' = a then checkAll Q p else .ret false

/-- **The deferral verifier**: as `lazyV`, but a node first asks every query of `Q` and checks the
recorded answers. -/
def deferV (c : Digest) (π : Proof) : OProg Bool :=
  match _h : C.dec π with
  | some (.base π') => Vc c π'
  | some (.defer c₁ c₂ π₁ π₂ Q) =>
    checkAll Q (.ret (decide (c = nodeStmt c₁ c₂) &&
      decide ((deferV c₁ π₁).runLog Q = some true) && decide ((deferV c₂ π₂).runLog Q = some true)))
  | none => .ret false
termination_by π.size
decreasing_by all_goals exact C.lt _h _ (by simp [DFrame.sub])

/-- A base witness as a witness of the node verifiers: a node's child proofs wrapped as base
frames. -/
def lift : Wit → Wit
  | .leaf s n => .leaf s n
  | .node c₁ c₂ π₁ π₂ => .node c₁ c₂ (C.enc (.base π₁)) (C.enc (.base π₂))

/-- The natural extractor of the node verifiers: the base extractor `E` (lifted) on a base frame,
the frame's fields on a node frame. -/
def dE (E : Digest → Proof → Log → Option Wit) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  match C.dec π with
  | some (.base π') => (E c π' L).map (lift C)
  | some (.defer c₁ c₂ π₁ π₂ _) => some (.node c₁ c₂ π₁ π₂)
  | none => none

theorem lazyV_base (c : Digest) (π' : Proof) : lazyV C Vc c (C.enc (.base π')) = Vc c π' := by
  rw [lazyV]; split <;> simp_all [C.dec_enc]

theorem lazyV_defer (c c₁ c₂ : Digest) (π₁ π₂ : Proof) (Q : Log) :
    lazyV C Vc c (C.enc (.defer c₁ c₂ π₁ π₂ Q)) =
      .ret (decide (c = nodeStmt c₁ c₂) && decide ((lazyV C Vc c₁ π₁).runLog Q = some true) &&
        decide ((lazyV C Vc c₂ π₂).runLog Q = some true)) := by
  rw [lazyV]; split <;> simp_all [C.dec_enc]

theorem deferV_base (c : Digest) (π' : Proof) : deferV C Vc c (C.enc (.base π')) = Vc c π' := by
  rw [deferV]; split <;> simp_all [C.dec_enc]

theorem dE_defer (E : Digest → Proof → Log → Option Wit) (c c₁ c₂ : Digest) (π₁ π₂ : Proof)
    (Q L : Log) : dE C E c (C.enc (.defer c₁ c₂ π₁ π₂ Q)) L = some (.node c₁ c₂ π₁ π₂) := by
  simp [dE, C.dec_enc]

/-! ## (a) The lazy verifier -/

/-- The node proof over the base proofs `π₁`, `π₂` of `c₁`, `c₂`, carrying the answers `Q`. -/
def nodeProof (c₁ c₂ : Digest) (π₁ π₂ : Proof) (Q : Log) : Proof :=
  C.enc (.defer c₁ c₂ (C.enc (.base π₁)) (C.enc (.base π₂)) Q)

/-- A lazy node statement: `ρ` is a node frame over `x, y` and `d` is their node statement. -/
def IsLazyNode (d : Digest) (ρ : Proof) : Prop :=
  ∃ x y ρ₁ ρ₂ Q, C.dec ρ = some (.defer x y ρ₁ ρ₂ Q) ∧ d = nodeStmt x y

/-- What an extractor must output for the lazy node over `c₁, c₂` on the empty log: a leaf
witness whose statement is `nodeStmt c₁ c₂`, or a node witness `(d₁, d₂)` with
`nodeStmt d₁ d₂ = nodeStmt c₁ c₂` whose children are lazy node statements. -/
def Collides (c₁ c₂ : Digest) : Wit → Prop
  | .leaf s n => n ≤ chainCap ∧ nodeStmt c₁ c₂ = leafStmt (chainEnd s n) n
  | .node d₁ d₂ ρ₁ ρ₂ => nodeStmt d₁ d₂ = nodeStmt c₁ c₂ ∧ IsLazyNode C d₁ ρ₁ ∧ IsLazyNode C d₂ ρ₂

variable {C Vc}

/-- Over a base verifier that queries on every input, only lazy node statements are accepted on
the empty log. -/
theorem isLazyNode_of_empty (hq : ∀ c π, (Vc c π).runLog [] = none) {d : Digest} {ρ : Proof}
    (h : (lazyV C Vc d ρ).runLog [] = some true) : IsLazyNode C d ρ := by
  rw [lazyV] at h
  split at h
  next π' _ => simp [hq] at h
  next x y ρ₁ ρ₂ Q hd =>
    simp only [OProg.runLog, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨x, y, ρ₁, ρ₂, Q, hd, h.1.1⟩
  next => simp [OProg.runLog] at h

/-- The lazy node proof over accepted base proofs is accepted on the empty log. -/
theorem lazy_accepts {c₁ c₂ : Digest} {π₁ π₂ : Proof} {Q : Log}
    (h₁ : (Vc c₁ π₁).runLog Q = some true) (h₂ : (Vc c₂ π₂).runLog Q = some true) :
    (lazyV C Vc (nodeStmt c₁ c₂) (nodeProof C c₁ c₂ π₁ π₂ Q)).runLog [] = some true := by
  simp [nodeProof, lazyV_defer, lazyV_base, h₁, h₂, OProg.runLog]

/-- **No relativized knowledge state for the lazy verifier** with its natural extractor, at any
error, as soon as two base proofs are accepted on some list of answers. -/
theorem lazy_no_kstate (hq : ∀ c π, (Vc c π).runLog [] = none)
    (E : Digest → Proof → Log → Option Wit) {c₁ c₂ : Digest} {π₁ π₂ : Proof} {Q : Log}
    (h₁ : (Vc c₁ π₁).runLog Q = some true) (h₂ : (Vc c₂ π₂).runLog Q = some true) (ε : ℝ≥0) :
    ¬ Nonempty (KStateRel (lazyV C Vc) (dE C E) ε) := by
  rintro ⟨k⟩
  obtain ⟨w, hw, hR⟩ := k.final [] _ _ (Nat.zero_le _) (by rw [k.empty]; exact one_pos)
    (lazy_accepts h₁ h₂)
  rw [nodeProof, dE_defer, Option.some.injEq] at hw
  subst hw
  simp [lazyV_base, hq] at hR

/-- **Every extractor of a relativized knowledge state for the lazy verifier finds collisions**:
on the empty log it opens the lazy node over two accepted base proofs to a `Collides` witness. -/
theorem lazy_extractor_collides (hq : ∀ c π, (Vc c π).runLog [] = none)
    {E : Digest → Proof → Log → Option Wit} (k : KStateRel (lazyV C Vc) E ε) {c₁ c₂ : Digest}
    {π₁ π₂ : Proof} {Q : Log} (h₁ : (Vc c₁ π₁).runLog Q = some true)
    (h₂ : (Vc c₂ π₂).runLog Q = some true) :
    ∃ w, E (nodeStmt c₁ c₂) (nodeProof C c₁ c₂ π₁ π₂ Q) [] = some w ∧ Collides C c₁ c₂ w := by
  obtain ⟨w, hw, hR⟩ := k.final [] _ _ (Nat.zero_le _) (by rw [k.empty]; exact one_pos)
    (lazy_accepts h₁ h₂)
  refine ⟨w, hw, ?_⟩
  cases w with
  | leaf s n => exact ⟨hR.1, hR.2⟩
  | node d₁ d₂ ρ₁ ρ₂ => exact ⟨hR.1.symm, isLazyNode_of_empty hq hR.2.1,
      isLazyNode_of_empty hq hR.2.2⟩

/-- **Why (a) names the extractor**: if every digest is the leaf statement of a chain of length
`0` (a property of BLAKE2s that nothing here refutes), every verifier has a relativized knowledge
state at error `0`, for the extractor that inverts `leafStmt`. -/
theorem kstate_of_leaf_surjective (V : Digest → Proof → OProg Bool)
    (h : ∀ c, ∃ s, c = leafStmt (chainEnd s 0) 0) : ∃ E, Nonempty (KStateRel V E 0) :=
  ⟨fun c _ _ => some (.leaf (h c).choose 0),
    ⟨.zero 0 fun _ c _ _ => ⟨_, rfl, Nat.zero_le _, (h c).choose_spec⟩⟩⟩

/-! ## (b) The deferral verifier -/

/-- If `checkAll Q p` accepts on `L`, then `Q` agrees with `L` and `p` accepts on `L`. -/
theorem runLog_checkAll {L : Log} {p : OProg Bool} :
    ∀ {Q}, (checkAll Q p).runLog L = some true → Agrees Q L ∧ p.runLog L = some true
  | [], h => ⟨by simp [Agrees], h⟩
  | (q, a) :: Q, h => by
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split_ifs at h with ha
    · obtain ⟨hQ, hp⟩ := runLog_checkAll h
      refine ⟨fun f hf => ?_, hp⟩
      rcases List.mem_cons.mp hf with rfl | hf
      · simp [firstAns, he, ha]
      · exact hQ f hf
    · simp [OProg.runLog] at h

/-- `checkAll Q (ret b)` asks at most the `|Q|` queries of `Q`. -/
theorem queries_checkAll (H : ByteArray → Digest) (b : Bool) :
    ∀ Q, ((checkAll Q (.ret b)).queries H).length ≤ Q.length
  | [] => by simp [checkAll, OProg.queries]
  | (q, a) :: Q => by
    simp only [checkAll, OProg.queries, List.length_cons]
    split_ifs
    · exact Nat.succ_le_succ (queries_checkAll H b Q)
    · simp [OProg.queries]

/-- A deferral node asks at most the `|Q|` queries of its answer list. -/
theorem queries_defer (H : ByteArray → Digest) (c c₁ c₂ : Digest) (π₁ π₂ : Proof) (Q : Log) :
    ((deferV C Vc c (C.enc (.defer c₁ c₂ π₁ π₂ Q))).queries H).length ≤ Q.length := by
  rw [deferV]; split <;> simp_all [C.dec_enc, queries_checkAll]

variable (C) in
/-- **Deferral is relativized-sound**: a relativized knowledge state for the base verifier gives
the deferral verifier one with the same potential and error. -/
def deferState {E : Digest → Proof → Log → Option Wit} (k : KStateRel Vc E ε) :
    KStateRel (deferV C Vc) (dE C E) ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L c π hL hμ h := by
    rw [deferV] at h
    split at h
    next π' hd =>
      obtain ⟨w, hE, hw⟩ := k.final L c π' hL hμ h
      refine ⟨lift C w, by simp [dE, hd, hE], ?_⟩
      cases w with
      | leaf s n => exact hw
      | node c₁ c₂ π₁ π₂ => simpa [lift, deferV_base] using hw
    next c₁ c₂ π₁ π₂ Q hd =>
      obtain ⟨hQ, hb⟩ := runLog_checkAll h
      simp only [OProg.runLog, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at hb
      exact ⟨.node c₁ c₂ π₁ π₂, by simp [dE, hd], hb.1.1, runLog_of_agrees hQ hb.1.2,
        runLog_of_agrees hQ hb.2⟩
    next => simp [OProg.runLog] at h

/-! ## A base verifier that meets the hypotheses -/

/-- The witness-sending verifier with one dummy query (the empty string): every run asks it. -/
def W1 (c : Digest) (π : Proof) : OProg Bool :=
  .query .empty fun _ => .ret (WitnessSending.check c π)

theorem runLog_W1 (L : Log) (c : Digest) (π : Proof) :
    (W1 c π).runLog L = (firstAns L .empty).map fun _ => WitnessSending.check c π := by
  simp only [W1, OProg.runLog, firstAns]
  cases L.find? (fun e => decide (e.1 = .empty)) <;> rfl

theorem W1_empty (c : Digest) (π : Proof) : (W1 c π).runLog [] = none := rfl

/-- `W1` is relativized-sound at potential `0`. -/
def w1State : KStateRel W1 WitnessSending.E 0 :=
  .zero 0 fun L c π h => by
    rw [runLog_W1] at h
    obtain ⟨a, ha, hc⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨w, hd, hw⟩ := WitnessSending.check_sound hc
    refine ⟨w, hd, (rel_eq _ ▸ hw).mono fun h => ?_⟩
    rw [WitnessSending.Vb_eq, Bool.and_eq_true] at h
    simp [runLog_W1, ha, h.2]

/-- The leaf statement of the empty chain from the zero digest, and its witness-sending proof. -/
def l₀ : Digest := leafStmt (chainEnd (Vector.replicate 32 0) 0) 0

/-- The witness-sending proof of `l₀`. -/
def p₀ : Proof := WitnessSending.encode (.leaf (Vector.replicate 32 0) 0)

theorem W1_accepts : (W1 l₀ p₀).runLog [(.empty, Vector.replicate 32 0)] = some true := by
  simp [W1, OProg.runLog, p₀, l₀, WitnessSending.check_leaf _ _ (by decide : 0 < 2 ^ 64),
    chainCap]

/-- (a) for `W1`: no relativized knowledge state with the natural extractor, at any error. -/
theorem lazy_W1_no_kstate (ε : ℝ≥0) :
    ¬ Nonempty (KStateRel (lazyV C W1) (dE C WitnessSending.E) ε) :=
  lazy_no_kstate W1_empty _ W1_accepts W1_accepts ε

/-- (a) for `W1`: every extractor of a relativized knowledge state finds collisions. -/
theorem lazy_W1_collides {E : Digest → Proof → Log → Option Wit} (k : KStateRel (lazyV C W1) E ε) :
    ∃ w, E (nodeStmt l₀ l₀) (nodeProof C l₀ l₀ p₀ p₀ [(.empty, Vector.replicate 32 0)]) [] =
      some w ∧ Collides C l₀ l₀ w :=
  lazy_extractor_collides W1_empty k W1_accepts W1_accepts

/-- (a) with the unary codec: the hypotheses of `lazy_W1_no_kstate` are met. -/
theorem lazy_unary_no_kstate (ε : ℝ≥0) :
    ¬ Nonempty (KStateRel (lazyV (Codec.unary DFrame.sub) W1)
      (dE (Codec.unary DFrame.sub) WitnessSending.E) ε) :=
  lazy_W1_no_kstate ε

variable (C) in
/-- (b) for `W1`: the deferral verifier over `W1` is relativized-sound at potential `0`. -/
def defer_W1 : KStateRel (deferV C W1) (dE C WitnessSending.E) 0 := deferState C w1State

end RecursionFast.Explore.Relativized

/-
# Exploration: attestation escapes "the parent must re-ask"                        (UNTRUSTED)

Probe P2, item 4, the point of the exercise. P1 (`Relativized/Lazy.lean`) showed that in the pure
ROM a parent that judges its children against answers it did not ask is unsound
(`lazy_no_kstate`: its node proofs are accepted on the empty log, where no child is accepted), and
that a parent that re-asks them is sound but makes `|Q|` oracle queries per node
(`queries_defer`), as many as running its children. **With the attestation service, one call
per node suffices.**

* `attV C Vc`: a base frame is judged by the child verifier `Vc`; a node frame
  `(c₁, c₂, π₁, π₂, xs)` makes **one** call, `attest (hashList xs)`, and accepts when it is
  attested, `xs` is bounded, `c = nodeStmt c₁ c₂`, and `attV` accepts both children **reading
  `xs`** (`runItems`, the in-circuit run; children in the clear). The children may be node frames
  themselves: their own `attest` calls are answered by the `att` items of `xs`, so a node's list
  holds its children's answers and its children's list hashes, and the root makes one call for the
  whole tree (recursive attestation, W2 §A.1).
* `attE C Ec`: on a node frame, find the first certified list `ys` of the log with
  `hashList ys = hashList xs`; return the node witness if `ys = xs`, else **the pair `(xs, ys)`
  as a collision**. On a base frame, the child extractor `Ec`.
* **`attState`**: a `KStateA Vc Ec ε` gives `KStateA (attV C Vc) (attE C Ec) ε` with the same
  potential. Why: on a well-formed log the attested hash is that of a certified list `ys`, which
  is valid (every answer is the log's, every hash attested). If `ys = xs`, the children's verdicts
  read from `xs` are their verdicts on the log (`runItems_valid`), which is the relativized node
  clause. If not, `xs ≠ ys` are bounded with one hash.
* **`calls_node`**: at a node, the calls of `attV` are exactly `[attest (hashList xs)]`, for every
  oracle and attest predicate: one attestation request, no query. `attKSA`: with a child verifier
  of at most `qV ≥ 1` calls, `attV` makes at most `qV` calls on every input, at every level.
* **`att_W1`**: over P1's `W1` (witness-sending with one dummy query, lifted), `KSA` at error `0`
  with **one call per verification**, every level of the tree. Contrast `deferV` over `W1`, which
  makes `|Q|` queries at a node.
* The contrast with P1's lazy parent: `attV_empty`. On the empty log the attested node proof is
  rejected (nothing is attested), where `lazy_accepts` accepts the lazy one. The attestation call
  is what ties the list to the log.
* Completeness at a node (`attV_complete`): if both children are accepted on a well-formed log
  with small queries and attested hashes only (`Clean`), the honest node prover certifies the
  concatenation of their lists (`exists_items`), and the node is accepted on the log extended by
  that certification, which stays well formed. Clean accepted runs stay accepted and clean when the
  log grows (`runLog_append_of_clean`), which is what lifts this up a tree.

**Abstraction.** The byte format is a `Codec AFrame AFrame.sub` (P1's `Codec`); `Codec.unary`
inhabits it (`Encodable AFrame`), and `att_W1` holds for every codec, the unary one included.
-/
import RecursionFast.Explore.Attested.Compose
import RecursionFast.Explore.Relativized.Lazy

open scoped NNReal

namespace RecursionFast.Explore.Attested

open Relativized

/-! ## Frames -/

/-- An attestation frame: a child verifier's proof, or a node's two child digests, child proofs
and the list of items the children are judged against. -/
inductive AFrame where
  /-- A proof for the child verifier. -/
  | base (π : Proof)
  /-- A node: the child digests, the child proofs, and a list of items. -/
  | node (c₁ c₂ : Digest) (π₁ π₂ : Proof) (xs : List Item)

/-- The sub-proofs of an attestation frame: a node's two child proofs. -/
def AFrame.sub : AFrame → List Proof
  | .base _ => []
  | .node _ _ π₁ π₂ _ => [π₁, π₂]

instance : Encodable Item := Encodable.ofEquiv ((ByteArray × Digest) ⊕ Digest)
  { toFun := fun | .ans q a => .inl (q, a) | .att h => .inr h
    invFun := fun | .inl (q, a) => .ans q a | .inr h => .att h
    left_inv := fun x => by cases x <;> rfl
    right_inv := fun x => by rcases x with ⟨_, _⟩ | _ <;> rfl }

instance : Encodable AFrame :=
  Encodable.ofEquiv (Proof ⊕ (Digest × Digest × Proof × Proof × List Item))
  { toFun := fun | .base π => .inl π | .node c₁ c₂ π₁ π₂ xs => .inr (c₁, c₂, π₁, π₂, xs)
    invFun := fun | .inl π => .base π | .inr (c₁, c₂, π₁, π₂, xs) => .node c₁ c₂ π₁ π₂ xs
    left_inv := fun f => by cases f <;> rfl
    right_inv := fun f => by rcases f with _ | ⟨_, _, _, _, _⟩ <;> rfl }

variable (C : Codec AFrame AFrame.sub) (Vc : Digest → Proof → AProg Bool) {ε : ℝ≥0}

/-! ## The attesting verifier and its extractor -/

/-- **The attesting verifier**: a base frame is judged by `Vc`; a node frame
`(c₁, c₂, π₁, π₂, xs)` asks once whether `hashList xs` is attested, and accepts when it is, `xs`
is bounded, `c` is the children's node statement, and this verifier accepts both children reading
`xs`. -/
def attV (c : Digest) (π : Proof) : AProg Bool :=
  match _h : C.dec π with
  | some (.base π') => Vc c π'
  | some (.node c₁ c₂ π₁ π₂ xs) =>
    .attest (hashList xs) fun b => .ret (b && decide (Bounded xs) && decide (c = nodeStmt c₁ c₂) &&
      decide ((attV c₁ π₁).runItems xs = some true) &&
      decide ((attV c₂ π₂).runItems xs = some true))
  | none => .ret false
termination_by π.size
decreasing_by all_goals exact C.lt _h _ (by simp [AFrame.sub])

/-- A child extractor's output as an output for the attesting verifier: a node's child proofs
wrapped as base frames. -/
def liftOut : Out → Out
  | .wit (.node c₁ c₂ π₁ π₂) => .wit (.node c₁ c₂ (C.enc (.base π₁)) (C.enc (.base π₂)))
  | o => o

/-- **The attesting extractor**: the child extractor on a base frame; on a node frame, the first
certified list `ys` with the carried list's hash gives the node witness if `ys` is the carried
list, else the collision of the two lists. -/
def attE (Ec : Digest → Proof → ALog → Option Out) (c : Digest) (π : Proof) (L : ALog) :
    Option Out :=
  match C.dec π with
  | some (.base π') => (Ec c π' L).map (liftOut C)
  | some (.node c₁ c₂ π₁ π₂ xs) => (certOf L (hashList xs)).map fun ys =>
      if ys = xs then .wit (.node c₁ c₂ π₁ π₂) else .coll xs ys
  | none => none

theorem attV_base (c : Digest) (π' : Proof) : attV C Vc c (C.enc (.base π')) = Vc c π' := by
  rw [attV]; split <;> simp_all [C.dec_enc]

theorem attV_node (c c₁ c₂ : Digest) (π₁ π₂ : Proof) (xs : List Item) :
    attV C Vc c (C.enc (.node c₁ c₂ π₁ π₂ xs)) = .attest (hashList xs) fun b =>
      .ret (b && decide (Bounded xs) && decide (c = nodeStmt c₁ c₂) &&
        decide ((attV C Vc c₁ π₁).runItems xs = some true) &&
        decide ((attV C Vc c₂ π₂).runItems xs = some true)) := by
  rw [attV]; split <;> simp_all [C.dec_enc]

/-! ## Soundness -/

variable {C Vc}

/-- **Attestation is relativized-sound**: an attested knowledge state for the child verifier gives
the attesting verifier one with the same potential and error, whose extractor returns the node
witness or the collision between the carried and the certified list. -/
def attState {Ec : Digest → Proof → ALog → Option Out} (k : KStateA Vc Ec ε) :
    KStateA (attV C Vc) (attE C Ec) ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  cert := k.cert
  final L c π hW hL hμ h := by
    rw [attV] at h
    split at h
    next π' hd =>
      obtain ⟨o, hE, hS⟩ := k.final L c π' hW hL hμ h
      refine ⟨liftOut C o, by simp [attE, hd, hE], ?_⟩
      rcases o with (⟨s, n⟩ | ⟨c₁, c₂, π₁, π₂⟩) | ⟨x, y⟩
      · exact hS
      · simpa [liftOut, Sound, attV_base] using hS
      · exact hS
    next c₁ c₂ π₁ π₂ xs hd =>
      simp only [AProg.runLog, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, h₁⟩, h₂⟩ := h
      obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp ha
      obtain ⟨hmem, hhash⟩ := certOf_spec hys
      have hv := hW.valid_of_mem hmem
      by_cases hyx : ys = xs
      · subst hyx
        exact ⟨.wit (.node c₁ c₂ π₁ π₂), by simp [attE, hd, hys], hc, runItems_valid hv h₁,
          runItems_valid hv h₂⟩
      · exact ⟨.coll xs ys, by simp [attE, hd, hys, hyx], hb, hv.bounded, Ne.symm hyx, hhash.symm⟩
    next => simp [AProg.runLog] at h

theorem attState_μ {Ec : Digest → Proof → ALog → Option Out} (k : KStateA Vc Ec ε) :
    (attState (C := C) k).μ = k.μ := rfl

/-! ## One call per node -/

variable (C Vc) in
/-- **A node makes one call**: the calls of the attesting verifier on a node frame are exactly
one attestation request for the carried list's hash, under every oracle and attest predicate.
(Contrast `queries_defer`: a re-asking node makes `|Q|` queries.) -/
theorem calls_node (H : ByteArray → Digest) (A : Digest → Bool) (c c₁ c₂ : Digest)
    (π₁ π₂ : Proof) (xs : List Item) :
    (attV C Vc c (C.enc (.node c₁ c₂ π₁ π₂ xs))).calls H A = [.attest (hashList xs)] := by
  rw [attV_node]; rfl

/-- The attesting verifier makes at most `qV ≥ 1` calls when the child verifier does. -/
theorem attV_calls {qV : ℕ} (hq : 1 ≤ qV)
    (h : ∀ H A c π, ((Vc c π).calls H A).length ≤ qV) (H : ByteArray → Digest)
    (A : Digest → Bool) (c : Digest) (π : Proof) : ((attV C Vc c π).calls H A).length ≤ qV := by
  rw [attV]; split
  · exact h H A c _
  · exact hq
  · exact Nat.zero_le _

/-- **`KSA` for the attesting verifier**, with the child's error and call bound. -/
theorem attKSA {Ec : Digest → Proof → ALog → Option Out} {qV : ℕ} (hq : 1 ≤ qV)
    (h : KSA Vc Ec ε qV) : KSA (attV C Vc) (attE C Ec) ε qV :=
  ⟨⟨attState h.1.some⟩, attV_calls hq h.2⟩

/-- The contrast with the lazy parent: on the empty log a node frame is rejected (nothing is
attested), where P1's `lazy_accepts` accepts the lazy node proof. -/
theorem attV_empty (c c₁ c₂ : Digest) (π₁ π₂ : Proof) (xs : List Item) :
    (attV C Vc c (C.enc (.node c₁ c₂ π₁ π₂ xs))).runLog [] = some false := by
  rw [attV_node]; rfl

/-! ## The instance over `W1` -/

/-- P1's `W1` (witness-sending with one dummy query) as an attested verifier. -/
def W1A : Digest → Proof → AProg Bool := liftV W1

/-- `W1` lifted: an attested knowledge state at potential `0`. -/
def w1A : KStateA W1A (liftE WitnessSending.E) 0 := .ofRel w1State

theorem W1_queries (H : ByteArray → Digest) (c : Digest) (π : Proof) :
    ((W1 c π).queries H).length ≤ 1 := by simp [W1, OProg.queries]

theorem w1A_ksa : KSA W1A (liftE WitnessSending.E) 0 1 := KSA.ofRel ⟨⟨w1State⟩, W1_queries⟩

variable (C) in
/-- **The escape, instantiated**: over `W1`, the attesting verifier is attested-knowledge-sound at
error `0` with one call per verification, at every level of the tree. -/
theorem att_W1 : KSA (attV C W1A) (attE C (liftE WitnessSending.E)) 0 1 :=
  attKSA le_rfl w1A_ksa

variable (C) in
/-- The instance holds with the unary codec, so its hypotheses are met. -/
theorem att_W1_unary :
    KSA (attV (Codec.unary AFrame.sub) W1A) (attE (Codec.unary AFrame.sub)
      (liftE WitnessSending.E)) 0 1 := att_W1 _

/-! ## Completeness at a node -/

/-- A run on `L` is **clean** when its queries are small and every attestation request it makes
is answered `true`: the runs whose items an honest prover can certify. -/
def Clean {α : Type} (L : ALog) : AProg α → Prop
  | .ret _ => True
  | .query q k => q.size < 2 ^ 64 ∧ ∀ a, firstAns L q = some a → Clean L (k a)
  | .attest h k => attested L h = true ∧ Clean L (k true)

theorem itemAns_of_mem {ys : List Item} {q : ByteArray} {a : Digest} (h : Item.ans q a ∈ ys) :
    ∃ a', itemAns ys q = some a' := by
  cases hc : itemAns ys q with
  | some a' => exact ⟨a', rfl⟩
  | none => have := List.findSome?_eq_none_iff.mp hc _ h; simp at this

/-- **The items of a clean run**: a list valid on `L` such that every valid list containing it
gives the run's verdict. -/
theorem exists_items {α : Type} {L : ALog} :
    ∀ {p : AProg α} {b : α}, Clean L p → p.runLog L = some b →
      ∃ xs, Valid L xs ∧ ∀ ys, Valid L ys → xs ⊆ ys → p.runItems ys = some b
  | .ret _, _, _, h => ⟨[], by simp [Valid], fun _ _ _ => h⟩
  | .query q k, b, hC, h => by
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hv, hxs⟩ := exists_items (hC.2 a ha) h
    refine ⟨.ans q a :: xs, ?_, fun ys hys hsub => ?_⟩
    · rintro x (_ | ⟨_, hx⟩)
      exacts [⟨hC.1, ha⟩, hv x hx]
    · have hm := hsub List.mem_cons_self
      obtain ⟨a', ha'⟩ := itemAns_of_mem hm
      have : a' = a := by
        have := (hys _ (itemAns_mem ha')).2; rw [ha] at this; exact (Option.some.inj this).symm
      subst this
      simp only [AProg.runItems, ha', Option.bind_some]
      exact hxs ys hys fun x hx => hsub (List.mem_cons_of_mem _ hx)
  | .attest g k, b, hC, h => by
    simp only [AProg.runLog, hC.1] at h
    obtain ⟨xs, hv, hxs⟩ := exists_items hC.2 h
    refine ⟨.att g :: xs, ?_, fun ys hys hsub => ?_⟩
    · rintro x (_ | ⟨_, hx⟩)
      exacts [hC.1, hv x hx]
    · simp only [AProg.runItems, hsub List.mem_cons_self, ite_true]
      exact hxs ys hys fun x hx => hsub (List.mem_cons_of_mem _ hx)

/-- An accepted node frame's run is clean (its one request is answered `true`). -/
theorem clean_attV (hVc : ∀ L c π, (Vc c π).runLog L = some true → Clean L (Vc c π))
    {L : ALog} {c : Digest} {π : Proof} (h : (attV C Vc c π).runLog L = some true) :
    Clean L (attV C Vc c π) := by
  rw [attV] at h ⊢
  split at h
  next => exact hVc L c _ h
  next =>
    simp only [AProg.runLog, Option.some.injEq, Bool.and_eq_true] at h
    exact ⟨h.1.1.1.1, trivial⟩
  next => simp [AProg.runLog] at h

/-- **Completeness at a node**: if both children's runs on a well-formed log are clean and
accepted, the honest node prover certifies a valid list, the log stays well formed, and the node
proof carrying that list is accepted on the extended log. -/
theorem attV_complete {L : ALog} (hW : WF L) {c₁ c₂ : Digest} {π₁ π₂ : Proof}
    (hC₁ : Clean L (attV C Vc c₁ π₁)) (hC₂ : Clean L (attV C Vc c₂ π₂))
    (h₁ : (attV C Vc c₁ π₁).runLog L = some true) (h₂ : (attV C Vc c₂ π₂).runLog L = some true) :
    ∃ xs, Valid L xs ∧ WF (L ++ [.cert xs]) ∧
      (attV C Vc (nodeStmt c₁ c₂) (C.enc (.node c₁ c₂ π₁ π₂ xs))).runLog (L ++ [.cert xs]) =
        some true := by
  obtain ⟨xs₁, hv₁, hr₁⟩ := exists_items hC₁ h₁
  obtain ⟨xs₂, hv₂, hr₂⟩ := exists_items hC₂ h₂
  have hv : Valid L (xs₁ ++ xs₂) := fun x hx => (List.mem_append.mp hx).elim (hv₁ x) (hv₂ x)
  have ha : attested (L ++ [.cert (xs₁ ++ xs₂)]) (hashList (xs₁ ++ xs₂)) = true :=
    attested_iff.mpr ⟨_, by simp, rfl⟩
  refine ⟨xs₁ ++ xs₂, hv, hW.snoc_cert hv, ?_⟩
  rw [attV_node]
  simp [AProg.runLog, ha, hv.bounded, hr₁ _ hv (List.subset_append_left _ _),
    hr₂ _ hv (List.subset_append_right _ _)]

/-- **A clean run keeps its verdict and stays clean when the log grows** (what lifts node
completeness up a tree: children accepted before a certification are still accepted after). -/
theorem runLog_append_of_clean {α : Type} {L : ALog} (S : ALog) :
    ∀ {p : AProg α} {b : α}, Clean L p → p.runLog L = some b →
      p.runLog (L ++ S) = some b ∧ Clean (L ++ S) p
  | .ret _, _, _, h => ⟨h, trivial⟩
  | .query q k, b, hC, h => by
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    have ha' := firstAns_append S ha
    obtain ⟨h', hC'⟩ := runLog_append_of_clean S (hC.2 a ha) h
    refine ⟨by simp only [AProg.runLog, ha', Option.bind_some]; exact h', hC.1, fun a' h'' => ?_⟩
    rw [ha', Option.some.injEq] at h''
    exact h'' ▸ hC'
  | .attest g k, b, hC, h => by
    simp only [AProg.runLog, hC.1] at h
    have hg := attested_append S hC.1
    obtain ⟨h', hC'⟩ := runLog_append_of_clean S hC.2 h
    exact ⟨by simpa only [AProg.runLog, hg] using h', hg, hC'⟩

/-- `W1`'s runs are clean: one query of the empty string. -/
theorem clean_W1A (L : ALog) (c : Digest) (π : Proof) : Clean L (W1A c π) :=
  ⟨by decide, fun _ _ => trivial⟩

end RecursionFast.Explore.Attested

/-
# Exploration: controls for the attested model                                     (UNTRUSTED)

Probe P2, item 5.

**(a) The collision disjunct.**
* `acceptAll_iff`: the verifier that accepts everything, with the extractor that always returns
  `coll x y`, has an attested knowledge state (at any error) **exactly when** `IsColl x y`; so a
  certificate for it with a named pair is a concrete BLAKE2s collision (`acceptAll_blake2s`).
* `final_prop_vacuous`: the proposition form is vacuous. For every verifier, log and accepted
  proof, "a witness exists or a collision exists" holds, by `exists_isColl` (pigeonhole).
* `acceptAll_choice`: naming the pair in the output type is not enough. The extractor that returns
  the `Classical.choose` of `exists_isColl` certifies the accept-all verifier, `KSA` at error `0`
  with no call. What excludes it is the requirement that the extractor be computed by a program
  (v3's `Computes`, not modelled here): a program's output is a concrete pair, and a proof that
  it collides is a BLAKE2s collision.

**(b) Valid lists and well-formed logs.**
* Negative: a certified list with a wrong answer (`wrong_not_wf`), with an answer the log does not
  have (`unasked_not_wf`), with an answer that is not the log's **first** (`shadowed_not_wf`), or
  with an unattested hash (`unattested_not_wf`) makes the log ill formed.
* Positive: `wf₁` (one answer, one certification of it) and `wf₂` (a certification of an attested
  hash on top: recursive attestation) are well formed.

**(c) Witness-sending.** `wsA`, `ws_ksa`: P1's `wsState` lifts to an attested knowledge state at
potential `0` (`wsA_μ`), `KSA` at error `0` with no call.

**(d) The escape is not vacuous.** A depth-2 tree over `W1` leaves, on a concrete well-formed log
of potential `0` (`L₂`: one answer, a certification of a leaf list, a certification of that list's
hash). The root node is accepted (`root_accepts`) with **one** call (`root_calls`), and
`compose_all` applies to it (`root_extracts`): the tree is extracted to every depth or the walk
returns a BLAKE2s collision.

**(e) Why `IsColl` asks for bounded lists.** `enc64` wraps at `2^64`, so `encList` is not
injective on all lists (`encList_not_inj`): a single answer to a query of exactly `2^64` bytes
(its length code reads `0`) has the bytes of a 41-byte answer to the empty query followed by a run
of `att` and `ans` items. So two distinct lists can share a `hashList` with **the same preimage**
(`hashList_not_coll`), which is no BLAKE2s collision. W2 M1 on paper; here in the kernel.
-/
import RecursionFast.Explore.Attested.Escape
import RecursionFast.Explore.Relativized.Concat

open scoped NNReal

namespace RecursionFast.Explore.Attested

open Relativized

/-! ## (a) The collision disjunct -/

/-- The verifier that accepts everything, with no call. -/
def acceptAll (_ : Digest) (_ : Proof) : AProg Bool := .ret true

/-- **The constant-collision extractor certifies the accept-all verifier exactly when its pair is
a list-hash collision.** -/
theorem acceptAll_iff (x y : List Item) (ε : ℝ≥0) :
    Nonempty (KStateA acceptAll (fun _ _ _ => some (.coll x y)) ε) ↔ IsColl x y := by
  constructor
  · rintro ⟨k⟩
    obtain ⟨o, ho, hS⟩ := k.final [] (Vector.replicate 32 0) .empty WF.nil (Nat.zero_le _)
      (by rw [k.empty]; exact one_pos) rfl
    cases ho
    exact hS
  · exact fun h => ⟨.zero ε fun _ _ _ _ _ => ⟨_, rfl, h⟩⟩

/-- So certifying it with a named pair exhibits a BLAKE2s-256 collision. -/
theorem acceptAll_blake2s {x y : List Item} {ε : ℝ≥0}
    (h : Nonempty (KStateA acceptAll (fun _ _ _ => some (.coll x y)) ε)) :
    tagList :: encList x ≠ tagList :: encList y ∧
      blake2s256 (tagList :: encList x) = blake2s256 (tagList :: encList y) :=
  ((acceptAll_iff x y ε).mp h).blake2s

/-- **The proposition form is vacuous**: "a witness or a collision exists" holds for every
verifier and every accepted proof. -/
theorem final_prop_vacuous (V : Digest → Proof → AProg Bool) (L : ALog) (c : Digest)
    (π : Proof) (_ : (V c π).runLog L = some true) :
    (∃ w, RelA V L c w) ∨ ∃ x y, IsColl x y :=
  .inr exists_isColl

/-- A collision pair chosen by `Classical.choose` (it exists by pigeonhole; nobody knows it). -/
noncomputable def chosen : List Item × List Item :=
  (exists_isColl.choose, exists_isColl.choose_spec.choose)

/-- **Naming the pair in the type is not enough**: the extractor returning the chosen pair
certifies the accept-all verifier at error `0` with no call. -/
theorem acceptAll_choice :
    KSA acceptAll (fun _ _ _ => some (.coll chosen.1 chosen.2)) 0 0 :=
  ⟨(acceptAll_iff _ _ 0).mpr exists_isColl.choose_spec.choose_spec, fun _ _ _ _ => le_rfl⟩

/-! ## (b) Valid lists and well-formed logs -/

section
variable (q : ByteArray) (a a' : Digest) (h : Digest)

theorem firstAns_single : firstAns [.ans q a] q = some a := by simp [firstAns, Ev.ansFor]

/-- A certified list with a wrong answer: the log is not well formed. -/
theorem wrong_not_wf (hne : a ≠ a') : ¬ WF [.ans q a', .cert [.ans q a]] := fun hW => by
  have := (hW [.ans q a'] [.ans q a] [] rfl _ List.mem_cons_self).2
  rw [firstAns_single] at this
  exact hne (Option.some.inj this).symm

/-- A certified answer the log does not have: not well formed. -/
theorem unasked_not_wf : ¬ WF [.cert [.ans q a]] := fun hW => by
  have := (hW [] [.ans q a] [] rfl _ List.mem_cons_self).2
  simp [firstAns] at this

/-- A certified answer that is not the log's first: not well formed. -/
theorem shadowed_not_wf (hne : a ≠ a') : ¬ WF [.ans q a, .ans q a', .cert [.ans q a']] :=
  fun hW => by
    have := (hW [.ans q a, .ans q a'] [.ans q a'] [] rfl _ List.mem_cons_self).2
    simp [firstAns, Ev.ansFor] at this
    exact hne this

/-- A certified hash that is not attested: not well formed. -/
theorem unattested_not_wf : ¬ WF [.cert [.att h]] := fun hW => by
  have := hW [] [.att h] [] rfl _ List.mem_cons_self
  simp [Item.OK, attested, certOf] at this

theorem valid₁ (hq : q.size < 2 ^ 64) : Valid [.ans q a] [.ans q a] := by
  rintro x (_ | ⟨_, ⟨⟩⟩); exact ⟨hq, firstAns_single q a⟩

/-- One answer and a certification of it: well formed. -/
theorem wf₁ (hq : q.size < 2 ^ 64) : WF [.ans q a, .cert [.ans q a]] := by
  simpa using (WF.nil.snoc_ans q a).snoc_cert (by simpa using valid₁ q a hq)

theorem valid₂ : Valid [.ans q a, .cert [.ans q a]] [.att (hashList [.ans q a])] := by
  rintro x (_ | ⟨_, ⟨⟩⟩); exact attested_iff.mpr ⟨_, by simp, rfl⟩

/-- A certification of an attested hash on top: well formed (recursive attestation). -/
theorem wf₂ (hq : q.size < 2 ^ 64) :
    WF [.ans q a, .cert [.ans q a], .cert [.att (hashList [.ans q a])]] := by
  simpa using (wf₁ q a hq).snoc_cert (valid₂ q a)

end

/-! ## (c) Witness-sending -/

/-- The witness-sending verifier, lifted: an attested knowledge state at potential `0`. -/
def wsA : KStateA (liftV WitnessSending.V) (liftE WitnessSending.E) 0 := .ofRel wsState

theorem wsA_μ : wsA.μ = fun _ => 0 := rfl

/-- Witness-sending is attested-knowledge-sound at error `0` with no call. -/
theorem ws_ksa : KSA (liftV WitnessSending.V) (liftE WitnessSending.E) 0 0 := KSA.ofRel ws_ksRel

/-! ## (d) The escape is not vacuous: a depth-2 tree over `W1` -/

section
variable (C : Codec AFrame AFrame.sub)

/-- The zero digest, the answer to `W1`'s dummy query in the example. -/
def z : Digest := Vector.replicate 32 0

/-- The leaf node's list: the answer of `W1`'s dummy query. -/
def xs₁ : List Item := [.ans .empty z]

/-- The root's list: the hash of the leaf node's list. -/
def xs₂ : List Item := [.att (hashList xs₁)]

/-- The log: the dummy answer, the leaf node's certification, the root's certification. -/
def L₂ : ALog := [.ans .empty z, .cert xs₁, .cert xs₂]

/-- The inner node: two `W1` leaves of `l₀`, judged against `xs₁`. -/
def π₁ : Proof := C.enc (.node l₀ l₀ (C.enc (.base p₀)) (C.enc (.base p₀)) xs₁)

/-- The root: two copies of the inner node, judged against `xs₂`. -/
def π₂ : Proof := C.enc (.node (nodeStmt l₀ l₀) (nodeStmt l₀ l₀) (π₁ C) (π₁ C) xs₂)

/-- The root statement. -/
def c₂ : Digest := nodeStmt (nodeStmt l₀ l₀) (nodeStmt l₀ l₀)

theorem wf_L₂ : WF L₂ := wf₂ .empty z (by decide)

theorem check_l₀ : WitnessSending.check l₀ p₀ = true := by
  have := W1_accepts; rw [runLog_W1] at this; exact (Option.map_eq_some_iff.mp this).choose_spec.2

theorem leaf_items : (attV C W1A l₀ (C.enc (.base p₀))).runItems xs₁ = some true := by
  rw [attV_base]
  simp [W1A, liftV, W1, OProg.toA, AProg.runItems, itemAns, xs₁, check_l₀]

theorem bounded₁ : Bounded xs₁ := by
  intro x hx; simp only [xs₁, List.mem_singleton] at hx; subst hx; decide

theorem bounded₂ : Bounded xs₂ := by
  intro x hx; simp only [xs₂, List.mem_singleton] at hx; subst hx; rfl

theorem inner_items : (attV C W1A (nodeStmt l₀ l₀) (π₁ C)).runItems xs₂ = some true := by
  rw [π₁, attV_node]
  simp [AProg.runItems, xs₂, leaf_items, bounded₁]

/-- **The root is accepted** on the well-formed log `L₂`. -/
theorem root_accepts : (attV C W1A c₂ (π₂ C)).runLog L₂ = some true := by
  have ha : attested L₂ (hashList xs₂) = true := attested_iff.mpr ⟨_, by simp [L₂], rfl⟩
  rw [π₂, c₂, attV_node]
  simp [AProg.runLog, ha, bounded₂, inner_items]

/-- **The root makes one call** for the whole depth-2 tree. -/
theorem root_calls (H : ByteArray → Digest) (A : Digest → Bool) :
    (attV C W1A c₂ (π₂ C)).calls H A = [.attest (hashList xs₂)] := calls_node C W1A H A _ _ _ _ _ _

/-- **Whole-tree extraction applies**: the attested state over `W1` has potential `0` on `L₂`,
so the root's tree is extracted to every depth or the walk returns a collision. -/
theorem root_extracts :
    (∀ d, TreeOKA (attE C (liftE WitnessSending.E)) L₂ d c₂ (π₂ C)) ∨
      ∃ d x y, collAt (attE C (liftE WitnessSending.E)) L₂ d c₂ (π₂ C) = some (x, y) ∧
        IsColl x y :=
  compose_all (attState (C := C) w1A) wf_L₂ (by decide) (show (0 : ℝ≥0) < 1 from one_pos)
    (root_accepts C)

end

/-! ## (e) The encoding is not injective on unbounded lists -/

theorem enc_ans_empty : (Item.ans .empty z).enc = List.replicate 41 0 := by decide

theorem encList_append (xs ys : List Item) : encList (xs ++ ys) = encList xs ++ encList ys :=
  List.flatMap_append

theorem length_encList_replicate (n : ℕ) (x : Item) :
    (encList (List.replicate n x)).length = n * x.enc.length := by
  simp [encList, List.flatMap_replicate, List.length_flatten, List.sum_replicate]

/-- **`encList` is not injective**: an answer to a `2^64`-byte query re-parses as an answer to the
empty query followed by `39` hash items and `j + 1` empty answers,
`33 · 39 + 41 · (j + 1) = 2^64`. -/
theorem encList_not_inj : ∃ x y : List Item, x ≠ y ∧ encList x = encList y := by
  obtain ⟨j, hj⟩ : ∃ j, 33 * 39 + 41 * (j + 1) = 2 ^ 64 := ⟨(2 ^ 64 - 1328) / 41, by norm_num⟩
  set P := List.replicate 39 (Item.att z) ++ List.replicate j (Item.ans .empty z) with hPdef
  have hP : (encList P).length = 33 * 39 + 41 * j := by
    rw [hPdef, encList_append, List.length_append, length_encList_replicate,
      length_encList_replicate, enc_ans_empty, List.length_replicate]
    simp [Item.enc]; ring
  set q : ByteArray := ⟨(List.replicate 32 0 ++ encList P ++ List.replicate 9 0).toArray⟩ with hqdef
  have hq : q.size = 2 ^ 64 := by
    rw [hqdef, ByteArray.size, List.size_toArray]
    simp only [List.length_append, List.length_replicate, hP]; omega
  refine ⟨[.ans q z], .ans .empty z :: (P ++ [.ans .empty z]), by simp, ?_⟩
  have h64 : enc64 (2 ^ 64) = List.replicate 8 0 := by decide
  have hz : z.toList = List.replicate 32 0 := by decide
  have h9 : List.replicate 9 (0 : UInt8) ++ List.replicate 32 0 = List.replicate 41 0 := rfl
  have hqd : q.data.toList = List.replicate 32 0 ++ encList P ++ List.replicate 9 0 := by
    rw [hqdef]
  rw [encList_cons, encList_nil, List.append_nil, encList_cons, encList_append, encList_cons,
    encList_nil, List.append_nil, enc_ans_empty, Item.enc, hq, h64, hqd, hz]
  simp only [List.append_assoc, h9]
  rfl

/-- **Two distinct lists with one `hashList` and one preimage**: not a BLAKE2s collision, so
`IsColl` must ask for bounded lists. -/
theorem hashList_not_coll : ∃ x y : List Item, x ≠ y ∧ hashList x = hashList y ∧
    tagList :: encList x = tagList :: encList y := by
  obtain ⟨x, y, hne, h⟩ := encList_not_inj
  exact ⟨x, y, hne, by rw [hashList, hashList, h], by rw [h]⟩

end RecursionFast.Explore.Attested

/-
# Exploration: the deterministic core of deferral                                 (UNTRUSTED)

Probe P4, optional item (`docs/explore/notes/T1-impossibility.md` §2.1, §2.2 (b)/(d), §7 item 2).
**A recursive design must re-ask its children's queries.** If the extractor of a relativized
knowledge state is *decoding* (on a node proof it returns the child proofs the proof commits to,
or nothing), then a parent that accepts without reading a query `q` that a committed child's
verification reads contradicts `final` on a log of potential below `1`. Two forms:

* **Log form** (`reask`). `path L p`: the queries `p` asks when its answers are read from `L`.
  `mem_of_runLog` (log coverage, T1 Lemma 2.1): an accepted run's path lies in `L`'s keys.
  `runLog_eraseKey` (locality): removing every entry for a query off the path changes nothing;
  `runLog_eraseKey_of_mem`: removing one on the path makes the run fail. Hence `reask`: on a log
  `L` where the parent accepts, if a committed child's path reads `q` and the log without `q` has
  potential below `1`, the parent's own path reads `q`.
* **Oracle-flip form** (`flip_reask`, T1 Theorem 2.2 (a), (b), (d)). Let the parent accept under the
  flipped oracle `O[q ↦ a]` (completeness gives this for the honest proof built under the flipped
  oracle), let `L` be a log of the true oracle `O` covering the parent's queries under `O`, of
  potential below `1`, and let a committed child be rejected on `L` (answer-sensitive). Then the
  parent asks `q` under `O[q ↦ a]`. The probabilistic half (potential below `1` except with
  probability `(Q + qV) · ε`) is `KStateRel.paper`.

**Teeth** (`lazy_W1_no_kstate'`): `reask` re-derives P1's `lazy_W1_no_kstate`, the lazy parent over
`W1` has no relativized knowledge state with its decoding extractor: its node asks nothing, its
children ask the dummy query.
-/
import RecursionFast.Explore.Relativized.Lazy
import RecursionFast.Library.Oracle

open scoped NNReal

namespace RecursionFast.Explore.Lift
open Relativized

variable {α : Type}

/-! ## Paths, erasure and locality -/

/-- **The path of a program on a log**: the queries it asks when every answer is read from `L`, in
order, up to the first query `L` does not answer (included). -/
def path (L : Log) : OProg α → List ByteArray
  | .ret _ => []
  | .query q k => q :: match L.find? (fun e => e.1 = q) with
    | some e => path L (k e.2)
    | none => []

/-- The log with every entry for the query `q` removed. -/
def eraseKey (L : Log) (q : ByteArray) : Log := L.filter fun e => e.1 ≠ q

theorem length_eraseKey_le (L : Log) (q : ByteArray) : (eraseKey L q).length ≤ L.length :=
  List.length_filter_le _ _

theorem find?_eraseKey_self (L : Log) (q : ByteArray) :
    (eraseKey L q).find? (fun e => e.1 = q) = none := by
  simp [eraseKey, List.find?_eq_none]

theorem find?_eraseKey_ne {q q' : ByteArray} (h : q' ≠ q) (L : Log) :
    (eraseKey L q).find? (fun e => e.1 = q') = L.find? (fun e => e.1 = q') := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    by_cases he : e.1 = q
    · have : e.1 ≠ q' := fun h' => h (h' ▸ he)
      simp_all [eraseKey]
    · by_cases he' : e.1 = q' <;> simp_all [eraseKey]

/-- **Log coverage** (T1 Lemma 2.1): every query on the path of a run accepted on `L` is answered
by `L`. -/
theorem mem_of_runLog {L : Log} {b : α} {p : OProg α} (h : p.runLog L = some b) :
    ∀ q ∈ path L p, q ∈ L.map Prod.fst := by
  induction p with
  | ret a => simp [path]
  | query q' k ih =>
    obtain ⟨e, he, hk⟩ := Option.bind_eq_some_iff.mp h
    intro q hq
    simp only [path, he, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact List.mem_map.mpr ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he⟩
    · exact ih e.2 hk q hq

/-- **Locality**: removing every entry for a query off the path changes nothing. -/
theorem runLog_eraseKey {L : Log} {q : ByteArray} {p : OProg α} (h : q ∉ path L p) :
    p.runLog (eraseKey L q) = p.runLog L := by
  induction p with
  | ret a => rfl
  | query q' k ih =>
    have hne : q' ≠ q := by rintro rfl; exact h (by simp [path])
    simp only [OProg.runLog, find?_eraseKey_ne hne]
    cases he : L.find? (fun e => e.1 = q') with
    | none => rfl
    | some e =>
      simp only [path, he, List.mem_cons, not_or] at h
      exact ih e.2 h.2

/-- Removing the entries for a query on the path makes the run fail. -/
theorem runLog_eraseKey_of_mem {L : Log} {q : ByteArray} {p : OProg α} (h : q ∈ path L p) :
    p.runLog (eraseKey L q) = none := by
  induction p with
  | ret a => simp [path] at h
  | query q' k ih =>
    by_cases hq : q' = q
    · subst hq; simp [OProg.runLog, find?_eraseKey_self]
    · simp only [OProg.runLog, find?_eraseKey_ne hq]
      cases he : L.find? (fun e => e.1 = q') with
      | none => simp [path, he, Ne.symm hq] at h
      | some e => exact ih e.2 (by simpa [path, he, Ne.symm hq] using h)

/-! ## Decoding extractors re-ask -/

variable {V : Digest → Proof → OProg Bool} {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0}
  {children : Proof → Option (Digest × Digest × Proof × Proof)}

/-- **A decoding extractor** for the child parser `children`: on a proof that commits to children,
it returns nothing or the node witness of exactly those children. -/
def Decoding (E : Digest → Proof → Log → Option Wit)
    (children : Proof → Option (Digest × Digest × Proof × Proof)) : Prop :=
  ∀ c π L c₁ c₂ π₁ π₂ w, children π = some (c₁, c₂, π₁, π₂) → E c π L = some w →
    w = .node c₁ c₂ π₁ π₂

/-- **The parent re-asks** (log form): on a log where the parent accepts, if a committed child's
path reads `q` and the log without `q` is within `logCap` and below potential `1`, a decoding
extractor forces the parent's own path to read `q`. -/
theorem reask (k : KStateRel V E ε) (hE : Decoding E children) {c c₁ c₂ : Digest}
    {π π₁ π₂ : Proof} (hπ : children π = some (c₁, c₂, π₁, π₂)) {L : Log} {q : ByteArray}
    (hq : q ∈ path L (V c₁ π₁) ∨ q ∈ path L (V c₂ π₂)) (hacc : (V c π).runLog L = some true)
    (hlen : L.length ≤ logCap) (hμ : k.μ (eraseKey L q) < 1) : q ∈ path L (V c π) := by
  by_contra hp
  obtain ⟨w, hw, hrel⟩ := k.final _ c π ((length_eraseKey_le L q).trans hlen) hμ
    ((runLog_eraseKey hp).trans hacc)
  obtain rfl := hE _ _ _ _ _ _ _ _ hπ hw
  obtain ⟨-, h₁, h₂⟩ := hrel
  rcases hq with hq | hq
  · rw [runLog_eraseKey_of_mem hq] at h₁; cases h₁
  · rw [runLog_eraseKey_of_mem hq] at h₂; cases h₂

/-- A program's verdict and queries depend only on the oracle's answers at the points it asks. -/
theorem run_congr {H H' : ByteArray → Digest} {p : OProg α} (h : ∀ q ∈ p.queries H, H q = H' q) :
    p.run H = p.run H' ∧ p.queries H = p.queries H' := by
  induction p with
  | ret a => exact ⟨rfl, rfl⟩
  | query q k ih =>
    have hq : H q = H' q := h q (List.mem_cons_self ..)
    obtain ⟨h₁, h₂⟩ := ih (H q) fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    simp only [OProg.run, OProg.queries, ← hq, h₁, h₂, and_self]

/-- **The parent re-asks** (oracle-flip form, T1 Theorem 2.2 (a), (b), (d)): if the parent accepts
under the flipped oracle `O[q ↦ a]`, a log `L` of the true oracle `O` covers the parent's queries
and is within `logCap` below potential `1`, and a committed child is rejected on `L`, then a
decoding extractor forces the parent to ask `q` under the flipped oracle. -/
theorem flip_reask (k : KStateRel V E ε) (hE : Decoding E children) {c c₁ c₂ : Digest}
    {π π₁ π₂ : Proof} (hπ : children π = some (c₁, c₂, π₁, π₂)) {L : Log}
    (hsens : (V c₁ π₁).runLog L ≠ some true ∨ (V c₂ π₂).runLog L ≠ some true)
    {O : ByteArray → Digest} {q : ByteArray} {a : Digest}
    (hacc : (V c π).run (Function.update O q a) = true) (hL : ∀ e ∈ L, e.2 = O e.1)
    (hcov : ∀ q' ∈ (V c π).queries O, q' ∈ L.map Prod.fst) (hlen : L.length ≤ logCap)
    (hμ : k.μ L < 1) : q ∈ (V c π).queries (Function.update O q a) := by
  by_contra hq
  have hrun : (V c π).run (Function.update O q a) = (V c π).run O :=
    (run_congr (H := Function.update O q a) (H' := O) fun q' hq' =>
      Function.update_of_ne (β := fun _ => Digest) (by rintro rfl; exact hq hq') a O).1
  have h := (V c π).runLog_eq_run hL hcov
  rw [← hrun, hacc] at h
  obtain ⟨w, hw, hrel⟩ := k.final L c π hlen hμ h
  obtain rfl := hE _ _ _ _ _ _ _ _ hπ hw
  rcases hsens with h₁ | h₂
  exacts [h₁ hrel.2.1, h₂ hrel.2.2]

/-! ## Teeth: the lazy parent -/

/-- The children a deferral frame commits to. -/
def dChildren (C : Codec DFrame DFrame.sub) (π : Proof) :
    Option (Digest × Digest × Proof × Proof) :=
  match C.dec π with
  | some (.defer c₁ c₂ π₁ π₂ _) => some (c₁, c₂, π₁, π₂)
  | _ => none

/-- P1's natural extractor of the node verifiers is decoding. -/
theorem dE_decoding (C : Codec DFrame DFrame.sub) (E : Digest → Proof → Log → Option Wit) :
    Decoding (dE C E) (dChildren C) := by
  intro c π L c₁ c₂ π₁ π₂ w hπ hw
  unfold dChildren at hπ
  unfold dE at hw
  split at hπ
  next _ _ _ _ _ hd => rw [hd] at hw; simp_all
  next => cases hπ

/-- **`reask` has teeth**: it re-derives P1's `lazy_W1_no_kstate`. The lazy node over two `W1`
leaf proofs asks nothing, its children ask the dummy query `.empty`, and the log without that
query is empty (potential `0`), so no relativized knowledge state exists with the decoding
extractor. -/
theorem lazy_W1_no_kstate' (C : Codec DFrame DFrame.sub) (ε : ℝ≥0) :
    ¬ Nonempty (KStateRel (lazyV C W1) (dE C WitnessSending.E) ε) := by
  rintro ⟨k⟩
  let L : Log := [(.empty, Vector.replicate 32 0)]
  have hacc : (lazyV C W1 (nodeStmt l₀ l₀) (nodeProof C l₀ l₀ p₀ p₀ L)).runLog L = some true := by
    have := W1_accepts
    simp [nodeProof, lazyV_defer, lazyV_base, OProg.runLog, this, L]
  have hpath := reask k (dE_decoding C _) (c₁ := l₀) (c₂ := l₀) (π₁ := C.enc (.base p₀))
    (π₂ := C.enc (.base p₀)) (by simp [dChildren, nodeProof, C.dec_enc])
    (q := .empty) (Or.inl (by simp [lazyV_base, W1, path])) hacc (by decide)
    (by simp [L, eraseKey, k.empty])
  simp [nodeProof, lazyV_defer, path] at hpath

end RecursionFast.Explore.Lift

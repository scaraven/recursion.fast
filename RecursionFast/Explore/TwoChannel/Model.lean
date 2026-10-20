/-
# Exploration P3: the two-channel model (W5, the channel split)                     (UNTRUSTED)

Branch `explore/relativized-nark`, probe P3 (`docs/explore/notes/W1-workarounds.md` §7). Two
oracles: a **secret** one for challenges (deployed as a keyed PRF the submitter cannot evaluate)
and **public** BLAKE2s for commitments, computed by anyone.

* **Logs.** `Entry.sec q a` is the secret oracle's answer `a` to `q`; `Entry.pub m a` is a BLAKE2s
  evaluation of the bytes `m`. `pubConsistent L`: every `pub` entry is right, `a = BLAKE2s m`. Only
  `sec` answers are random.
* **Programs.** `TProg` has two query constructors. `runLog L` answers a `sec` query from the first
  `sec` entry for it and a `pub` query from the first `pub` entry for it (`none` if absent), so a
  verifier's BLAKE2s evaluations are part of the log the extractor reads, as v3's verifier queries
  are part of the final log. `run O` answers `sec` with the secret oracle `O` and `pub` with
  BLAKE2s. `runLog_run`: on a consistent log a verdict is the deployment verdict under every `O`
  that agrees with the log's `sec` entries. **On the public channel the model and the deployment
  cannot differ.** (W1 §7.1 has `runLog` read only `sec` entries, with the verifier hashing
  outside the log. A Merkle verifier written that way has no knowledge state:
  `Merkle.pure_no_kstate`. This is the first deviation, see the note.)
* **Escapes as data.** The extractor returns `W ⊕ Esc`: a witness, or an escape that names entries
  of the log. `Esc.col m m' a`: two distinct `pub` inputs with the same output, both in the log
  (`Collision`). `Esc.late j m a`: the digest `a` occurs in the input of entry `j`, no entry up to
  `j` produces it, and a later `pub` entry does (`LatePre`, a preimage found after its digest was
  used: the event preimage awareness excludes). The bare proposition "BLAKE2s has a collision" is
  true by pigeonhole (`blake2s_collides`), so an escape must point into the log: otherwise `final`
  would be vacuous. `Mode.col` allows collisions only (W1 §7.1's `final`); `Mode.colLate` also late
  preimages. `escSearch` finds a valid escape whenever one exists (`escSearch_sound`,
  `escSearch_complete`).
* **Knowledge states.** `KState2 mode R V E ε`: a potential `μ` with `empty`; `step` for a fresh
  `sec` query on a consistent log (average rise at most `ε` over the `2^256` answers, within
  `logCap` counted in `sec` entries); **`pubStep`**: a consistent `pub` entry never raises `μ`;
  `final`: on a consistent log below potential `1` every proof `V` accepts is extracted to a
  witness or a valid escape.
  `KState2W` is the same with the fallback `pubStep` ("or the new entry completes a collision");
  `KState2.toW`. Negative results are stated for `KState2W`, so they hold for both forms.
* **Builder.** `KState2.ofHist bad`: the potential `1` on logs in which some `sec` answer was bad
  for the log before it, `0` elsewhere. Its `pubStep` holds with equality (`ofHist_pub`): a `pub`
  entry adds no secret answer and changes no earlier prefix. `step` needs a bound on the bad
  answers per query; `final` is the content.
* **Tools for negative results.** `KState2W.le_of_pubTail` (a run of consistent evaluations that
  completes no collision never raises the potential), `final_tail`, `card_le` (from a log of
  potential `0`, at most `ε · 2^256` answers to a fresh query force the potential to `1`),
  `one_le_of_fail` (if after every answer some evaluations make `V` accept a proof the extractor
  does not open, then `ε ≥ 1`), `exists_valid` (the same argument for an arbitrary extractor:
  some answer leads to a log on which it returns a valid output), `pre_snoc_sec`,
  `EscValid.of_snoc_sec` (a final secret answer changes no preimage and adds no escape).

No proof here unfolds `blake2sDigest`: every result holds for any public hash function.
-/
import RecursionFast.Library.Security

open scoped NNReal

namespace RecursionFast.Explore.TwoChannel
open RecursionFast

/-! ## Logs -/

/-- An entry of a two-channel log: the secret oracle's answer `a` to the query `q`, or a public
BLAKE2s evaluation of the bytes `m` with output `a`. -/
inductive Entry where
  /-- The secret oracle answered `q` with `a`. -/
  | sec (q : List UInt8) (a : Digest)
  /-- BLAKE2s of `m` was evaluated, with output `a`. -/
  | pub (m : List UInt8) (a : Digest)
  deriving DecidableEq

/-- A two-channel log: entries in the order they were made. -/
abbrev Log2 := List Entry

/-- The input bytes of an entry: the query or the hashed message. -/
def Entry.input : Entry → List UInt8
  | .sec q _ => q
  | .pub m _ => m

/-- The digest a `pub` entry produces; a secret answer produces nothing. -/
def Entry.out : Entry → Option Digest
  | .sec _ _ => none
  | .pub _ a => some a

/-- Every `pub` entry of the log is a correct BLAKE2s evaluation. -/
def pubConsistent (L : Log2) : Prop := ∀ m a, Entry.pub m a ∈ L → a = blake2sDigest m

/-- The answer of a `sec` entry for the query `q`. -/
def secPick (q : List UInt8) : Entry → Option Digest
  | .sec q' a => if q' = q then some a else none
  | .pub _ _ => none

/-- The output of a `pub` entry for the message `m`. -/
def pubPick (m : List UInt8) : Entry → Option Digest
  | .pub m' a => if m' = m then some a else none
  | .sec _ _ => none

/-- The input of a `pub` entry producing `a`. -/
def prePick (a : Digest) : Entry → Option (List UInt8)
  | .pub m b => if b = a then some m else none
  | .sec _ _ => none

/-- The query of a `sec` entry. -/
def secQ : Entry → Option (List UInt8)
  | .sec q _ => some q
  | .pub _ _ => none

/-- The first answer the log gives to the secret query `q`. -/
def secAns (L : Log2) (q : List UInt8) : Option Digest := L.findSome? (secPick q)

/-- The first output the log records for BLAKE2s of `m`. -/
def pubAns (L : Log2) (m : List UInt8) : Option Digest := L.findSome? (pubPick m)

/-- The first logged BLAKE2s input whose output is `a` (its preimage, as the log knows it). -/
def pre (L : Log2) (a : Digest) : Option (List UInt8) := L.findSome? (prePick a)

/-- The secret queries of the log. -/
def secQueries (L : Log2) : List (List UInt8) := L.filterMap secQ

/-- The number of secret entries: the length the length guard counts. -/
def secCount (L : Log2) : ℕ := (secQueries L).length

theorem mem_of_findSome? {β : Type} {f : Entry → Option β} {L : Log2} {b : β}
    (h : L.findSome? f = some b) : ∃ x ∈ L, f x = some b := by
  obtain ⟨l₁, x, l₂, rfl, hx, -⟩ := List.findSome?_eq_some_iff.mp h
  exact ⟨x, by simp, hx⟩

theorem secAns_mem {L : Log2} {q : List UInt8} {a : Digest} (h : secAns L q = some a) :
    Entry.sec q a ∈ L := by
  obtain ⟨x, hx, hf⟩ := mem_of_findSome? h
  cases x with
  | sec q' a' => simp only [secPick] at hf; split_ifs at hf with hq; cases hf; subst hq; exact hx
  | pub _ _ => cases hf

theorem pubAns_mem {L : Log2} {m : List UInt8} {a : Digest} (h : pubAns L m = some a) :
    Entry.pub m a ∈ L := by
  obtain ⟨x, hx, hf⟩ := mem_of_findSome? h
  cases x with
  | pub m' a' => simp only [pubPick] at hf; split_ifs at hf with hq; cases hf; subst hq; exact hx
  | sec _ _ => cases hf

theorem prePick_eq_some {a : Digest} {x : Entry} {m : List UInt8} :
    prePick a x = some m ↔ x = .pub m a := by
  cases x with
  | pub m' b => simp only [prePick]; split_ifs with h <;> simp_all [eq_comm]
  | sec _ _ => simp [prePick]

theorem prePick_eq_none {a : Digest} {x : Entry} : prePick a x = none ↔ x.out ≠ some a := by
  cases x with
  | pub m' b => simp only [prePick, Entry.out]; split_ifs with h <;> simp [h]
  | sec _ _ => simp [prePick, Entry.out]

theorem pre_mem {L : Log2} {a : Digest} {m : List UInt8} (h : pre L a = some m) :
    Entry.pub m a ∈ L := by
  obtain ⟨x, hx, hf⟩ := mem_of_findSome? h
  rwa [prePick_eq_some.mp hf] at hx

/-- No entry of `L` produces `a` exactly when `L` knows no preimage of `a`. -/
theorem pre_eq_none {L : Log2} {a : Digest} : pre L a = none ↔ ∀ x ∈ L, x.out ≠ some a := by
  simp only [pre, List.findSome?_eq_none_iff, prePick_eq_none]

/-- A preimage known to a prefix is the one the whole log knows. -/
theorem pre_append {A B : Log2} {a : Digest} {m : List UInt8} (h : pre A a = some m) :
    pre (A ++ B) a = some m := by
  simp [pre, List.findSome?_append] at h ⊢; simp [h]

/-- A logged evaluation producing `a` gives `a` a first preimage in the log. -/
theorem pre_of_mem {L : Log2} {m : List UInt8} {a : Digest} (h : Entry.pub m a ∈ L) :
    ∃ m', pre L a = some m' := by
  cases hp : pre L a with
  | some m' => exact ⟨m', rfl⟩
  | none => exact absurd rfl (pre_eq_none.mp hp _ h)

/-- The first preimage splits the log at the entry that produced it. -/
theorem pre_split {L : Log2} {a : Digest} {m : List UInt8} (h : pre L a = some m) :
    ∃ A B, L = A ++ Entry.pub m a :: B ∧ pre A a = none := by
  obtain ⟨A, x, B, rfl, hx, hA⟩ := List.findSome?_eq_some_iff.mp h
  exact ⟨A, B, by rw [prePick_eq_some.mp hx], List.findSome?_eq_none_iff.mpr hA⟩

/-- The first answer to a secret query splits the log at that entry. -/
theorem secAns_split {L : Log2} {q : List UInt8} {a : Digest} (h : secAns L q = some a) :
    ∃ A B, L = A ++ Entry.sec q a :: B := by
  obtain ⟨A, x, B, rfl, hx, -⟩ := List.findSome?_eq_some_iff.mp h
  cases x with
  | sec q' a' =>
    simp only [secPick] at hx; split_ifs at hx with hq; cases hx; subst hq; exact ⟨A, B, rfl⟩
  | pub _ _ => cases hx

/-! ## Two-channel programs -/

/-- A computation that asks the secret oracle (`sec`) and evaluates BLAKE2s (`pub`). -/
inductive TProg (α : Type) where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Ask the secret oracle `q`, continue with its answer. -/
  | sec (q : List UInt8) (k : Digest → TProg α)
  /-- Evaluate BLAKE2s on `m`, continue with the digest. -/
  | pub (m : List UInt8) (k : Digest → TProg α)

namespace TProg
variable {α : Type}

/-- The result when every query is answered from the log: a secret query from its first `sec`
entry, an evaluation from its first `pub` entry; `none` if the log lacks one. -/
def runLog (L : Log2) : TProg α → Option α
  | ret a => some a
  | sec q k => (secAns L q).bind fun a => (k a).runLog L
  | pub m k => (pubAns L m).bind fun a => (k a).runLog L

/-- The result in deployment: the secret oracle is `O`, the public channel is BLAKE2s. -/
def run (O : List UInt8 → Digest) : TProg α → α
  | ret a => a
  | sec q k => (k (O q)).run O
  | pub m k => (k (blake2sDigest m)).run O

/-- **No divergence on the public channel**: a verdict read from a consistent log is the
deployment verdict under every secret oracle that agrees with the log's `sec` entries. -/
theorem runLog_run {O : List UInt8 → Digest} {L : Log2} (hpub : pubConsistent L)
    (hsec : ∀ q a, Entry.sec q a ∈ L → O q = a) {p : TProg α} {b : α}
    (h : p.runLog L = some b) : p.run O = b := by
  induction p with
  | ret a => exact Option.some.inj h
  | sec q k ih =>
    obtain ⟨a, ha, hk⟩ := Option.bind_eq_some_iff.mp h
    rw [run, hsec q a (secAns_mem ha)]; exact ih a hk
  | pub m k ih =>
    obtain ⟨a, ha, hk⟩ := Option.bind_eq_some_iff.mp h
    rw [run, ← hpub m a (pubAns_mem ha)]; exact ih a hk

end TProg

/-! ## Escapes -/

/-- Which escapes `final` allows: collisions only (W1 §7.1), or collisions and late preimages. -/
inductive Mode where
  /-- Collisions in the log only. -/
  | col
  /-- Collisions and late preimages in the log. -/
  | colLate
  deriving DecidableEq

/-- An escape the extractor may return in place of a witness, naming entries of the log. -/
inductive Esc where
  /-- `m ≠ m'` were both evaluated with output `a`. -/
  | col (m m' : List UInt8) (a : Digest)
  /-- `a` occurs in the input of entry `j`, nothing up to `j` produces it, and the later entry
  `pub m a` does. -/
  | late (j : ℕ) (m : List UInt8) (a : Digest)
  deriving DecidableEq

/-- The digest `a` occurs (as 32 consecutive bytes) in the input of entry `j`. -/
def occursAt (L : Log2) (j : ℕ) (a : Digest) : Bool :=
  match L[j]? with
  | some e => decide (a.toList <:+: e.input)
  | none => false

/-- **A valid escape** of the log: a collision between two logged evaluations, or (in mode
`colLate`) a late preimage, a logged evaluation producing a digest that an earlier entry's input
contains while no entry up to that one produced it. -/
def EscValid (mode : Mode) (L : Log2) : Esc → Prop
  | .col m m' a => m ≠ m' ∧ Entry.pub m a ∈ L ∧ Entry.pub m' a ∈ L
  | .late j m a => mode = .colLate ∧ occursAt L j a = true ∧
      (∀ x ∈ L.take (j + 1), x.out ≠ some a) ∧ Entry.pub m a ∈ L.drop (j + 1)

instance (mode : Mode) (L : Log2) : DecidablePred (EscValid mode L)
  | .col _ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .late _ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The log contains a BLAKE2s collision between two of its evaluations. -/
def Collision (L : Log2) : Prop := ∃ m m' a, EscValid .col L (.col m m' a)

/-- The log contains a late preimage. -/
def LatePre (L : Log2) : Prop := ∃ j m a, EscValid .colLate L (.late j m a)

/-- **Why an escape must point into the log**: BLAKE2s has collisions (pigeonhole: infinitely
many inputs, `2^256` outputs), so "witness or a BLAKE2s collision" with the collision a bare
proposition would make every `final` true. -/
theorem blake2s_collides : ∃ m m' : List UInt8, m ≠ m' ∧ blake2sDigest m = blake2sDigest m' := by
  by_contra h
  push Not at h
  exact not_injective_infinite_finite blake2sDigest fun m m' e => by_contra fun hne => h m m' hne e

/-- What the extractor returns is valid: a witness of `R` for the statement, or a valid escape. -/
def Valid {W : Type} (mode : Mode) (R : Digest → W → Prop) (c : Digest) (L : Log2) :
    W ⊕ Esc → Prop
  | .inl w => R c w
  | .inr e => EscValid mode L e

/-- A collision candidate from two entries. -/
def colCand : Entry → Entry → Option Esc
  | .pub m a, .pub m' _ => some (.col m m' a)
  | _, _ => none

/-- A late-preimage candidate at entry `j` from a later evaluation. -/
def lateCand (j : ℕ) : Entry → Option Esc
  | .pub m a => some (.late j m a)
  | .sec _ _ => none

/-- Every escape a log could have: a finite list read off the log. -/
def escCands (L : Log2) : List Esc :=
  (L.flatMap fun x => L.filterMap (colCand x)) ++
    ((List.range L.length).flatMap fun j => L.filterMap (lateCand j))

/-- **The escape search**: the first valid escape among the candidates. -/
def escSearch (mode : Mode) (L : Log2) : Option Esc :=
  (escCands L).find? fun e => decide (EscValid mode L e)

theorem escSearch_sound {mode : Mode} {L : Log2} {e : Esc} (h : escSearch mode L = some e) :
    EscValid mode L e := by
  unfold escSearch at h; simpa using List.find?_some h

theorem mem_escCands {mode : Mode} {L : Log2} {e : Esc} (h : EscValid mode L e) :
    e ∈ escCands L := by
  cases e with
  | col m m' a =>
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, h.2.1, ?_⟩)
    exact List.mem_filterMap.mpr ⟨_, h.2.2, rfl⟩
  | late j m a =>
    obtain ⟨-, hj, -, hm⟩ := h
    have hlt : j < L.length := by
      by_contra hn
      simp [occursAt, List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hj
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hlt, ?_⟩)
    exact List.mem_filterMap.mpr ⟨_, List.mem_of_mem_drop hm, rfl⟩

/-- The search finds a valid escape whenever the log has one. -/
theorem escSearch_complete {mode : Mode} {L : Log2} {e : Esc} (h : EscValid mode L e) :
    ∃ e', escSearch mode L = some e' := by
  have : (escSearch mode L).isSome := List.find?_isSome.mpr ⟨e, mem_escCands h, decide_eq_true h⟩
  exact Option.isSome_iff_exists.mp this

/-- A late preimage from a split of the log: `a` occurs in `e`, nothing in `A` or `e` produces it,
and `pub m a` comes after `e`. -/
theorem late_valid {A B : Log2} {e : Entry} {m : List UInt8} {a : Digest}
    (ho : a.toList <:+: e.input) (hA : ∀ x ∈ A, x.out ≠ some a) (he : e.out ≠ some a)
    (hm : Entry.pub m a ∈ B) : EscValid .colLate (A ++ e :: B) (.late A.length m a) := by
  refine ⟨rfl, by simp [occursAt, ho], fun x hx => ?_, by
    rw [List.drop_length_add_append]; simpa using hm⟩
  rw [List.take_length_add_append] at hx
  simp only [List.take_succ_cons, List.take_zero] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hA x hx
  · rw [List.mem_singleton.mp hx]; exact he

/-- A secret answer at the end of a log changes no preimage. -/
theorem pre_snoc_sec (L : Log2) (q : List UInt8) (a x : Digest) :
    pre (L ++ [.sec q a]) x = pre L x := by
  simp [pre, List.findSome?_append, prePick]

/-- A secret answer at the end of a log adds no escape. -/
theorem EscValid.of_snoc_sec {mode : Mode} {L : Log2} {q : List UInt8} {a : Digest} {e : Esc}
    (h : EscValid mode (L ++ [.sec q a]) e) : EscValid mode L e := by
  cases e with
  | col m m' b =>
    obtain ⟨hne, h1, h2⟩ := h
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h1 h2
    exact ⟨hne, h1, h2⟩
  | late j m b =>
    obtain ⟨hm, ho, hA, hB⟩ := h
    by_cases hj : j + 1 ≤ L.length
    · rw [List.drop_append_of_le_length hj] at hB
      rw [List.take_append_of_le_length hj] at hA
      have ho' : occursAt L j b = true := by
        simpa [occursAt, List.getElem?_append_left (by omega : j < L.length)] using ho
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hB
      exact ⟨hm, ho', hA, hB⟩
    · have : (L ++ [Entry.sec q a]).drop (j + 1) = [] :=
        List.drop_eq_nil_of_le (by simp; omega)
      simp [this] at hB

/-! ## Knowledge states -/

variable {W Pf : Type}

/-- **A two-channel knowledge state** with per-query error `ε` and escapes `mode`, for the
relation `R`, the verifier `V` and the extractor `E`. -/
structure KState2 (mode : Mode) (R : Digest → W → Prop) (V : Digest → Pf → TProg Bool)
    (E : Digest → Pf → Log2 → Option (W ⊕ Esc)) (ε : ℝ≥0) where
  /-- The potential of a log; below `1`, no accepted proof escapes the extractor. -/
  μ : Log2 → ℝ≥0
  /-- The empty log has potential `0`. -/
  empty : μ [] = 0
  /-- On a consistent log within `logCap` secret entries and below `1`, a fresh secret query
  raises the potential by at most `ε` on average over its `2^256` answers. -/
  step : ∀ L q, pubConsistent L → secCount L < logCap → μ L < 1 → q ∉ secQueries L →
    ∑ a : Digest, μ (L ++ [.sec q a]) ≤ (μ L + ε) * 2 ^ 256
  /-- **A consistent BLAKE2s evaluation never raises the potential.** -/
  pubStep : ∀ L m a, pubConsistent (L ++ [.pub m a]) → μ (L ++ [.pub m a]) ≤ μ L
  /-- On a consistent log within `logCap` and below `1`, every proof the verifier accepts on the
  log is extracted to a witness or a valid escape. -/
  final : ∀ L c π, pubConsistent L → secCount L ≤ logCap → μ L < 1 →
    (V c π).runLog L = some true → ∃ o, E c π L = some o ∧ Valid mode R c L o

/-- `KState2` with the **fallback** `pubStep`: a consistent evaluation never raises the potential
unless it completes a collision. -/
structure KState2W (mode : Mode) (R : Digest → W → Prop) (V : Digest → Pf → TProg Bool)
    (E : Digest → Pf → Log2 → Option (W ⊕ Esc)) (ε : ℝ≥0) where
  /-- The potential of a log. -/
  μ : Log2 → ℝ≥0
  /-- The empty log has potential `0`. -/
  empty : μ [] = 0
  /-- As `KState2.step`. -/
  step : ∀ L q, pubConsistent L → secCount L < logCap → μ L < 1 → q ∉ secQueries L →
    ∑ a : Digest, μ (L ++ [.sec q a]) ≤ (μ L + ε) * 2 ^ 256
  /-- A consistent evaluation never raises the potential, or it completes a collision. -/
  pubStep : ∀ L m a, pubConsistent (L ++ [.pub m a]) →
    μ (L ++ [.pub m a]) ≤ μ L ∨ Collision (L ++ [.pub m a])
  /-- As `KState2.final`. -/
  final : ∀ L c π, pubConsistent L → secCount L ≤ logCap → μ L < 1 →
    (V c π).runLog L = some true → ∃ o, E c π L = some o ∧ Valid mode R c L o

variable {mode : Mode} {R : Digest → W → Prop} {V : Digest → Pf → TProg Bool}
  {E : Digest → Pf → Log2 → Option (W ⊕ Esc)} {ε : ℝ≥0}

/-- The strong form gives the fallback form. -/
def KState2.toW (k : KState2 mode R V E ε) : KState2W mode R V E ε :=
  ⟨k.μ, k.empty, k.step, fun L m a h => .inl (k.pubStep L m a h), k.final⟩

/-- Escapes allowed under `col` are allowed under `colLate`. -/
theorem Valid.toColLate {c : Digest} {L : Log2} {o : W ⊕ Esc} (h : Valid .col R c L o) :
    Valid .colLate R c L o := by
  rcases o with w | (⟨m, m', a⟩ | ⟨j, m, a⟩)
  exacts [h, h, absurd h.1 (by decide)]

/-- A collision-only state is a state with both escapes. -/
def KState2W.toColLate (k : KState2W .col R V E ε) : KState2W .colLate R V E ε :=
  ⟨k.μ, k.empty, k.step, k.pubStep, fun L c π h1 h2 h3 h4 => by
    obtain ⟨o, ho, hv⟩ := k.final L c π h1 h2 h3 h4; exact ⟨o, ho, hv.toColLate⟩⟩

/-! ## Potentials that price each secret answer against the log before it -/

/-- Some secret answer of the log was **bad** for the log before it. -/
def BadLog (bad : Log2 → List UInt8 → Digest → Prop) (L : Log2) : Prop :=
  ∃ A q a B, L = A ++ .sec q a :: B ∧ bad A q a

variable {bad : Log2 → List UInt8 → Digest → Prop}

theorem badLog_mono {bad' : Log2 → List UInt8 → Digest → Prop} (h : ∀ L q a, bad L q a → bad' L q a)
    {L : Log2} : BadLog bad L → BadLog bad' L
  | ⟨A, q, a, B, hL, hb⟩ => ⟨A, q, a, B, hL, h _ _ _ hb⟩

/-- Splitting a log with one more entry at the end: the split is inside the old log, or at the new
entry. -/
theorem split_snoc {L A B : Log2} {x y : Entry} (h : L ++ [x] = A ++ y :: B) :
    (∃ B', B = B' ++ [x] ∧ L = A ++ y :: B') ∨ (B = [] ∧ L = A ∧ x = y) := by
  rcases List.eq_nil_or_concat B with rfl | ⟨B', z, rfl⟩
  · right
    have : L = A ∧ x = y := by simpa using h
    exact ⟨rfl, this⟩
  · left
    have h' : L ++ [x] = (A ++ y :: B') ++ [z] := by simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h2
    exact ⟨B', by simp, h1⟩

/-- A `pub` entry at the end adds no bad secret answer. -/
theorem badLog_pub {L : Log2} {m : List UInt8} {a : Digest} :
    BadLog bad (L ++ [.pub m a]) ↔ BadLog bad L := by
  constructor
  · rintro ⟨A, q, b, B, hL, hb⟩
    rcases split_snoc hL with ⟨B', -, rfl⟩ | ⟨-, -, h⟩
    · exact ⟨A, q, b, B', rfl, hb⟩
    · cases h
  · rintro ⟨A, q, b, B, rfl, hb⟩
    exact ⟨A, q, b, B ++ [.pub m a], by simp, hb⟩

/-- A `sec` entry at the end is bad, or the bad answers are the old ones. -/
theorem badLog_sec {L : Log2} {q : List UInt8} {a : Digest} :
    BadLog bad (L ++ [.sec q a]) ↔ BadLog bad L ∨ bad L q a := by
  constructor
  · rintro ⟨A, q', b, B, hL, hb⟩
    rcases split_snoc hL with ⟨B', -, rfl⟩ | ⟨-, rfl, h⟩
    · exact .inl ⟨A, q', b, B', rfl, hb⟩
    · cases h; exact .inr hb
  · rintro (⟨A, q', b, B, rfl, hb⟩ | hb)
    · exact ⟨A, q', b, B ++ [.sec q a], by simp, hb⟩
    · exact ⟨L, q, a, [], rfl, hb⟩

open Classical in
/-- The potential of a bad-answer predicate: `1` on logs with a bad secret answer, `0` elsewhere. -/
noncomputable def histμ (bad : Log2 → List UInt8 → Digest → Prop) (L : Log2) : ℝ≥0 :=
  if BadLog bad L then 1 else 0

/-- **`pubStep` with equality** for every bad-answer potential. -/
theorem ofHist_pub (L : Log2) (m : List UInt8) (a : Digest) :
    histμ bad (L ++ [.pub m a]) = histμ bad L := by
  classical
  simp only [histμ, badLog_pub]

open Classical in
/-- **A two-channel knowledge state from bad answers**: at most `ε · 2^256` bad answers to each
query, and on consistent logs with no bad answer every accepted proof is extracted. The potential
is `histμ bad`, whose `pubStep` holds with equality. -/
noncomputable def KState2.ofHist (bad : Log2 → List UInt8 → Digest → Prop)
    (hb : ∀ L q, ((Finset.univ.filter (bad L q)).card : ℝ≥0) ≤ ε * 2 ^ 256)
    (hfinal : ∀ L c π, pubConsistent L → ¬ BadLog bad L → (V c π).runLog L = some true →
      ∃ o, E c π L = some o ∧ Valid mode R c L o) : KState2 mode R V E ε where
  μ := histμ bad
  empty := by simp [histμ, BadLog]
  step L q _ _ hμ _ := by
    have hg : ¬ BadLog bad L := fun h => by simp [histμ, h] at hμ
    have hs : ∀ a, histμ bad (L ++ [.sec q a]) = if a ∈ Finset.univ.filter (bad L q) then 1 else 0 :=
      fun a => by simp [histμ, badLog_sec, hg]
    simp only [hs, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [histμ, hg, ite_false, zero_add]
    exact hb L q
  pubStep L m a _ := (ofHist_pub L m a).le
  final L c π hL _ hμ h := hfinal L c π hL (fun hb => by simp [histμ, hb] at hμ) h

/-! ## Tools for negative results -/

/-- A list of consistent BLAKE2s evaluations (no secret answer). -/
def PubTail (T : Log2) : Prop := ∀ x ∈ T, ∃ m, x = .pub m (blake2sDigest m)

theorem pubConsistent_append {L T : Log2} (hL : pubConsistent L) (hT : PubTail T) :
    pubConsistent (L ++ T) := by
  intro m a hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hL m a hm
  · obtain ⟨m', h⟩ := hT _ hm; cases h; rfl

theorem secCount_append (L T : Log2) : secCount (L ++ T) = secCount L + secCount T := by
  simp [secCount, secQueries]

theorem secCount_pubTail {T : Log2} (hT : PubTail T) : secCount T = 0 := by
  simp only [secCount, secQueries, List.length_eq_zero_iff, List.filterMap_eq_nil_iff]
  intro x hx; obtain ⟨m, rfl⟩ := hT x hx; rfl

theorem Collision.append {L : Log2} (T : Log2) : Collision L → Collision (L ++ T)
  | ⟨m, m', a, hne, h1, h2⟩ => ⟨m, m', a, hne, List.mem_append_left _ h1, List.mem_append_left _ h2⟩

/-- **A run of consistent evaluations never raises the potential** of a state with the fallback
`pubStep`, as long as it completes no collision. -/
theorem KState2W.le_of_pubTail (k : KState2W mode R V E ε) :
    ∀ {L T : Log2}, pubConsistent L → PubTail T → ¬ Collision (L ++ T) → k.μ (L ++ T) ≤ k.μ L
  | L, [], _, _, _ => by simp
  | L, x :: T, hL, hT, hc => by
    obtain ⟨m, rfl⟩ := hT x (List.mem_cons_self ..)
    have hL' : pubConsistent (L ++ [.pub m (blake2sDigest m)]) :=
      pubConsistent_append hL fun y hy => ⟨m, List.mem_singleton.mp hy⟩
    have e : L ++ Entry.pub m (blake2sDigest m) :: T = (L ++ [.pub m (blake2sDigest m)]) ++ T := by
      simp
    rw [e] at hc ⊢
    refine (k.le_of_pubTail hL' (fun y hy => hT y (List.mem_cons_of_mem _ hy)) hc).trans ?_
    rcases k.pubStep L m _ hL' with h | h
    · exact h
    · exact absurd (h.append T) hc

/-- **Extraction after a squeeze and a run of evaluations**: if the squeeze answer leaves the
potential below `1`, `final` applies to the log extended by the evaluations. -/
theorem KState2W.final_tail (k : KState2W mode R V E ε) {L₀ T : Log2} {q : List UInt8} {a : Digest}
    (hL₀ : pubConsistent L₀) (hlen : secCount L₀ < logCap) (hT : PubTail T)
    (hc : ¬ Collision (L₀ ++ .sec q a :: T)) (hμ : k.μ (L₀ ++ [.sec q a]) < 1) {c : Digest} {π : Pf}
    (hacc : (V c π).runLog (L₀ ++ .sec q a :: T) = some true) :
    ∃ o, E c π (L₀ ++ .sec q a :: T) = some o ∧ Valid mode R c (L₀ ++ .sec q a :: T) o := by
  have e : L₀ ++ Entry.sec q a :: T = (L₀ ++ [.sec q a]) ++ T := by simp
  have hs : pubConsistent (L₀ ++ [.sec q a]) := fun m b hm => by
    rcases List.mem_append.mp hm with hm | hm
    · exact hL₀ m b hm
    · simp at hm
  rw [e] at hc hacc ⊢
  refine k.final _ c π (pubConsistent_append hs hT) ?_
    ((k.le_of_pubTail hs hT hc).trans_lt hμ) hacc
  rw [secCount_append, secCount_append, secCount_pubTail hT]
  have : secCount [Entry.sec q a] = 1 := rfl
  omega

/-- **Counting answers that force the potential to `1`**: from a consistent log of potential `0`,
the answers to a fresh secret query that reach potential `1` are at most `ε · 2^256`. -/
theorem KState2W.card_le (k : KState2W mode R V E ε) {L₀ : Log2} (h0 : k.μ L₀ = 0)
    (hL₀ : pubConsistent L₀) (hlen : secCount L₀ < logCap) {q : List UInt8}
    (hq : q ∉ secQueries L₀) (S : Digest → Prop) [DecidablePred S]
    (hS : ∀ a, S a → 1 ≤ k.μ (L₀ ++ [.sec q a])) :
    ((Finset.univ.filter S).card : ℝ≥0) ≤ ε * 2 ^ 256 := by
  have hstep := k.step L₀ q hL₀ hlen (by simp [h0]) hq
  rw [h0, zero_add] at hstep
  refine le_trans ?_ hstep
  rw [← Finset.sum_boole]
  exact Finset.sum_le_sum fun a _ => by split_ifs with h; exacts [hS a h, zero_le]

/-- If every answer to a fresh secret query reaches potential `1`, the error is at least `1`. -/
theorem KState2W.one_le (k : KState2W mode R V E ε) {L₀ : Log2} (h0 : k.μ L₀ = 0)
    (hL₀ : pubConsistent L₀) (hlen : secCount L₀ < logCap) {q : List UInt8}
    (hq : q ∉ secQueries L₀) (hall : ∀ a, 1 ≤ k.μ (L₀ ++ [.sec q a])) : 1 ≤ ε := by
  have hc := k.card_le h0 hL₀ hlen hq (fun _ => True) fun a _ => hall a
  have e : (Finset.univ.filter fun _ : Digest => True).card = 2 ^ 256 := by
    rw [Finset.filter_true, Finset.card_univ, fintype_card_digest]
  rw [e, Nat.cast_pow, Nat.cast_ofNat] at hc
  exact (le_mul_iff_one_le_left (by positivity)).mp hc

/-- **The negative pattern**: from a consistent log of potential `0`, every answer to a fresh
secret query is followed by evaluations, completing no collision, after which `V` accepts a
proof the extractor does not open. Then the error is at least `1`. -/
theorem KState2W.one_le_of_fail (k : KState2W mode R V E ε) {L₀ : Log2} (h0 : k.μ L₀ = 0)
    (hL₀ : pubConsistent L₀) (hlen : secCount L₀ < logCap) {q : List UInt8}
    (hq : q ∉ secQueries L₀) (c : Digest) (π : Digest → Pf) (T : Digest → Log2)
    (hT : ∀ a, PubTail (T a)) (hc : ∀ a, ¬ Collision (L₀ ++ .sec q a :: T a))
    (hacc : ∀ a, (V c (π a)).runLog (L₀ ++ .sec q a :: T a) = some true)
    (hfail : ∀ a o, E c (π a) (L₀ ++ .sec q a :: T a) = some o →
      ¬ Valid mode R c (L₀ ++ .sec q a :: T a) o) : 1 ≤ ε :=
  k.one_le h0 hL₀ hlen hq fun a => by
    by_contra hlt
    obtain ⟨o, ho, hv⟩ := k.final_tail hL₀ hlen (hT a) (hc a) (not_le.mp hlt) (hacc a)
    exact hfail a o ho hv

/-- **What every extractor must do**: under the hypotheses of `one_le_of_fail` without the
failing extractor, and `ε < 1`, some answer leads to a log on which the extractor returns a valid
output. -/
theorem KState2W.exists_valid (k : KState2W mode R V E ε) (hε : ε < 1) {L₀ : Log2}
    (h0 : k.μ L₀ = 0) (hL₀ : pubConsistent L₀) (hlen : secCount L₀ < logCap) {q : List UInt8}
    (hq : q ∉ secQueries L₀) (c : Digest) (π : Digest → Pf) (T : Digest → Log2)
    (hT : ∀ a, PubTail (T a)) (hc : ∀ a, ¬ Collision (L₀ ++ .sec q a :: T a))
    (hacc : ∀ a, (V c (π a)).runLog (L₀ ++ .sec q a :: T a) = some true) :
    ∃ a o, E c (π a) (L₀ ++ .sec q a :: T a) = some o ∧ Valid mode R c (L₀ ++ .sec q a :: T a) o := by
  by_contra hno
  push Not at hno
  exact absurd (k.one_le_of_fail h0 hL₀ hlen hq c π T hT hc hacc fun a o ho hv => hno a o ho hv)
    (not_le.mpr hε)

end RecursionFast.Explore.TwoChannel

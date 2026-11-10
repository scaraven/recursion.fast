/-
  RecursionFast.Explore.StreamBound  (UNTRUSTED, kernel-checked; audit probe, not imported)

  **The depth-free whole-stream bound** (docs/audit/recursive-ks/stream-bound.md).

  * `KS.exists_wins`: on the final log of any `Q`-query program, the probability that **some**
    pair `(c, π)` wins `KS`'s game is at most `(Q + qV) · ε`: one `KS.select` whose selector
    picks a winning pair when there is one (CGSY24 Thm 5.1's "first failing vertex", without a
    tree). The contract's `KS` quantifies over unbounded programs, so the selector may search.
  * `escape_any_le`, `stream_escape_le`: hence an escape anywhere (any output of the stream, any
    member of its extraction tree, any depth) costs `(Q + qV) · ε`, independent of `M` and of the
    number of members (the union bounds `193` and `9,408` of design §2.4 are not needed).
  * `stream_prob`: the comb corollary: the probability that some accepted stream output's
    `combWalk` ends in an escape (not the leaf starts, a collision or a forgery) is at most
    `(Q + qV) · ε`.
  * C4 / seams-T1 Finding 2: `StructOk` (the extractor's output is a witness of the relation with
    `acc` replaced by `true`: V-free) and `escape_or_forgery_of_bad`: a tree member where `E`
    returns no structural witness, under an accepted root, gives an escape or a forgery at that
    member or an ancestor. `stream_bad_prob` bounds the V-free event by `(Q + qV) · ε`.
  * Arithmetic at the target (`Q ≤ 2^64`, `qV ≤ 2^16`, `ε ≤ 2^-120`).
-/
import RecursionFast.Explore.CombCompose

open scoped NNReal

namespace RecursionFast
variable {α : Type} {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
  {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} {qV : ℕ}

/-- **Some pair wins, one `KS` error**: on the final log `L` of a run of `A` (at most `Q`
queries), the probability that there is any pair `(c, π)` that `V` accepts reading its answers
from `L` and for which `E` on `L` returns no witness of `R` is at most `(Q + qV) · ε`. -/
theorem KS.exists_wins (h : KS R V E ε qV) (A : OProg α) {Q : ℕ}
    (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun _ L => ∃ y, Wins R V E y L) A [] ≤ (Q + qV) * ε :=
  have : Nonempty (Digest × Proof) := ⟨(Vector.replicate 32 0, ByteArray.empty)⟩
  (prob_mono (fun _ _ hw => Classical.epsilon_spec hw) A []).trans
    (h.select A hA hQ fun _ L => Classical.epsilon fun y => Wins R V E y L)

end RecursionFast

namespace RecursionFast.StreamBound
open RecursionFast RecursionFast.Compose RecursionFast.CombCompose

variable {S : Submission} {vk : Digest} {ε : ℝ≥0} {qV : ℕ}

/-! ## The depth-free bound -/

/-- **An escape anywhere, one `KS` error**: for any program `A` (at most `Q` queries, any
output type), the probability that some signed proof escapes on `A`'s final log (accepted by
`acc`, trace in the log, no witness from `E`) is at most `(Q + qV) · ε`. -/
theorem escape_any_le (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) {α : Type} (A : OProg α)
    {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun _ L => ∃ c q, Escape S vk L c q) A [] ≤ (Q + qV) * ε :=
  (prob_mono_of_inv Log.Functional (fun _ _ _ => functional_append)
    (B' := fun _ L => ∃ y, Wins (Rel (S.acc vk)) (S.V vk) S.E y L)
    (fun _ _ hL ⟨c, q, he⟩ => ⟨(c, q.π), he.wins hL⟩) A
    (fun _ h => absurd h List.not_mem_nil)).trans (hks.exists_wins A hA hQ)

/-- **The whole stream, depth-free**: `A` outputs every stream output (statement and signed
proof of each step). The probability that some member, at any path, of the extraction tree of
some output escapes on `A`'s final log is at most `(Q + qV) · ε`: no factor `M`, no factor for
the number of members, no restriction to a path set. -/
theorem stream_escape_le (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV)
    (A : OProg (List (Digest × Signed))) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q)
    (hQ : Q + qV ≤ logCap) :
    prob (fun xs L => ∃ r ∈ xs, ∃ bs c q, InTree S L r.1 r.2 bs c q ∧ Escape S vk L c q) A [] ≤
      (Q + qV) * ε :=
  (prob_mono (fun _ _ ⟨_, _, _, c, q, _, he⟩ => ⟨c, q, he⟩) A []).trans (escape_any_le hks A hA hQ)

/-! ## The comb corollary -/

/-- The chain lengths of a prefix of the stream's chains are within `chainCap`. -/
theorem hn_take {l₀ : Digest × ℕ} {ls : List (Digest × ℕ)} (hn : ∀ x ∈ l₀ :: ls, x.2 ≤ chainCap)
    (k : ℕ) : ∀ x ∈ l₀ :: ls.take k, x.2 ≤ chainCap := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | h
  · exact hn _ (.head _)
  · exact hn x (.tail _ (List.mem_of_mem_take h))

/-- **The stream's composition theorem with probabilities** (V4-A11): the harness draws the chains
`l₀ :: ls` (`M = |ls|`); `A` (at most `Q` queries) outputs the signed proofs `xs`, `xs[i]` for
step `i + 1`, whose statement is `combStmt l₀ (ls.take (i + 1))`. For each output that `acc`
accepts, `combWalk` on `A`'s final log returns the leaf starts, an explicit collision, an explicit
capped forgery in that output's extraction tree, or an escape (`COut`). The probability that
**some** accepted output's walk returns an escape is at most `(Q + qV) · ε`, independent of `M`. -/
theorem stream_prob (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV) (l₀ : Digest × ℕ)
    (ls : List (Digest × ℕ)) (hn : ∀ x ∈ l₀ :: ls, x.2 ≤ chainCap) (A : OProg (List Signed))
    {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q) (hQ : Q + qV ≤ logCap) :
    prob (fun xs L => ∃ (i : ℕ) (hi : i < xs.length)
      (hacc : S.acc vk (combStmt l₀ (ls.take (i + 1))) xs[i] = true),
      (combWalk L l₀ (ls.take (i + 1)) (hn_take hn (i + 1)) xs[i] hacc).Escaped) A [] ≤
        (Q + qV) * ε := by
  refine (prob_mono (fun xs L ⟨i, hi, hacc, he⟩ => ?_) A []).trans (escape_any_le hks A hA hQ)
  obtain ⟨_, _, c, q, _, h⟩ := he.exists
  exact ⟨c, q, h⟩

/-! ## C4: a V-free event (seams-T1 Finding 2) -/

/-- **The extractor's output is structurally a witness** at `(c, p)` on `L`: `E` returns a leaf
witness whose chain ends at `c`'s leaf statement, or a node witness whose children hash to `c`.
The children's acceptance is not checked: deciding it runs no verifier, only `E` and BLAKE2s. -/
def StructOk (S : Submission) (L : Log) (c : Digest) (p : Signed) : Prop :=
  ∃ w, S.E c p.π L = some w ∧ Rel (fun _ _ => true) c w

instance (L : Log) (c : Digest) (p : Signed) : Decidable (StructOk S L c p) :=
  decOpens _ c _

/-- A witness of the relation is a structural witness. -/
theorem rel_struct {acc : Digest → Signed → Bool} {c : Digest} :
    ∀ {w : Wit}, Rel acc c w → Rel (fun _ _ => true) c w
  | .leaf _ _, h => h
  | .node _ _ _ _, h => ⟨h.1, rfl, rfl⟩

/-- An accepted signed proof with no witness from `E` escapes, or is a forgery against `L`. -/
theorem escape_or_forgery_of_acc {L : Log} {c : Digest} {q : Signed}
    (hacc : S.acc vk c q = true) (hno : ¬ ∃ w, S.E c q.π L = some w ∧ Rel (S.acc vk) c w) :
    Escape S vk L c q ∨ ∃ f : Forgery vk L, f.p = q := by
  by_cases hin : ∀ e ∈ q.tr, e ∈ L
  · exact .inl ⟨hacc, hin, hno⟩
  · exact .inr ⟨⟨q, (acc_parts hacc).2.1, (acc_parts hacc).2.2.1, hin⟩, rfl⟩

/-- **A rejected member has an escaping or forged ancestor**: under an accepted root, a member of
the extraction tree that `acc` rejects has a proper ancestor (path a suffix) that escapes or is a
forgery against `L`: the nearest accepted ancestor's `E` output names a rejected child. -/
theorem anc_of_not_acc {L : Log} {c₀ : Digest} {p₀ : Signed} (hroot : S.acc vk c₀ p₀ = true)
    {bs : List Bool} {c : Digest} {q : Signed} (hm : InTree S L c₀ p₀ bs c q)
    (hq : S.acc vk c q = false) :
    ∃ bs' c' q', bs' <:+ bs ∧ InTree S L c₀ p₀ bs' c' q' ∧
      (Escape S vk L c' q' ∨ ∃ f : Forgery vk L, f.p = q') := by
  induction hm with
  | root => simp [hroot] at hq
  | @left bs c c₁ c₂ p p₁ p₂ hm' hE ih =>
    by_cases hp : S.acc vk c p = true
    · refine ⟨bs, c, p, List.suffix_cons _ _, hm', escape_or_forgery_of_acc hp ?_⟩
      rintro ⟨w, hw, hR⟩
      rw [hE] at hw; cases hw; exact Bool.false_ne_true (hq.symm.trans hR.2.1)
    · obtain ⟨bs', c', q', hs, hm'', h⟩ := ih (by simpa using hp)
      exact ⟨bs', c', q', hs.trans (List.suffix_cons _ _), hm'', h⟩
  | @right bs c c₁ c₂ p p₁ p₂ hm' hE ih =>
    by_cases hp : S.acc vk c p = true
    · refine ⟨bs, c, p, List.suffix_cons _ _, hm', escape_or_forgery_of_acc hp ?_⟩
      rintro ⟨w, hw, hR⟩
      rw [hE] at hw; cases hw; exact Bool.false_ne_true (hq.symm.trans hR.2.2)
    · obtain ⟨bs', c', q', hs, hm'', h⟩ := ih (by simpa using hp)
      exact ⟨bs', c', q', hs.trans (List.suffix_cons _ _), hm'', h⟩

/-- **The V-free failure implies an escape or a forgery**: under an accepted root, a member of
the extraction tree at which `E` returns no structural witness has, at itself or an ancestor, an
escape or a forgery against `L`. -/
theorem escape_or_forgery_of_bad {L : Log} {c₀ : Digest} {p₀ : Signed}
    (hroot : S.acc vk c₀ p₀ = true) {bs : List Bool} {c : Digest} {q : Signed}
    (hm : InTree S L c₀ p₀ bs c q) (hbad : ¬ StructOk S L c q) :
    ∃ bs' c' q', bs' <:+ bs ∧ InTree S L c₀ p₀ bs' c' q' ∧
      (Escape S vk L c' q' ∨ ∃ f : Forgery vk L, f.p = q') := by
  cases hq : S.acc vk c q
  · exact anc_of_not_acc hroot hm hq
  · exact ⟨bs, c, q, List.suffix_refl _, hm,
      escape_or_forgery_of_acc hq fun ⟨w, hw, hR⟩ => hbad ⟨w, hw, rel_struct hR⟩⟩

/-- **The comb's paths are closed under suffixes** (ancestors of comb members are comb members). -/
theorem combPaths_suffix {M : ℕ} {bs bs' : List Bool} (h : bs ∈ combPaths M) (hs : bs' <:+ bs) :
    bs' ∈ combPaths M := by
  have hrep : ∀ {j : ℕ} {l : List Bool}, l <:+ List.replicate j false → j ≤ M → l ∈ combPaths M :=
    fun {j l} hl hj => by
      have hl' : l = List.replicate l.length false :=
        List.eq_replicate_iff.mpr ⟨rfl, fun b hb => List.eq_of_mem_replicate (hl.subset hb)⟩
      rw [hl']
      exact spine_mem ((hl.length_le.trans (List.length_replicate ..).le).trans hj)
  rcases Finset.mem_union.mp h with h | h <;> obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h <;>
    simp only [Finset.mem_range] at hj
  · exact hrep hs (by omega)
  · rcases List.suffix_cons_iff.mp hs with rfl | hs
    · exact leaf_mem hj
    · exact hrep hs (by omega)

/-- **The V-free event over the whole stream**: for a suffix-closed path set `P` (for instance
`combPaths M`), the probability that some output `r` is accepted, some member of its tree at a path
in `P` gets no structural witness from `E`, and no member of its tree at a path in `P` is a forgery
against the final log, is at most `(Q + qV) · ε`. Apart from the roots' acceptance (the harness's
own capped check), the event runs `E` and BLAKE2s along the paths of `P`, plus, for the forgery
clause, trace membership and `SigOk`: never `V`. -/
theorem stream_bad_prob (hks : KS (Rel (S.acc vk)) (S.V vk) S.E ε qV)
    (A : OProg (List (Digest × Signed))) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q)
    (hQ : Q + qV ≤ logCap) (P : Finset (List Bool))
    (hP : ∀ bs ∈ P, ∀ bs', bs' <:+ bs → bs' ∈ P) :
    prob (fun xs L => ∃ r ∈ xs, S.acc vk r.1 r.2 = true ∧
      (∃ bs ∈ P, ∃ c q, InTree S L r.1 r.2 bs c q ∧ ¬ StructOk S L c q) ∧
      ¬ ∃ (f : Forgery vk L), ∃ bs ∈ P, ∃ c, InTree S L r.1 r.2 bs c f.p) A [] ≤
        (Q + qV) * ε := by
  refine (prob_mono (fun xs L ⟨r, _, hroot, ⟨bs, hbs, c, q, hm, hbad⟩, hnf⟩ => ?_) A []).trans
    (escape_any_le hks A hA hQ)
  obtain ⟨bs', c', q', hs, hm', h | ⟨f, rfl⟩⟩ := escape_or_forgery_of_bad hroot hm hbad
  · exact ⟨c', q', h⟩
  · exact absurd ⟨f, bs', hP bs hbs bs' hs, c', hm'⟩ hnf

/-! ## Controls -/

/-- Positive: an escape at a fixed pair is one of the events `escape_any_le` bounds. -/
example {L : Log} {c : Digest} {q : Signed} (h : Escape S vk L c q) : ∃ c q, Escape S vk L c q :=
  ⟨c, q, h⟩

/-- Negative (`StructOk` is not vacuous): a node witness whose children do not hash to `c` is not
structural, whatever `acc` says. -/
example (c c₁ c₂ : Digest) (p₁ p₂ : Signed) (h : c ≠ nodeStmt c₁ c₂) :
    ¬ Rel (fun _ _ => true) c (.node c₁ c₂ p₁ p₂) := fun hR => h hR.1

/-- Positive: a node witness whose children hash to `c` is structural even if `acc` rejects
both children (`StructOk` is strictly weaker than the relation). -/
example (c₁ c₂ : Digest) (p₁ p₂ : Signed) :
    Rel (fun _ _ => true) (nodeStmt c₁ c₂) (.node c₁ c₂ p₁ p₂) ∧
      ¬ Rel (fun _ _ => false) (nodeStmt c₁ c₂) (.node c₁ c₂ p₁ p₂) :=
  ⟨⟨rfl, rfl, rfl⟩, fun hR => Bool.false_ne_true hR.2.1⟩

/-! ## Arithmetic at the target (`Q ≤ 2^64`, `qV ≤ 2^16`, `ε ≤ 2^-120`) -/

/-- **The whole stream at the target**: `(Q + qV) · ε ≤ 2^-55`. -/
theorem stream_err_target {Q qV : ℕ} {ε : ℝ≥0} (hQ : Q ≤ 2 ^ 64) (hq : qV ≤ 2 ^ 16)
    (hε : ε ≤ (2 ^ 120)⁻¹) : (Q + qV) * ε ≤ (2 ^ 55)⁻¹ := by
  have hs : ((Q : ℝ≥0) + qV) ≤ 2 ^ 64 + 2 ^ 16 := by
    have : Q + qV ≤ 2 ^ 64 + 2 ^ 16 := by omega
    exact_mod_cast this
  refine (mul_le_mul' hs hε).trans ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  norm_num

/-- The same number over `ℚ`: `(2^64 + 2^16) / 2^120 ≤ 2^-55`. -/
theorem stream_err_q : (2 ^ 64 + 2 ^ 16 : ℚ) / 2 ^ 120 ≤ 1 / 2 ^ 55 := by norm_num

/-- **The design's union-bound figures are `2^7`–`2^8` and `2^13`–`2^14` times larger**: the final
output's `193` members and every output's `9,408` members. -/
theorem union_factors (x : ℝ≥0) :
    2 ^ 7 * x ≤ 193 * x ∧ 2 ^ 13 * x ≤ 9408 * x ∧ (193 : ℕ) < 2 ^ 8 ∧ (9408 : ℕ) < 2 ^ 14 :=
  ⟨by gcongr; norm_num, by gcongr; norm_num, by norm_num, by norm_num⟩

end RecursionFast.StreamBound

#print axioms RecursionFast.KS.exists_wins
#print axioms RecursionFast.StreamBound.escape_any_le
#print axioms RecursionFast.StreamBound.stream_escape_le
#print axioms RecursionFast.StreamBound.stream_prob
#print axioms RecursionFast.StreamBound.escape_or_forgery_of_bad
#print axioms RecursionFast.StreamBound.stream_bad_prob
#print axioms RecursionFast.StreamBound.combPaths_suffix
#print axioms RecursionFast.StreamBound.stream_err_target
#print axioms RecursionFast.StreamBound.stream_err_q
#print axioms RecursionFast.StreamBound.union_factors

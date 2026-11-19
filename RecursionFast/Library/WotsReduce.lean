/-
  RecursionFast.Library.WotsReduce  (UNTRUSTED, kernel-checked)

  **EUF-CMA of the contract's signature, reduced to a Keccak-256 collision or a chain
  inversion** (`wotsReduce`), deterministic and compiled, with no probability: the discipline of
  `walk` (`Library/Compose.lean`).

  Fix the secret chain starts `sk` of the reference signer (`Library/Signer.lean`) and its
  signing record `R`, the (index, message) pairs it signed, each index once
  (`(R.map Prod.fst).Nodup`); the signature it issued for `(j, m₀)` is `sign sk j m₀`, which
  reveals chain `i` of key `j` at position `dᵢ(m₀)`, the `i`-th WOTS digit of `m₀`
  (`sign_ots_getElem?`), so every position above it too. A forgery is `SigOk (pk sk) m σ` with `m`
  among no message of `R`. With `j = σ.idx`, the reduction:
  1. **The path.** If the forged leaf is not key `j`'s honest leaf, the first level of the path
     where the forged value meets the honest tree (`node sk`) gives a `sigNode` collision (`climb`:
     the root is reached, so they meet). If the leaves are equal but the forged chain ends are not
     key `j`'s, a `wotsLeaf` collision (the same `enc64 j` prefix).
  2. **The chain.** It picks one chain `i` (`pick`): for an index `j` that `R` used, with the
     message `m₀ ≠ m`, the first `i` with `dᵢ(m) < dᵢ(m₀)` (`wotsDigits_dominates`); for an unused
     index, the first `i` with `dᵢ(m) < 3` (`wotsDigits_lt_three`). The forged value at
     `dᵢ(m)` and the honest one walk to the same end; if they differ, the first step that maps two
     different values to one is a `wotsStep` collision (`chainCollision`, the same tweak `j, i, s`).
  3. Else the forged value **is** the honest chain value at position `dᵢ(m)`, which lies below
     every position the signer revealed of chain `i` of key `j` (and below the end): an
     **inversion** (`WotsBreak.inversion`).

  **The type pins the inversion; the collision is computed.** `WotsBreak sk R m σ` is indexed by
  the forgery: its `inversion` carries the chain `i`, that the forgery's own value for chain `i`
  is the honest value `hv sk σ.idx i dᵢ(m)`, that `dᵢ(m) < 3`, and that `dᵢ(m) < dᵢ(m₀)` for every
  `(σ.idx, m₀) ∈ R`. So it exists only when the forger output an honest chain value at an
  unrevealed position: no chain value of an issued signature, on its own message, is an inversion
  (`Controls/WotsReduce.lean`, `not_inversion_issued`), and with an index used twice there may be
  no unrevealed position at all (`not_inversion_twice`). The `collision` carries a
  `Collision`, two different byte strings with one digest; such a pair exists by pigeonhole
  (`Controls/Compose.lean`, `collision_nonempty`), so as for `Outcome` the type alone is not the
  statement of the collision branch: its content is the compiled `wotsReduce`, which computes the
  colliding preimages from the forgery and `sk` (the honest tree and chains), and chooses no data
  classically. A forger that knows `sk` and signs a fresh message, at a used or an unused index,
  is reduced to an inversion (`wotsReduce_sign`, for every `sk`): the outcome is reachable.

  **Against the composition.** `eufReduce` takes an EUF-CMA forgery against `issued T` (the
  service's signed traces, `Library/Unforgeability.lean`) under `pk sk`, the traces' signature
  indices pairwise distinct, to a `WotsBreak` against `record T` (each trace's index and digest).
  The reduction reads the traces' digests and indices, never their signatures, as the EUF-CMA event
  does (`eufForgery_issued_iff`); by the service's specification those are `sign sk j (traceDigest
  tr)`, which is what makes the `unrevealed` positions unrevealed. `SignedOutcome.IsEuf.wots`
  splits the walk's EUF-CMA outcome into the reduction's two outcomes, and
  `compose_prob_stream_wots` is `compose_prob_stream_signed` with its EUF-CMA term so split: the
  stream composition fails with probability at most the escape bound plus the probabilities of a
  collision (the walk's, or the signature reduction's) and of a chain inversion.

  On paper: that the chain starts (`chainStart`) are pseudorandom, and the probability that an
  adversary outputs an honest chain value at an unrevealed position (one-wayness of the tweaked
  chain step, a preimage of `wotsStep` or, for an unused key, a guess of a pseudorandom value).
-/
import RecursionFast.Library.Signer
import RecursionFast.Library.Compose

namespace RecursionFast.WotsReduce
open RecursionFast RecursionFast.Signer

variable (sk : ℕ → ℕ → Digest)

/-- **The honest value** of chain `i` of key `j` at position `t`. -/
def hv (j i t : ℕ) : Digest := wotsChain j i 0 t (sk j i)

/-- **What the reduction of the forgery `σ` on `m` returns**, against the signing record `R`: a
Keccak-256 collision, or an **inversion**: a chain `i` on which the forgery's value is the honest
chain value at position `dᵢ(m)` (the `i`-th WOTS digit of `m`), below the chain's end and below
the position every signature of `R` with the forgery's index revealed. -/
inductive WotsBreak (R : List (ℕ × Digest)) (m : Digest) (σ : Sig) where
  /-- A Keccak-256 collision. -/
  | collision (col : Collision)
  /-- The forgery's value for chain `i` is the honest chain value at an unrevealed position. -/
  | inversion (i : ℕ) (hi : i < wotsLen) (below : (wotsDigits m).getD i 0 < 3)
      (value : σ.ots[i]? = some (hv sk σ.idx i ((wotsDigits m).getD i 0)))
      (unrevealed : ∀ m₀, (σ.idx, m₀) ∈ R →
        (wotsDigits m).getD i 0 < (wotsDigits m₀).getD i 0)

namespace WotsBreak
variable {sk} {R : List (ℕ × Digest)} {m : Digest} {σ : Sig}

/-- The outcome is a collision. -/
def IsCollision : WotsBreak sk R m σ → Prop
  | .collision _ => True
  | _ => False

/-- The outcome is an inversion. -/
def IsInversion : WotsBreak sk R m σ → Prop
  | .inversion .. => True
  | _ => False

/-- Every outcome is a collision or an inversion. -/
theorem cases (b : WotsBreak sk R m σ) : b.IsCollision ∨ b.IsInversion := by
  cases b
  · exact .inl trivial
  · exact .inr trivial

end WotsBreak

/-! ## The three collisions -/

/-- Two pairs of digests with equal byte strings are equal. -/
theorem toList_append_inj {a b c d : Digest} {u v : List UInt8} (hl : u.length = v.length)
    (h : u ++ a.toList ++ b.toList = v ++ c.toList ++ d.toList) : a = c ∧ b = d := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
  exact ⟨Vector.toList_inj.mp (List.append_inj h1 hl).2, Vector.toList_inj.mp h2⟩

/-- Lists of digests with equal byte strings are equal. -/
theorem flatMap_toList_inj : ∀ {E E' : List Digest},
    E.flatMap Vector.toList = E'.flatMap Vector.toList → E = E'
  | [], [], _ => rfl
  | [], _ :: _, h => by have := congrArg List.length h; simp at this; omega
  | _ :: _, [], h => by have := congrArg List.length h; simp at this
  | a :: E, b :: E', h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    rw [Vector.toList_inj.mp h1, flatMap_toList_inj h2]

/-- **A `sigNode` collision at one level of the path**: the forged value `x` of node `k` of
level `t` is not the honest one, but its parent (with the sibling `s`) is. -/
def nodeCollision (t k : ℕ) (x s : Digest) (hne : x ≠ node sk t k)
    (h : (if k % 2 = 0 then sigNode x s else sigNode s x) = node sk (t + 1) (k / 2)) :
    Collision :=
  if hk : k % 2 = 0 then
    Collision.of (x := tagSigNode :: x.toList ++ s.toList)
      (y := tagSigNode :: (node sk t (2 * (k / 2))).toList ++ (node sk t (2 * (k / 2) + 1)).toList)
      (fun hb => hne (by
        rw [(toList_append_inj (u := [_]) rfl hb).1, show 2 * (k / 2) = k by omega]))
      (by simp only [hk, ↓reduceIte] at h; exact h)
  else
    Collision.of (x := tagSigNode :: s.toList ++ x.toList)
      (y := tagSigNode :: (node sk t (2 * (k / 2))).toList ++ (node sk t (2 * (k / 2) + 1)).toList)
      (fun hb => hne (by
        rw [(toList_append_inj (u := [_]) rfl hb).2, show 2 * (k / 2) + 1 = k by omega]))
      (by simp only [hk, ↓reduceIte] at h; exact h)

/-- **The climb's collision**: a forged value `x` of node `k` of level `t` that is not the honest
one, but whose climb along `p` reaches the honest node above, meets the honest tree at some
level: a `sigNode` collision there. -/
def climb : (t k : ℕ) → (x : Digest) → (p : List Digest) → x ≠ node sk t k →
    sigRoot k x p = node sk (t + p.length) (k / 2 ^ p.length) → Collision
  | t, k, x, [], hne, h => absurd (by simpa [sigRoot] using h) hne
  | t, k, x, s :: p, hne, h =>
    if hy : (if k % 2 = 0 then sigNode x s else sigNode s x) = node sk (t + 1) (k / 2) then
      nodeCollision sk t k x s hne hy
    else
      climb (t + 1) (k / 2) _ p hy (by
        rw [sigRoot] at h
        rw [h, List.length_cons, pow_succ', ← Nat.div_div_eq_div_mul,
          show t + (p.length + 1) = t + 1 + p.length by omega])

/-- **A `wotsStep` collision on a chain**: two different values at position `s` of chain `i` of
key `j` that walk `n` steps to one value meet at a step that maps two different values to one. -/
def chainCollision (j i : ℕ) : (s n : ℕ) → (x y : Digest) → x ≠ y →
    wotsChain j i s n x = wotsChain j i s n y → Collision
  | _, 0, _, _, hne, h => absurd h hne
  | s, n + 1, x, y, hne, h =>
    if hs : wotsStep j i s x = wotsStep j i s y then
      Collision.of (x := tagWots :: enc64 j ++ [i.toUInt8, s.toUInt8] ++ x.toList)
        (y := tagWots :: enc64 j ++ [i.toUInt8, s.toUInt8] ++ y.toList)
        (fun hb => hne (Vector.toList_inj.mp (List.append_cancel_left hb))) hs
    else chainCollision j i (s + 1) n _ _ hs h

/-! ## The chain to compare -/

/-- The first chain `i < wotsLen` with `d i < b i`, given that one exists. -/
def firstBelow (d b : ℕ → ℕ) (h : ∃ i < wotsLen, d i < b i) : {i // i < wotsLen ∧ d i < b i} :=
  match hf : (List.range wotsLen).find? (fun i => decide (d i < b i)) with
  | some i =>
    have hd := List.find?_some hf
    ⟨i, List.mem_range.mp (List.mem_of_find?_eq_some hf), of_decide_eq_true hd⟩
  | none => absurd h fun ⟨i, hi, hlt⟩ =>
      List.find?_eq_none.mp hf i (List.mem_range.mpr hi) (decide_eq_true hlt)

/-- **The chain to compare** for a forgery on `m` with key `j`: one whose digit of `m` is below 3
and below its digit of every message `R` signed with key `j`. -/
def pick (R : List (ℕ × Digest)) (hR : (R.map Prod.fst).Nodup) (j : ℕ) (m : Digest)
    (hm : ∀ x ∈ R, x.2 ≠ m) :
    {i // i < wotsLen ∧ (wotsDigits m).getD i 0 < 3 ∧
      ∀ m₀, (j, m₀) ∈ R → (wotsDigits m).getD i 0 < (wotsDigits m₀).getD i 0} :=
  match hf : R.find? (fun x => decide (x.1 = j)) with
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hd := List.find?_some hf
    have hj : x.1 = j := of_decide_eq_true hd
    match firstBelow (fun i => (wotsDigits m).getD i 0) (fun i => (wotsDigits x.2).getD i 0)
        (wotsDigits_dominates (hm x hx)) with
    | ⟨i, hi, hlt⟩ => ⟨i, hi, lt_of_lt_of_le hlt (wotsDigits_getD_le _ _), fun m₀ hm₀ => by
        obtain rfl : (j, m₀) = x := List.inj_on_of_nodup_map hR hm₀ hx hj.symm
        exact hlt⟩
  | none =>
    match firstBelow (fun i => (wotsDigits m).getD i 0) (fun _ => 3) (wotsDigits_lt_three m) with
    | ⟨i, hi, hlt⟩ => ⟨i, hi, hlt, fun m₀ hm₀ =>
        absurd (decide_eq_true rfl) (List.find?_eq_none.mp hf _ hm₀)⟩

/-! ## The reduction -/

/-- The forged chain end of chain `i`, from its value `x`. -/
theorem wotsEnds_getElem? {j : ℕ} {m : Digest} {ots : List Digest} {i : ℕ} {x : Digest}
    (hi : i < wotsLen) (hx : ots[i]? = some x) :
    (wotsEnds j m ots)[i]? =
      some (wotsChain j i ((wotsDigits m).getD i 0) (3 - (wotsDigits m).getD i 0) x) := by
  have hi' : i < (wotsDigits m).length := by rwa [wotsDigits_length]
  have hd : (wotsDigits m)[i]? = some ((wotsDigits m).getD i 0) := by
    rw [List.getElem?_eq_getElem hi', List.getD_eq_getElem _ _ hi']
  rw [wotsEnds, List.getElem?_mapIdx,
    (List.getElem?_zip_eq_some (z := ((wotsDigits m).getD i 0, x))).mpr ⟨hd, hx⟩]
  rfl

/-- The honest chain end of chain `i`, from the honest value at any position `d ≤ 3`. -/
theorem pubEnds_getElem? {j i d : ℕ} (hi : i < wotsLen) (hd : d ≤ 3) :
    (pubEnds sk j)[i]? = some (wotsChain j i d (3 - d) (hv sk j i d)) := by
  simp only [pubEnds, List.getElem?_map, List.getElem?_range hi, Option.map_some, hv]
  conv_lhs => rw [← Nat.add_sub_cancel' hd, wotsChain_add, Nat.zero_add]

/-- **The reduction of a forgery**, computed: a valid signature `σ` under `pk sk` on a message
`m` that the signing record `R` (each index once) never signed is a `sigNode`, `wotsLeaf` or
`wotsStep` collision, or the honest chain value at an unrevealed position (`WotsBreak`). -/
def wotsReduce (R : List (ℕ × Digest)) (hR : (R.map Prod.fst).Nodup) (m : Digest) (σ : Sig)
    (hσ : SigOk (pk sk) m σ = true) (hm : ∀ x ∈ R, x.2 ≠ m) : WotsBreak sk R m σ :=
  have hσ' : ((σ.idx < 2 ^ sigHeight ∧ σ.ots.length = wotsLen) ∧ σ.path.length = sigHeight) ∧
      sigRoot σ.idx (wotsLeaf σ.idx (wotsEnds σ.idx m σ.ots)) σ.path = pk sk := by
    simpa only [SigOk, Bool.and_eq_true, decide_eq_true_eq] using hσ
  if hl : wotsLeaf σ.idx (wotsEnds σ.idx m σ.ots) = node sk 0 σ.idx then
    if he : wotsEnds σ.idx m σ.ots = pubEnds sk σ.idx then
      match pick R hR σ.idx m hm with
      | ⟨i, hi, hb, hu⟩ =>
        match hx : σ.ots[i]? with
        | some x =>
          if hxv : x = hv sk σ.idx i ((wotsDigits m).getD i 0) then
            .inversion i hi hb (hx.trans (congrArg some hxv)) hu
          else
            .collision (chainCollision σ.idx i ((wotsDigits m).getD i 0)
              (3 - (wotsDigits m).getD i 0) x _ hxv (Option.some.inj (by
                rw [← wotsEnds_getElem? hi hx, he,
                  pubEnds_getElem? sk (d := (wotsDigits m).getD i 0) hi (by omega)])))
        | none => absurd hx (by have := hσ'.1.1.2; rw [List.getElem?_eq_getElem (by omega)]; simp)
    else
      .collision (Collision.of
        (x := tagWotsLeaf :: enc64 σ.idx ++ (wotsEnds σ.idx m σ.ots).flatMap Vector.toList)
        (y := tagWotsLeaf :: enc64 σ.idx ++ (pubEnds sk σ.idx).flatMap Vector.toList)
        (fun hb => he (flatMap_toList_inj (List.append_cancel_left hb))) hl)
  else
    .collision (climb sk 0 σ.idx _ σ.path hl (by
      rw [hσ'.2, hσ'.1.2, Nat.div_eq_of_lt hσ'.1.1.1, pk, Nat.zero_add]))

/-- **A forger that knows the key is reduced to an inversion**: for every `sk`, record `R` and
key index `j < 2^16`, the honest signature `sign sk j m` on a message `R` never signed reduces to
the honest chain value at an unrevealed position, whether `R` used `j` or not. -/
theorem wotsReduce_sign (R : List (ℕ × Digest)) (hR : (R.map Prod.fst).Nodup) {j : ℕ}
    (hj : j < 2 ^ sigHeight) (m : Digest) (hm : ∀ x ∈ R, x.2 ≠ m) :
    (wotsReduce sk R hR m (sign sk j m) (sigOk_sign sk j hj m) hm).IsInversion := by
  have he : wotsEnds (sign sk j m).idx m (sign sk j m).ots = pubEnds sk (sign sk j m).idx :=
    wotsEnds_sign sk j m
  have hl : wotsLeaf (sign sk j m).idx (wotsEnds (sign sk j m).idx m (sign sk j m).ots) =
      node sk 0 (sign sk j m).idx := by rw [he]; rfl
  unfold wotsReduce
  rw [dite_eq_left_of_eq_true (eq_true hl), dite_eq_left_of_eq_true (eq_true he)]
  generalize pick R hR (sign sk j m).idx m hm = P
  obtain ⟨i, hi, hb, hu⟩ := P
  dsimp only
  split
  · rename_i x hx
    rw [sign_ots_getElem? sk j m hi, Option.some.injEq] at hx
    rw [dite_eq_left_of_eq_true (eq_true (by rw [← hx]; rfl))]
    trivial
  · rename_i hx
    rw [sign_ots_getElem? sk j m hi] at hx
    exact absurd hx (by simp)

/-! ## Against the service's signed traces -/

/-- **The signing record of signed traces**: each trace's signature index and digest. -/
def record (T : List (Trace × Sig)) : List (ℕ × Digest) :=
  T.map fun x => (x.2.idx, traceDigest x.1)

/-- **An EUF-CMA forgery against the service's signed traces, reduced**: under `pk sk`, with the
signed traces' indices pairwise distinct, a `WotsBreak` against their record. -/
def eufReduce (T : List (Trace × Sig)) (hT : (T.map fun x => x.2.idx).Nodup) {m : Digest}
    {σ : Sig} (h : EufForgery (SigOk (pk sk)) (issued T) m σ) : WotsBreak sk (record T) m σ :=
  wotsReduce sk (record T) (by simpa [record, List.map_map, Function.comp_def] using hT) m σ h.1
    fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact (eufForgery_issued_iff.mp h).2 y hy

end RecursionFast.WotsReduce

/-! ## The stream composition's failure: a collision or a chain inversion -/

namespace RecursionFast.Compose.SignedOutcome
open RecursionFast RecursionFast.Signer RecursionFast.WotsReduce
open scoped NNReal

variable {S : Submission} {sk : ℕ → ℕ → Digest} {L : Log} {T : List (Trace × Sig)} {n : ℕ}
  {hs : List Digest} {c₀ : Digest} {p₀ : Signed} {d : ℕ}

/-- The outcome is an EUF-CMA forgery that `eufReduce` reduces to a collision. -/
def IsWotsCollision (hN : (T.map fun x => x.2.idx).Nodup) :
    SignedOutcome S (pk sk) L T n hs c₀ p₀ d → Prop
  | .euf _ _ _ _ h => (eufReduce sk T hN h).IsCollision
  | _ => False

/-- The outcome is an EUF-CMA forgery that `eufReduce` reduces to a chain inversion. -/
def IsWotsInversion (hN : (T.map fun x => x.2.idx).Nodup) :
    SignedOutcome S (pk sk) L T n hs c₀ p₀ d → Prop
  | .euf _ _ _ _ h => (eufReduce sk T hN h).IsInversion
  | _ => False

/-- **The walk's EUF-CMA forgery is a collision or a chain inversion**, under `pk sk` with the
signed traces' indices pairwise distinct. -/
theorem IsEuf.wots (hN : (T.map fun x => x.2.idx).Nodup)
    {o : SignedOutcome S (pk sk) L T n hs c₀ p₀ d} (h : o.IsEuf) :
    o.IsWotsCollision hN ∨ o.IsWotsInversion hN := by
  cases o with
  | euf _ _ _ _ he => exact (eufReduce sk T hN he).cases
  | _ => exact absurd h id

/-- The union bound for two events. -/
private theorem prob_or_le {α : Type} (B₁ B₂ : α → Log → Prop) (p : OProg α) (L : Log) :
    prob (fun x L => B₁ x L ∨ B₂ x L) p L ≤ prob B₁ p L + prob B₂ p L := by
  have h := prob_exists_le {true, false} (fun b => if b then B₁ else B₂) p L
  rw [Finset.sum_pair (by decide)] at h
  refine (prob_mono (fun x L hx => ?_) p L).trans h
  rcases hx with hx | hx
  · exact ⟨true, by simp, hx⟩
  · exact ⟨false, by simp, hx⟩

/-- **The composition theorem over the stream, down to Keccak-256 and the chains**: under the
reference signer's public key `pk sk`, with the signed traces' indices pairwise distinct (each
index signs once), the probability that `acc` accepts the adversary's signed proof of the
stream's digest and the stream walk returns no leaf seeds is at most
`(2|hs| - 1) · (Q + qV) · ε` plus the probabilities that it returns a collision, that its EUF-CMA
forgery reduces to a collision, and that it reduces to a chain inversion (`eufReduce`). -/
theorem compose_prob_stream_wots {ε : ℝ≥0} {qV : ℕ} (sk : ℕ → ℕ → Digest)
    (hks : KS (Rel (S.acc (pk sk))) (S.V (pk sk)) S.E ε qV) (n : ℕ) (hn : n ≤ leafCap)
    (hs : List Digest) (A : OProg Signed) {Q : ℕ} (hA : ∀ H, (A.queries H).length ≤ Q)
    (hQ : Q + qV ≤ logCap) (T : Signed → Log → List (Trace × Sig))
    (hT : ∀ p L, Honest (T p L) L) (hN : ∀ p L, ((T p L).map fun x => x.2.idx).Nodup) :
    prob (fun p L => ∃ hacc : S.acc (pk sk) (streamStmt n hs) p = true,
      (walkStreamSigned L (T p L) (hT p L) n hn hs p hacc).seeds? = none) A [] ≤
      (2 * hs.length - 1 : ℕ) * ((Q + qV) * ε) +
      prob (fun p L => ∃ hacc : S.acc (pk sk) (streamStmt n hs) p = true,
        (walkStreamSigned L (T p L) (hT p L) n hn hs p hacc).IsCollision) A [] +
      prob (fun p L => ∃ hacc : S.acc (pk sk) (streamStmt n hs) p = true,
        (walkStreamSigned L (T p L) (hT p L) n hn hs p hacc).IsWotsCollision (hN p L)) A [] +
      prob (fun p L => ∃ hacc : S.acc (pk sk) (streamStmt n hs) p = true,
        (walkStreamSigned L (T p L) (hT p L) n hn hs p hacc).IsWotsInversion (hN p L)) A [] := by
  refine (compose_prob_stream_signed hks n hn hs A hA hQ T hT).trans
    ((add_le_add le_rfl ?_).trans (add_assoc _ _ _).symm.le)
  refine (prob_mono (fun p L ⟨hacc, h⟩ => ?_) A []).trans (prob_or_le _ _ A [])
  exact (h.wots (hN p L)).imp (⟨hacc, ·⟩) (⟨hacc, ·⟩)

end RecursionFast.Compose.SignedOutcome

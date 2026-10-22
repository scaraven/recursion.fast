/-
ADV1 probes: two ROM-sound verifiers that admit no knowledge state at any useful error.

* `Product`: a verifier that asks `k` fixed queries and accepts iff every answer lies in a set `T`.
  Its random-oracle soundness error is `(|T|/2^256)^k` (the queries are fixed, so no adversary
  does better). Every `Bounded ε` knowledge state for a relation with a witnessless statement has
  `ε ≥ |T|/2^256` (`eps_ge_density`). With `T` = "first byte zero" and `k = 16` the ROM error is
  `2^-128` but `ε ≥ 2^-8` (`product16_not_capped`). This is the shape of a FRI/WHIR/Ligero query
  phase whose positions come from several 32-byte squeezes.
* `Collision`: a verifier that accepts a proof naming two distinct queries with equal answers.
  Its ROM error is at most `(Q+2)^2 / 2^257`. No knowledge state is bounded at `errorCap`
  (`collision_not_capped`), nor at any `ε` with `2·⌊ε·2^256⌋ < 2^256` (`collision_no_bound`):
  `Bounded` quantifies over logs of every length, so a collision bad set (size `|L|`) is never
  within `ε·2^256` for all logs. This is the binding (Merkle) half of every hash-based SNARK.
-/
import RecursionFast.Library.Security
import Mathlib.Basic.Finite.Sum

open scoped NNReal

namespace AdvProbe
open RecursionFast

/-- Query number `i`: `i` zero bytes. -/
def z (i : ℕ) : ByteArray := ⟨Array.replicate i 0⟩

theorem z_size (i : ℕ) : (z i).size = i := by simp [z, ByteArray.size]

theorem z_inj {i j : ℕ} (h : z i = z j) : i = j := by
  simpa [z_size] using congrArg ByteArray.size h

/-- The log answering `z 0, …, z (N-1)` with `f 0, …, f (N-1)`. -/
def logOf (f : ℕ → Digest) (N : ℕ) : Log := (List.range N).map fun j => (z j, f j)

theorem find_none (f : ℕ → Digest) (N : ℕ) :
    (logOf f N).find? (fun e => decide (e.1 = z N)) = none := by
  rw [List.find?_eq_none]
  intro e he
  simp only [logOf, List.mem_map, List.mem_range] at he
  obtain ⟨j, hj, rfl⟩ := he
  simp only [decide_eq_true_eq]
  intro h; have := z_inj h; omega

theorem find_some (f : ℕ → Digest) : ∀ N i, i < N →
    (logOf f N).find? (fun e => decide (e.1 = z i)) = some (z i, f i)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | N + 1, i, h => by
    have hs : logOf f (N + 1) = logOf f N ++ [(z N, f N)] := by
      simp [logOf, List.range_succ]
    rw [hs, List.find?_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · rw [find_some f N i h]; rfl
    · subst h; rw [find_none]; simp

theorem fresh (f : ℕ → Digest) (N : ℕ) : z N ∉ (logOf f N).map Prod.fst := by
  simp only [logOf, List.map_map, List.mem_map, List.mem_range, Function.comp_def, not_exists,
    not_and]
  intro j hj h; have := z_inj h; omega

theorem logOf_succ (f : ℕ → Digest) (N : ℕ) (a : Digest) :
    logOf (Function.update f N a) (N + 1) = logOf f N ++ [(z N, a)] := by
  simp only [logOf, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    Function.update_self]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  rw [Function.update_of_ne (by omega)]

instance : Finite Digest := Finite.of_equiv _ digestEquiv.symm

/-! ## Product: a challenge spread over `k` answers -/

/-- Ask `z i, …, z (i+n-1)`; accept iff every answer satisfies `t`. -/
def chk (t : Digest → Bool) : ℕ → ℕ → OProg Bool
  | _, 0 => .ret true
  | i, n + 1 => .query (z i) fun a => if t a then chk t (i + 1) n else .ret false

/-- The `k`-query verifier: it ignores the statement and the proof. -/
def Vprod (t : Digest → Bool) (k : ℕ) (_ : Digest) (_ : Proof) : OProg Bool := chk t 0 k

theorem runLog_chk (t : Digest → Bool) (L : Log) : ∀ n i,
    (∀ j, i ≤ j → j < i + n → ∃ a, t a = true ∧
      L.find? (fun e => decide (e.1 = z j)) = some (z j, a)) →
    (chk t i n).runLog L = some true
  | 0, _, _ => rfl
  | n + 1, i, h => by
    obtain ⟨a, ha, hf⟩ := h i le_rfl (by omega)
    simp only [chk, OProg.runLog, hf, Option.bind_some, ha, ite_true]
    exact runLog_chk t L n (i + 1) fun j h1 h2 => h j (by omega) (by omega)

/-- **Product probe.** For a relation with a witnessless statement `c₀`, every bounded knowledge
state of the `k`-query verifier has `ε · 2^256 ≥ |T|`, whatever `k`. -/
theorem eps_ge_density (t : Digest → Bool) (k : ℕ) {R : Digest → Wit → Prop} (c₀ : Digest)
    (hR : ∀ w, ¬ R c₀ w) {E : Digest → Proof → Log → Option Wit} (ks : KState R (Vprod t k) E)
    {ε : ℝ≥0} (hb : ks.Bounded ε) :
    (Nat.card {a // t a = true} : ℝ≥0) ≤ ε * Nat.card Digest := by
  by_contra hlt
  push Not at hlt
  have hpick : ∀ L q, ∃ a, t a = true ∧ ¬ ks.bad L q a := by
    intro L q
    by_contra hno
    push Not at hno
    have h1 : Nat.card {a // t a = true} ≤ Nat.card {a // ks.bad L q a} :=
      Nat.card_le_card_of_injective (fun x => ⟨x.1, hno x.1 x.2⟩)
        (fun x y h => Subtype.ext (by simpa using h))
    have h2 : (Nat.card {a // ks.bad L q a} : ℝ≥0) < Nat.card {a // t a = true} :=
      (hb L q).trans_lt hlt
    exact absurd h1 (not_le.mpr (by exact_mod_cast h2))
  have hbuild : ∀ N, ∃ f : ℕ → Digest, ks.good (logOf f N) ∧ ∀ j < N, t (f j) = true := by
    intro N
    induction N with
    | zero => exact ⟨fun _ => Vector.replicate 32 0, ks.empty, by simp⟩
    | succ N ih =>
      obtain ⟨f, hg, ht⟩ := ih
      obtain ⟨a, ha, hnb⟩ := hpick (logOf f N) (z N)
      refine ⟨Function.update f N a, ?_, ?_⟩
      · rw [logOf_succ]; exact ks.step _ _ _ hg (fresh f N) hnb
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · rw [Function.update_of_ne (by omega)]; exact ht j hj
        · subst hj; rw [Function.update_self]; exact ha
  obtain ⟨f, hg, ht⟩ := hbuild k
  have hacc : (Vprod t k c₀ ByteArray.empty).runLog (logOf f k) = some true :=
    runLog_chk t _ k 0 fun j _ hj => ⟨f j, ht j (by omega), find_some f k j (by omega)⟩
  obtain ⟨w, _, hw⟩ := ks.final _ c₀ _ hg hacc
  exact hR w hw

/-- "The first byte is zero": `2^248` of the `2^256` answers. -/
def t0 (a : Digest) : Bool := decide (a[0] = 0)

theorem card_t0 : Nat.card {a : Digest // t0 a = true} = 2 ^ 248 := by
  have e1 : {a : Digest // t0 a = true} ≃ {f : Fin 32 → Fin 256 // f 0 = 0} :=
    digestEquiv.subtypeEquiv fun a => by
      simp only [t0, decide_eq_true_eq, digestEquiv, Equiv.coe_fn_mk]
      constructor
      · intro h; simp [h]
      · intro h
        have : a[0].toFin = (0 : UInt8).toFin := by simpa using h
        exact UInt8.toFin_inj.mp this
  have e2 : {f : Fin 32 → Fin 256 // f 0 = 0} ≃ (Fin 31 → Fin 256) :=
    { toFun := fun f => Fin.tail f.1
      invFun := fun g => ⟨Fin.cons 0 g, rfl⟩
      left_inv := fun f => Subtype.ext (by
        conv_rhs => rw [← Fin.cons_self_tail f.1]
        rw [f.2])
      right_inv := fun g => Fin.tail_cons _ _ }
  rw [Nat.card_congr (e1.trans e2)]
  simp

/-- **A 16-query verifier with ROM error `2^-128` has no knowledge state below `2^-8`.** -/
theorem product16_ge {R : Digest → Wit → Prop} (c₀ : Digest) (hR : ∀ w, ¬ R c₀ w)
    {E : Digest → Proof → Log → Option Wit} (ks : KState R (Vprod t0 16) E) {ε : ℝ≥0}
    (hb : ks.Bounded ε) : (2 : ℝ≥0)⁻¹ ^ 8 ≤ ε := by
  have h := eps_ge_density t0 16 c₀ hR ks hb
  rw [card_t0, card_digest] at h
  have h' : (2 : ℝ≥0) ^ 248 ≤ ε * 2 ^ 256 := by exact_mod_cast h
  have e : (2 : ℝ≥0)⁻¹ ^ 8 * 2 ^ 256 = 2 ^ 248 := by
    rw [inv_pow, show (2 : ℝ≥0) ^ 256 = 2 ^ 8 * 2 ^ 248 by norm_num, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  rw [← e] at h'
  exact le_of_mul_le_mul_right h' (by positivity)

theorem product16_not_capped {R : Digest → Wit → Prop} (c₀ : Digest) (hR : ∀ w, ¬ R c₀ w)
    {E : Digest → Proof → Log → Option Wit} (ks : KState R (Vprod t0 16) E) :
    ¬ ks.Bounded errorCap := fun hb => by
  have h := product16_ge c₀ hR ks hb
  rw [errorCap] at h
  have : (2 : ℝ≥0)⁻¹ ^ 128 < (2 : ℝ≥0)⁻¹ ^ 8 :=
    pow_lt_pow_right_of_lt_one₀ (by positivity) (by norm_num) (by norm_num)
  exact absurd h (not_le.mpr this)

/-! ## Collision: the binding half of a Merkle commitment -/

/-- A proof naming the queries `z i` and `z j`: `pair i j` zero bytes. -/
def pairProof (i j : ℕ) : Proof := ⟨Array.replicate (Nat.pair i j) 0⟩

/-- Accept iff the proof names two distinct queries with equal answers. -/
def Vcol (_ : Digest) (π : Proof) : OProg Bool :=
  .query (z (Nat.unpair π.size).1) fun a => .query (z (Nat.unpair π.size).2) fun b =>
    .ret (decide ((Nat.unpair π.size).1 ≠ (Nat.unpair π.size).2) && decide (a = b))

theorem pairProof_size (i j : ℕ) : (pairProof i j).size = Nat.pair i j := by
  simp [pairProof, ByteArray.size]

section
variable {R : Digest → Wit → Prop} {c₀ : Digest} (hR : ∀ w, ¬ R c₀ w)
  {E : Digest → Proof → Log → Option Wit} (ks : KState R Vcol E)
include hR

/-- In a good log of distinct queries, every earlier answer is bad for the next query. -/
theorem all_bad (f : ℕ → Digest) (N : ℕ) (hg : ks.good (logOf f N)) (i : ℕ) (hi : i < N) :
    ks.bad (logOf f N) (z N) (f i) := by
  by_contra hnb
  have hg' := ks.step _ _ _ hg (fresh f N) hnb
  have hacc : (Vcol c₀ (pairProof i N)).runLog (logOf f N ++ [(z N, f i)]) = some true := by
    simp only [Vcol, pairProof_size, Nat.unpair_pair, OProg.runLog, List.find?_append,
      find_some f N i hi, find_none, Option.some_or, Option.none_or, Option.bind_some]
    simp [List.find?, Nat.ne_of_lt hi]
  obtain ⟨w, _, hw⟩ := ks.final _ c₀ _ hg' hacc
  exact hR w hw

/-- **Collision probe.** No knowledge state whose bad sets have at most `K` answers with
`2K < 2^256`. -/
theorem collision_no_bound (K : ℕ) (hK : ∀ L q, Nat.card {a // ks.bad L q a} ≤ K)
    (h2 : 2 * K < 2 ^ 256) : False := by
  have hcard : Nat.card Digest = 2 ^ 256 := card_digest
  have hbuild : ∀ N, N ≤ K + 1 → ∃ f : ℕ → Digest, ks.good (logOf f N) ∧
      ∀ i < N, ∀ j < N, f i = f j → i = j := by
    intro N
    induction N with
    | zero => intro _; exact ⟨fun _ => Vector.replicate 32 0, ks.empty, by simp⟩
    | succ N ih =>
      intro hN
      obtain ⟨f, hg, hinj⟩ := ih (by omega)
      have hnew : ∃ a, (∀ i < N, f i ≠ a) ∧ ¬ ks.bad (logOf f N) (z N) a := by
        by_contra hno
        push Not at hno
        have hs : Function.Surjective
            (Sum.elim (fun i : Fin N => f i) (fun b : {a // ks.bad (logOf f N) (z N) a} => b.1)) := by
          intro a
          by_cases hb : ks.bad (logOf f N) (z N) a
          · exact ⟨.inr ⟨a, hb⟩, rfl⟩
          · have : ∃ i < N, f i = a := by
              by_contra hne; push Not at hne; exact hb (hno a hne)
            obtain ⟨i, hi, he⟩ := this
            exact ⟨.inl ⟨i, hi⟩, he⟩
        have : Finite {a // ks.bad (logOf f N) (z N) a} := Subtype.finite
        have := Nat.card_le_card_of_surjective _ hs
        have hfin : Nat.card (Fin N) = N := by simp
        rw [Nat.card_sum, hfin, hcard] at this
        have := hK (logOf f N) (z N)
        omega
      obtain ⟨a, hfa, hnb⟩ := hnew
      refine ⟨Function.update f N a, ?_, ?_⟩
      · rw [logOf_succ]; exact ks.step _ _ _ hg (fresh f N) hnb
      · intro i hi j hj hij
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at hij
          exact hinj i hi j hj hij
        · rw [Function.update_of_ne (by omega), Function.update_self] at hij
          exact absurd hij (hfa i hi)
        · rw [Function.update_self, Function.update_of_ne (by omega)] at hij
          exact absurd hij.symm (hfa j hj)
        · rfl
  obtain ⟨f, hg, hinj⟩ := hbuild (K + 1) le_rfl
  have hle : K + 1 ≤ Nat.card {a // ks.bad (logOf f (K + 1)) (z (K + 1)) a} := by
    have := Nat.card_le_card_of_injective
      (fun i : Fin (K + 1) => (⟨f i, all_bad hR ks f (K + 1) hg i i.2⟩ :
        {a // ks.bad (logOf f (K + 1)) (z (K + 1)) a}))
      (fun x y h => Fin.ext (hinj x x.2 y y.2 (congrArg Subtype.val h)))
    simpa using this
  have := hK (logOf f (K + 1)) (z (K + 1))
  omega

/-- **The collision verifier has no knowledge state at the contract's cap.** -/
theorem collision_not_capped : ¬ ks.Bounded errorCap := fun hb =>
  collision_no_bound hR ks (2 ^ 128) (fun L q => by
    have h := hb L q
    rw [card_digest, errorCap] at h
    have h' : (Nat.card {a // ks.bad L q a} : ℝ≥0) ≤ ((2 ^ 128 : ℕ) : ℝ≥0) := by
      refine h.trans (le_of_eq ?_)
      rw [inv_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
        show (2 : ℝ≥0) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add],
        inv_mul_cancel_left₀ (by positivity)]
    exact_mod_cast h') (by norm_num)

end

/-! ## The proposed fix, positive control: `Bounded` only on logs shorter than a cap -/

/-- `Bounded ε` restricted to logs of fewer than `N` entries (the fix of ADV-M1). Beyond the cap
every answer may be bad, so `step` no longer forces `good` onto long logs. -/
def BoundedBelow {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} (k : KState R V E) (ε : ℝ≥0) (N : ℕ) : Prop :=
  ∀ L q, L.length < N → (Nat.card {a // k.bad L q a} : ℝ≥0) ≤ ε * Nat.card Digest

theorem runLog_Vcol {L : Log} {c : Digest} {π : Proof} (h : (Vcol c π).runLog L = some true) :
    ∃ e₁ ∈ L, ∃ e₂ ∈ L, e₁.1 ≠ e₂.1 ∧ e₁.2 = e₂.2 := by
  simp only [Vcol, OProg.runLog] at h
  cases h1 : L.find? (fun e => decide (e.1 = z (Nat.unpair π.size).1)) with
  | none => simp [h1] at h
  | some e₁ =>
    cases h2 : L.find? (fun e => decide (e.1 = z (Nat.unpair π.size).2)) with
    | none => simp [h1, h2] at h
    | some e₂ =>
      simp only [h1, h2, Option.bind_some, Option.some.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at h
      have q1 : e₁.1 = z (Nat.unpair π.size).1 := by simpa using List.find?_some h1
      have q2 : e₂.1 = z (Nat.unpair π.size).2 := by simpa using List.find?_some h2
      refine ⟨e₁, List.mem_of_find?_eq_some h1, e₂, List.mem_of_find?_eq_some h2, ?_, h.2⟩
      rw [q1, q2]; exact fun he => h.1 (z_inj he)

/-- With the length cap `2^128`, the collision verifier has a knowledge state bounded at
`errorCap` for the empty relation: good logs are short and collision-free. -/
def colState : KState (fun _ _ => False) Vcol (fun _ _ _ => none) where
  good L := L.length ≤ 2 ^ 128 ∧ (L.map Prod.snd).Nodup
  bad L _ a := 2 ^ 128 ≤ L.length ∨ a ∈ L.map Prod.snd
  empty := by simp
  step L q a hL _ hb := by
    simp only [not_or, not_le] at hb
    refine ⟨by simp; omega, ?_⟩
    rw [List.map_append, List.map_singleton]
    exact hL.2.append (List.nodup_singleton _) (List.disjoint_singleton.mpr hb.2)
  final L c π hL h := by
    exfalso
    obtain ⟨e₁, h₁, e₂, h₂, hq, ha⟩ := runLog_Vcol h
    exact hq (congrArg Prod.fst (List.inj_on_of_nodup_map hL.2 h₁ h₂ ha))

theorem colState_bounded : BoundedBelow colState errorCap (2 ^ 128) := by
  intro L q hL
  have h1 : Nat.card {a // colState.bad L q a} ≤ L.length := by
    have : ∀ a, colState.bad L q a ↔ a ∈ L.map Prod.snd := fun a => by
      simp only [colState]; constructor
      · rintro (h | h); · omega
        · exact h
      · exact Or.inr
    calc Nat.card {a // colState.bad L q a} = Nat.card {a // a ∈ L.map Prod.snd} :=
          Nat.card_congr (Equiv.subtypeEquivRight this)
      _ ≤ (L.map Prod.snd).length := by
          have hs : Function.Surjective (fun i : Fin (L.map Prod.snd).length =>
              (⟨(L.map Prod.snd)[i], List.getElem_mem _⟩ : {a // a ∈ L.map Prod.snd})) := by
            rintro ⟨a, ha⟩
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
            exact ⟨⟨i, hi⟩, rfl⟩
          simpa using Nat.card_le_card_of_surjective _ hs
      _ = L.length := List.length_map _
  rw [card_digest, errorCap]
  calc (Nat.card {a // colState.bad L q a} : ℝ≥0) ≤ ((2 ^ 128 : ℕ) : ℝ≥0) := by
        exact_mod_cast (h1.trans hL.le)
    _ = (2 : ℝ≥0)⁻¹ ^ 128 * ((2 ^ 256 : ℕ) : ℝ≥0) := by
        rw [inv_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
          show (2 : ℝ≥0) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add],
          inv_mul_cancel_left₀ (by positivity)]

end AdvProbe

#print axioms AdvProbe.product16_not_capped
#print axioms AdvProbe.collision_not_capped
#print axioms AdvProbe.colState_bounded

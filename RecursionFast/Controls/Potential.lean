/-
# Controls: the potential against the boolean form, and the length guard    (V3-KS-A1, A2, A4)

Two toy verifiers whose random-oracle error is far below `errorCap`, for the empty relation (so
the extractor must never be needed: every accepted proof must be priced into the potential).

**`twoLucky` (a challenge spread over two answers; F1 §2, ADV-M3).** `V` asks two fixed queries
and accepts iff both answers are *lucky*: their first 12 bytes are zero (`2^160` of the `2^256`
digests). Its error is `2^-96 · 2^-96 = 2^-192`.
* `twoLucky_kstate` (positive): a potential at `ε = 2^-192`: the probability that `V` accepts
  given the answers so far (`2^-96` per unanswered query, `1` or `0` per answered one), except `0`
  while neither is answered. The first answer raises the average by `2^-192`, the second not at
  all (a martingale). So `KS` holds at the cap with `qV = 2` (`twoLucky_ks`).
* `twoLucky_bool_ge`, `twoLucky_no_bool_kstate` (negative): every boolean state (the Stage S1
  form) has at least `2^160` bad answers to one of the two queries, so `ε ≥ 2^-96`, and none is
  bounded at `errorCap`, **even on short logs** (`BoundedBelow`): the length guard does not help;
  the potential does.

**`Vcol` (collision resistance: the binding half of a Merkle commitment; F1 §1, ADV-M2).** `V`
accepts a proof naming two distinct queries with equal answers. Its error is at most
`(Q + 2)^2 / 2^257`.
* `collision_no_bool_kstate` (negative): no boolean state is bounded at `errorCap` over logs of
  every length: the probe's induction builds a good log of `2^128 + 1` distinct answers, every one
  of which is then bad for the next query.
* `colBool_below`, `colState` (positive): with the length guard, the boolean state "the answers
  so far are distinct" is bounded at `2^-192` on logs of fewer than `logCap` entries, so it embeds
  as a potential and `KS` holds at the cap (`collision_ks`).
So the guard is what lets the binding of a commitment be charged at all.

**Simplified from the F1 proposal (V3-KS-A4).** F1 §4.6 proposed `merkleToy` (§1.2: dangling
Fiat–Shamir transcripts over one committed word, then a hit on one of `2^128 + 1` roots). `Vcol`
is its collision half, kernel-checked by the ADV1 probe (`collision_not_capped`) and ported here;
the dangling-target half is the same counting argument over a longer log and is not built. Not
shown either: that a *potential* (not only a boolean state) for `Vcol` needs the guard at
`errorCap` (F1 §4.1, third row, a paper argument).
-/
import RecursionFast.Library.Security
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.Basic.Finite.Sum

open scoped NNReal

namespace RecursionFast.Controls.Potential
open RecursionFast

/-! ## Numbered queries and the logs they make -/

/-- Query number `i`: `i` zero bytes. -/
def z (i : ℕ) : ByteArray := ⟨Array.replicate i 0⟩

theorem z_size (i : ℕ) : (z i).size = i := by simp [z, ByteArray.size]

theorem z_inj {i j : ℕ} (h : z i = z j) : i = j := by
  simpa [z_size] using congrArg ByteArray.size h

/-- The first answer the log gives to `q`. -/
def ans (L : Log) (q : ByteArray) : Option Digest := (L.find? fun e => e.1 = q).map Prod.snd

theorem ans_append_ne {L : Log} {q q' : ByteArray} (a : Digest) (h : q ≠ q') :
    ans (L ++ [(q, a)]) q' = ans L q' := by
  cases hf : L.find? (fun e => decide (e.1 = q')) <;> simp [ans, List.find?_append, hf, h]

theorem find_fresh {L : Log} {q : ByteArray} (h : q ∉ L.map Prod.fst) :
    L.find? (fun e => decide (e.1 = q)) = none :=
  List.find?_eq_none.mpr fun e he hq => h (List.mem_map.mpr ⟨e, he, by simpa using hq⟩)

theorem ans_fresh {L : Log} {q : ByteArray} (h : q ∉ L.map Prod.fst) : ans L q = none := by
  simp [ans, find_fresh h]

theorem ans_append_fresh {L : Log} {q : ByteArray} (a : Digest) (h : q ∉ L.map Prod.fst) :
    ans (L ++ [(q, a)]) q = some a := by
  simp [ans, List.find?_append, find_fresh h]

/-- A query program's first step reads the log through `ans`. -/
theorem runLog_query {L : Log} {q : ByteArray} {k : Digest → OProg Bool} :
    (OProg.query q k).runLog L = (ans L q).bind fun a => (k a).runLog L := by
  simp only [OProg.runLog, ans]
  cases L.find? (fun e => decide (e.1 = q)) <;> rfl

/-! ## `twoLucky`: a challenge spread over two answers -/

/-- A lucky answer: its first 12 bytes are zero. -/
def lucky (a : Digest) : Prop := ∀ i : Fin 12, a[i.castAdd 20] = 0

instance : DecidablePred lucky := fun _ => inferInstanceAs (Decidable (∀ _ : Fin 12, _))

/-- The two queries. -/
def q₁ : ByteArray := z 0

/-- The two queries. -/
def q₂ : ByteArray := z 1

theorem q₁_ne_q₂ : q₁ ≠ q₂ := fun h => absurd (z_inj h) (by decide)

/-- Ask `q₁` and `q₂`; accept iff both answers are lucky. -/
def twoLucky (_ : Digest) (_ : Proof) : OProg Bool :=
  .query q₁ fun a => .query q₂ fun b => .ret (decide (lucky a) && decide (lucky b))

/-- Lucky digests are the 20 free bytes after 12 zero bytes. -/
def luckyEquiv : {a // lucky a} ≃ (Fin 20 → Fin 256) :=
  ((digestEquiv.subtypeEquiv (p := lucky) (q := fun f => ∀ i : Fin 12, f (i.castAdd 20) = 0)
    fun a => forall_congr' fun i => by
      simp only [digestEquiv, Equiv.coe_fn_mk]
      exact ⟨fun h => by simp [h], fun h => UInt8.toFin_inj.mp (by simpa using h)⟩).trans
  ((Fin.appendEquiv 12 20).symm.subtypeEquiv (q := fun p => p.1 = 0) fun f => by
      refine ⟨fun h => funext fun i => ?_, fun h i => ?_⟩
      · simpa [Fin.appendEquiv] using h i
      · have := congrFun h i
        simp only [Fin.appendEquiv, Equiv.coe_fn_symm_mk] at this
        simpa using this)).trans
  { toFun := fun p => p.1.2
    invFun := fun g => ⟨(0, g), rfl⟩
    left_inv := fun ⟨⟨u, v⟩, h⟩ => by simp only at h; subst h; rfl
    right_inv := fun _ => rfl }

/-- There are `2^160` lucky digests. -/
theorem card_lucky : Fintype.card {a // lucky a} = 2 ^ 160 := by
  rw [Fintype.card_congr luckyEquiv]; simp

/-- The chance that an answer to one of the two queries is lucky: `2^-96` before it is answered,
`1` or `0` after. -/
noncomputable def chance : Option Digest → ℝ≥0
  | none => (2 : ℝ≥0)⁻¹ ^ 96
  | some a => if lucky a then 1 else 0

/-- **The potential**: the probability that `twoLucky` accepts given the answers in the log, and
`0` while neither query is answered. -/
noncomputable def μ2 (L : Log) : ℝ≥0 :=
  if ans L q₁ = none ∧ ans L q₂ = none then 0 else chance (ans L q₁) * chance (ans L q₂)

/-- The sum of `chance` over the answers is the `2^160` lucky digests. -/
theorem sum_chance : ∑ a : Digest, chance (some a) = 2 ^ 160 := by
  simp only [chance]
  rw [Finset.sum_boole, ← Fintype.card_subtype, card_lucky]; norm_num

/-- Answering one of the two queries, the other's answer being `o`. -/
theorem step_one (o : Option Digest) (μL : ℝ≥0) (f : Digest → ℝ≥0)
    (hf : ∀ a, f a = chance (some a) * chance o)
    (hμ : μL = if o = none then 0 else (2 : ℝ≥0)⁻¹ ^ 96 * chance o) :
    ∑ a, f a ≤ (μL + (2 : ℝ≥0)⁻¹ ^ 192) * Fintype.card Digest := by
  simp only [hf, ← Finset.sum_mul, sum_chance, fintype_card_digest, Nat.cast_pow,
    Nat.cast_ofNat]
  have e1 : (2 : ℝ≥0)⁻¹ ^ 96 * 2 ^ 256 = 2 ^ 160 := by
    apply NNReal.coe_injective; push_cast; norm_num
  have e2 : (2 : ℝ≥0)⁻¹ ^ 192 * 2 ^ 256 = 2 ^ 160 * (2 : ℝ≥0)⁻¹ ^ 96 := by
    apply NNReal.coe_injective; push_cast; norm_num
  rcases o with _ | b
  · simp only [hμ, ↓reduceIte, zero_add, e2, chance]; rfl
  · simp only [reduceCtorEq, ↓reduceIte] at hμ
    rw [hμ, add_mul, mul_right_comm, e1, mul_comm]
    exact le_add_right le_rfl

/-- **`twoLucky` has a potential at `ε = 2^-192`**, for the empty relation and every extractor. -/
noncomputable def twoLucky_kstate (E : Digest → Proof → Log → Option Wit) :
    KState (fun _ _ => False) twoLucky E ((2 : ℝ≥0)⁻¹ ^ 192) where
  μ := μ2
  empty := by simp [μ2, ans]
  step L q _ _ hq := by
    by_cases h1 : q = q₁
    · subst h1
      refine step_one (ans L q₂) _ _ (fun a => ?_) ?_
      · simp [μ2, ans_append_fresh a hq, ans_append_ne a q₁_ne_q₂]
      · rcases h : ans L q₂ <;> simp [μ2, ans_fresh hq, h, chance]
    by_cases h2 : q = q₂
    · subst h2
      refine step_one (ans L q₁) _ _ (fun a => ?_) ?_
      · simp [μ2, ans_append_fresh a hq, ans_append_ne a q₁_ne_q₂.symm, mul_comm]
      · rcases h : ans L q₁ <;> simp [μ2, ans_fresh hq, h, chance, mul_comm]
    · have he : ∀ a, μ2 (L ++ [(q, a)]) = μ2 L := fun a => by
        simp [μ2, ans_append_ne a (Ne.symm (Ne.symm h1)), ans_append_ne a h2]
      simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_comm]; gcongr; exact le_self_add
  final L c π _ hμ hacc := by
    exfalso
    simp only [twoLucky, runLog_query] at hacc
    rcases h1 : ans L q₁ with _ | a <;> rcases h2 : ans L q₂ with _ | b <;>
      simp [h1, h2, OProg.runLog] at hacc
    simp [μ2, h1, h2, chance, hacc.1, hacc.2] at hμ

/-- `2^-192` is within the cap. -/
theorem le_errorCap_192 : (2 : ℝ≥0)⁻¹ ^ 192 ≤ errorCap :=
  pow_le_pow_of_le_one (by positivity) (by norm_num) (by norm_num)

/-- **`twoLucky` is knowledge-sound at the cap** with two verifier queries. -/
theorem twoLucky_ks (E : Digest → Proof → Log → Option Wit) :
    KS (fun _ _ => False) twoLucky E errorCap 2 :=
  ⟨⟨(twoLucky_kstate E).mono le_errorCap_192⟩, fun _ _ _ => by simp [twoLucky, OProg.queries]⟩

/-- A boolean state with fewer bad answers than lucky ones leaves a lucky answer that is not
bad. -/
theorem exists_lucky {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} (k : BoolKState R V E) (L : Log) (q : ByteArray)
    (h : Nat.card {a // k.bad L q a} < 2 ^ 160) : ∃ a, lucky a ∧ ¬ k.bad L q a := by
  by_contra hno
  push Not at hno
  have := Nat.card_le_card_of_injective (fun x : {a // lucky a} => (⟨x.1, hno x.1 x.2⟩ :
    {a // k.bad L q a})) fun x y h => Subtype.ext (by simpa using h)
  rw [Nat.card_eq_fintype_card (α := {a // lucky a}), card_lucky] at this
  omega

/-- **No boolean state below `2^-96`**: every boolean state of `twoLucky` for the empty relation,
bounded at `ε` on short logs, has `ε ≥ 2^-96`. -/
theorem twoLucky_bool_ge {E : Digest → Proof → Log → Option Wit}
    (k : BoolKState (fun _ _ => False) twoLucky E) {ε : ℝ≥0} (h : k.BoundedBelow ε) :
    (2 : ℝ≥0)⁻¹ ^ 96 ≤ ε := by
  by_contra hlt
  push Not at hlt
  have hfew : ∀ L q, L.length < logCap → Nat.card {a // k.bad L q a} < 2 ^ 160 := by
    intro L q hL
    have hb := h L q hL
    rw [card_digest] at hb
    have : ε * ((2 ^ 256 : ℕ) : ℝ≥0) < ((2 ^ 160 : ℕ) : ℝ≥0) := by
      have e : (2 : ℝ≥0)⁻¹ ^ 96 * ((2 ^ 256 : ℕ) : ℝ≥0) = ((2 ^ 160 : ℕ) : ℝ≥0) := by
        apply NNReal.coe_injective; push_cast; norm_num
      rw [← e]; exact mul_lt_mul_of_pos_right hlt (by positivity)
    exact_mod_cast hb.trans_lt this
  obtain ⟨a, ha, hna⟩ := exists_lucky k [] q₁ (hfew _ _ (by simp [logCap]))
  have g1 := k.step [] q₁ a k.empty (by simp) hna
  obtain ⟨b, hb, hnb⟩ := exists_lucky k ([] ++ [(q₁, a)]) q₂ (hfew _ _ (by simp [logCap]))
  have g2 := k.step _ q₂ b g1 (by simpa using q₁_ne_q₂.symm) hnb
  obtain ⟨w, -, hw⟩ := k.final _ (Vector.replicate 32 0) .empty g2 (by
    simp [twoLucky, runLog_query, ans, OProg.runLog, List.find?, q₁_ne_q₂, ha, hb])
  exact hw

/-- **`twoLucky` has no boolean state at the cap**, even on short logs; with the potential it
is knowledge-sound at the cap (`twoLucky_ks`). -/
theorem twoLucky_no_bool_kstate {E : Digest → Proof → Log → Option Wit}
    (k : BoolKState (fun _ _ => False) twoLucky E) : ¬ k.BoundedBelow errorCap := fun h =>
  (pow_lt_pow_right_of_lt_one₀ (by positivity) (by norm_num) (by norm_num) :
    (2 : ℝ≥0)⁻¹ ^ 128 < (2 : ℝ≥0)⁻¹ ^ 96).not_ge (twoLucky_bool_ge k h)

/-! ## `Vcol`: collisions, and the length guard -/

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
  {E : Digest → Proof → Log → Option Wit} (ks : BoolKState R Vcol E)
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

/-- **No boolean state whose bad sets have at most `K` answers** with `2K < 2^256`, over logs of
every length (the ADV1 probe). -/
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
        have hs : Function.Surjective (Sum.elim (fun i : Fin N => f i)
            (fun b : {a // ks.bad (logOf f N) (z N) a} => b.1)) := by
          intro a
          by_cases hb : ks.bad (logOf f N) (z N) a
          · exact ⟨.inr ⟨a, hb⟩, rfl⟩
          · have : ∃ i < N, f i = a := by
              by_contra hne; push Not at hne; exact hb (hno a hne)
            obtain ⟨i, hi, he⟩ := this
            exact ⟨.inl ⟨i, hi⟩, he⟩
        have := Nat.card_le_card_of_surjective _ hs
        rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin, hcard] at this
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

/-- **Without the length guard, the collision verifier has no boolean state at the cap.** -/
theorem collision_no_bool_kstate : ¬ ks.Bounded errorCap := fun hb =>
  collision_no_bound hR ks (2 ^ 128) (fun L q => by
    have h := hb L q
    rw [card_digest, errorCap] at h
    have h' : (Nat.card {a // ks.bad L q a} : ℝ≥0) ≤ ((2 ^ 128 : ℕ) : ℝ≥0) := by
      refine h.trans (le_of_eq ?_)
      apply NNReal.coe_injective; push_cast; norm_num
    exact_mod_cast h') (by norm_num)

end

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

/-- The boolean state "the answers so far are distinct", for the empty relation: a repeated
answer is the bad event. -/
def colBool : BoolKState (fun _ _ => False) Vcol (fun _ _ _ => none) where
  good L := (L.map Prod.snd).Nodup
  bad L _ a := a ∈ L.map Prod.snd
  empty := List.nodup_nil
  step L q a hL _ hb := by
    rw [List.map_append, List.map_singleton]
    exact hL.append (List.nodup_singleton _) (List.disjoint_singleton.mpr hb)
  final L c π hL h := by
    exfalso
    obtain ⟨e₁, h₁, e₂, h₂, hq, ha⟩ := runLog_Vcol h
    exact hq (congrArg Prod.fst (List.inj_on_of_nodup_map hL h₁ h₂ ha))

/-- **With the length guard, the collision charge is `2^-192`**: on logs of fewer than `logCap`
entries, at most `2^64` answers repeat an earlier one. -/
theorem colBool_below : colBool.BoundedBelow ((2 : ℝ≥0)⁻¹ ^ 192) := by
  intro L q hL
  have h1 : Nat.card {a // colBool.bad L q a} ≤ L.length := by
    calc Nat.card {a // colBool.bad L q a} = Nat.card {a // a ∈ L.map Prod.snd} := rfl
      _ ≤ (L.map Prod.snd).length := by
          have hs : Function.Surjective fun i : Fin (L.map Prod.snd).length =>
              (⟨(L.map Prod.snd)[i], List.getElem_mem _⟩ : {a // a ∈ L.map Prod.snd}) := by
            rintro ⟨a, ha⟩
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
            exact ⟨⟨i, hi⟩, rfl⟩
          simpa using Nat.card_le_card_of_surjective _ hs
      _ = L.length := List.length_map _
  rw [card_digest]
  calc (Nat.card {a // colBool.bad L q a} : ℝ≥0) ≤ ((2 ^ 64 : ℕ) : ℝ≥0) := by
        exact_mod_cast h1.trans (le_of_lt hL)
    _ = (2 : ℝ≥0)⁻¹ ^ 192 * ((2 ^ 256 : ℕ) : ℝ≥0) := by
        apply NNReal.coe_injective; push_cast; norm_num

/-- The same state over logs of every length is not bounded at the cap. -/
theorem colBool_not_bounded : ¬ colBool.Bounded errorCap :=
  collision_no_bool_kstate (c₀ := Vector.replicate 32 0) (fun _ h => h) colBool

/-- **The collision verifier's potential**, through the guard: `KState.ofBool` of `colBool`. -/
noncomputable def colState : KState (fun _ _ => False) Vcol (fun _ _ _ => none) errorCap :=
  (KState.ofBool colBool colBool_below).mono le_errorCap_192

/-- **The collision verifier is knowledge-sound at the cap** with two verifier queries. -/
theorem collision_ks : KS (fun _ _ => False) Vcol (fun _ _ _ => none) errorCap 2 :=
  ⟨⟨colState⟩, fun _ _ _ => by simp [Vcol, OProg.queries]⟩

end RecursionFast.Controls.Potential

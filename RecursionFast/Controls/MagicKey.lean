/-
# Control (negative, S5-M1 → S5-A10): `live` must name the indexer's keys

Adopted from the S5 review's probe `probes/s5/review/MagicKey.lean`. `Protocol.Secure` constrains
`P.verify` only on keys `P.VK L`, so a secure protocol may accept everything under a "magic" key
that no layout has. `toyCM` is the secure toy (`Controls/Toy.lean`) with its message
Merkle-committed in two leaves (so the rounds section is a 32-byte root) and a magic branch in the
verifier (`vk 0 = 2` accepts outright; `toyVK` is never 2).

* `toyCM_secure`: it is secure at every class in range (the magic branch is invisible to
  `Secure`).
* `narg_magic`: under a magic key with a 32-byte root every statement has an accepted 32-byte
  tape; `narg_nonmagic`, `narg_indexed`: under any other key, in particular every indexer key, no
  tape is accepted (the first query opens the index oracle, `8·2^28` bytes, beyond the cap).
* `magic_old_live`: the S5-A7 form of `live` (`∃ x' nw, aggOK … = true`) holds, with two magic
  leaves; `toyCM_no_indexed_node`: no node whose keys are indexer keys is accepted.
* **`magic_not_live`**: the S5-A10 field `live` (at the indexer's keys) fails for `toyCM`, for
  every `C`; so `toyCM` has no recursion entry (`magic_no_entry`). The positive counterpart is
  `cmpToy_live` (`Controls/Recursion.lean`).

Residual (S5-A10): a protocol that special-cases the key of a trivially satisfiable layout can
still meet `live`; the benchmark run shows that the benchmark's nodes are provable.
-/
import RecursionFast.Controls.Toy
import RecursionFast.Controls.Certificate
import RecursionFast.Controls.Compile
import RecursionFast.Library.Recursion

namespace RecursionFast.Controls.MagicKey
open RecursionFast RecursionFast.Controls RecursionFast.Controls.Compile Codec
open RecursionFast.Controls.Certificate (h20 takeN_short)

section
variable (k : ℕ) (hk : 20 ≤ k ∧ k ≤ 28)

/-- One round: the toy's message, Merkle-committed in two leaves. -/
def tcShape : Fin 1 → Round := fun _ => .msg ⟨k + 10, k + 9⟩

/-- A key element that `toyVK` never produces. -/
def magic : K := ⟨2⟩

/-- Accept outright under the magic key; otherwise the toy's verifier, reading both leaves. -/
def tcVerify (vk : Fin 1 → K) (x : Stmt) (_ : Challenges (tcShape k)) : QProg Bool :=
  if vk 0 = magic then .done true else
    .query 0 0 fun idx => .query 1 0 fun a => .query 1 1 fun b =>
      .done (toyDecide k vk x idx (a ++ b))

/-- The committed toy with a magic key. -/
abbrev toyCM : Protocol k where
  k_range := hk
  n := 1
  n_le := by decide
  shape := tcShape k
  vkLen := 1
  vkLen_le := by decide
  VK := toyVK k
  idxShape := ⟨k + 8, k + 8⟩
  IDX L := toOracle (k + 8) (eLayout L)
  shape_ok := ⟨fun _ => ⟨Nat.le_succ _, le_refl _⟩, le_refl _, le_refl _⟩
  prover := { next := fun s w _ _ => toOracle (k + 10) (eWit s.1 w),
              output := fun _ _ _ => ((), ()) }
  verify := tcVerify k
  extractor := firstMsgImage k 1
  ε := fun _ => 0

/-- The two leaves of the committed message, in order, are the message. -/
theorem leaves_append (v : OVal ⟨k + 10, k + 9⟩) :
    Oracle.leaf ⟨⟨k + 10, k + 9⟩, v⟩ 0 ++ Oracle.leaf ⟨⟨k + 10, k + 9⟩, v⟩ 1 = List.ofFn v := by
  have h2 : 2 ^ (k + 10) = 2 ^ (k + 9) + 2 ^ (k + 9) := by rw [pow_succ]; ring
  simp only [Oracle.leaf]
  refine List.ext_getElem (by simp [h2]) fun i h1 h2' => ?_
  simp only [List.length_append, List.length_ofFn] at h1
  rw [List.getElem_append]
  split_ifs with hi
  · simp only [List.getElem_ofFn, Oracle.get, zero_mul, zero_add]
    rw [dite_eq_left_of_eq_true (by simp; omega)]
  · simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn, Oracle.get, List.length_ofFn, one_mul]
    rw [dite_eq_left_of_eq_true (by simp; omega)]
    congr 2; omega

/-- The toy's key never holds the magic element. -/
theorem toyVK_ne_magic (L : Layout K) : toyVK k L 0 ≠ magic := by
  unfold toyVK; split_ifs <;> decide

/-- What the committed toy's verifier accepts under its own keys: the toy's decision. -/
theorem tc_accepts_iff (s : Layout K × Stmt) (tr : FullTranscript (tcShape k)) :
    (toyCM k hk).specVerifier s tr = some () ↔ (s, toyWit k s.1 (tr 0)) ∈ relK k := by
  obtain ⟨L, x⟩ := s
  refine Iff.trans ?_ (toyDecide_iff k hk L x (tr 0))
  have e := leaves_append k (tr 0)
  simp only [Protocol.specVerifier, tcVerify, toyVK_ne_magic k L, ite_false, QProg.eval,
    FullTranscript.oracles, tcShape, Round.oracles, OShape.leaves]
  simp [List.ofFn_succ, leaf_zero, e]

/-- No challenge rounds. -/
theorem tc_noChal (c : ChallengeIdx (tcShape k)) : False := by
  have := c.2; simp [tcShape, Round.isMsg] at this

include hk in
/-- The first-message image returns the tables the verifier checks (as for the toy). -/
theorem tc_extractMid {L : Layout K} (hL : L.Admissible k) (x : Stmt)
    (tr : Transcript (tcShape k) (Fin.castSucc 0)) (msg : OVal ⟨k + 10, k + 9⟩)
    (w : Mid 1 (Fin.succ 0)) :
    (((firstMsgImage k 1).toExtractor (tcShape k)).extractMid 0 (L, x) (tr.concat msg) w :
      List (Table K)) = toyWit k L msg := by
  have hL' := Layout.words_length hk.1 hL
  have h36 : 2 ^ (k + 8) ≤ 2 ^ 36 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h38 : 2 ^ (k + 10) ≤ 2 ^ 38 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h12 : 2 ^ (k + 10) ≤ 2 ^ (k + 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hf : 8 ≤ (firstMsgImage k 1).fuel (Fin.castSucc 0) := by
    show 8 ≤ 2 ^ (2 * k + 16)
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ 2 * k + 16))
  rw [firstMsg_extractMid k (tcShape k) 0 (L, x) (tr.concat msg) w
    (by simp [Round.words, tcShape]; omega) (by simp [Round.words, tcShape, witCap]; omega)
    (firstMsgImage k 1) rfl hf]
  have e : (tr.concat msg) (Fin.last 0) = msg := Transcript.concat_last tr msg
  show decTables (L.chips.map Chip.cols)
    (List.ofFn fun i => ((tr.concat msg) (Fin.last 0) i).bits) = _
  rw [e, show (List.ofFn fun i => (msg i).bits) = (List.ofFn msg).map K.bits from
    List.map_ofFn.symm, decTables_map_bits]
  rfl

/-- The toy's knowledge state function, for the committed shape. -/
def tcKSF : KSF (relK k) Set.univ (toyCM k hk).specVerifier
    ((toyCM k hk).extractor.toExtractor (toyCM k hk).shape) where
  toFun := fun m => Fin.cases
    (motive := fun m => Layout K × Stmt → Transcript (tcShape k) m → Mid 1 m → Prop)
    (fun s _ w => (s, w) ∈ relK k)
    (fun _ s tr _ => (s, toyWit k s.1 (tr ⟨0, Nat.succ_pos _⟩)) ∈ relK k) m
  empty := fun _ _ => Iff.rfl
  next := fun m s tr msg w h => by
    obtain ⟨m, hm⟩ := m
    obtain rfl : m = 0 := Subsingleton.elim _ _
    obtain ⟨L, x⟩ := s
    have e : (tr.concat msg) (Fin.last 0) = msg := Transcript.concat_last tr msg
    have h' : ((L, x), toyWit k L msg) ∈ relK k := by
      have h0 : ((L, x), toyWit k L ((tr.concat msg) (Fin.last 0))) ∈ relK k := h
      rwa [e] at h0
    show ((L, x), (((firstMsgImage k 1).toExtractor (tcShape k)).extractMid 0 (L, x)
      (tr.concat msg) w : List (Table K))) ∈ relK k
    rw [tc_extractMid k hk h'.1 x tr msg w]
    exact h'
  full := fun s tr _ _ hV _ => (tc_accepts_iff k hk s tr).mp hV

/-- **`toyCM` is secure**, at every class in range: the magic branch is invisible to `Secure`. -/
theorem toyCM_secure : (toyCM k hk).Secure where
  complete := by
    rintro ⟨L, x⟩ w ⟨hL, hrel⟩ ρ
    refine ⟨(tc_accepts_iff k hk _ _).mpr ⟨hL, ?_⟩, Set.mem_univ _⟩
    show L.rel k x (toyWit k L (toOracle (k + 10) (eWit L w)))
    have h28 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [toyWit, ofFn_toOracle (eWit_length hL hrel), pWit_eWit L w hrel.1
      (fun T hT => lt_of_le_of_lt (rows_le_of_rel hL hrel T hT) h28)]
    exact (rel_trim_iff hL.readsOwn hrel.1).mpr hrel
  sound := ⟨tcKSF k hk, fun _ c _ => (tc_noChal k c).elim⟩
  cap := fun c => (tc_noChal k c).elim

end

/-! ## The compiled argument at class 20 -/

/-- Reading exactly the whole tape. -/
theorem takeN_exact : ∀ (n : ℕ) (t acc : List UInt8), t.length = n →
    takeN n t acc = some (acc.reverse ++ t, [])
  | 0, [], _, _ => by simp [takeN]
  | n + 1, c :: t, acc, h => by
    simp only [takeN]; rw [takeN_exact n t (c :: acc) (by simpa using h)]; simp

/-- Reading leaves at most the tape. -/
theorem takeN_len : ∀ (n : ℕ) (t acc b r : List UInt8), takeN n t acc = some (b, r) →
    r.length ≤ t.length
  | 0, t, acc, b, r, h => by
    simp only [takeN, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact le_rfl
  | _ + 1, [], _, _, _, h => by simp [takeN] at h
  | n + 1, c :: t, acc, b, r, h => by
    simp only [takeN] at h; have := takeN_len n t (c :: acc) b r h; simp; omega

/-- The protocol at class 20. -/
abbrev P20 : Protocol 20 := toyCM 20 h20

/-- **Magic acceptance**: under a magic key with a 32-byte root, every statement has an accepted
tape (any 32 bytes: the root of the message). -/
theorem narg_magic (vkc : VKc 1) (hv : vkc.1 0 = magic) (hr : vkc.2.length = 32) (x : Stmt)
    (t : Tape) (ht : t.length = 32) : NARG cfg2 P20 vkc x t = true := by
  simp [NARG, ht, hr, tapeCap, pass, msgLen, OShape.plain, tcShape, takeN_exact 32 t [] ht,
    tcVerify, hv, runQ]

/-- **No acceptance under any other key**: the verifier's first query opens the index oracle, a
leaf of `8·2^28` bytes, beyond the tape cap. -/
theorem narg_nonmagic (vkc : VKc 1) (hv : vkc.1 0 ≠ magic) (x : Stmt) (t : Tape) :
    NARG cfg2 P20 vkc x t = false := by
  by_cases hc : t.length ≤ tapeCap
  · cases h : takeN 32 t [] with
    | none => simp [NARG, pass, msgLen, OShape.plain, tcShape, h]
    | some p =>
      obtain ⟨b, r⟩ := p
      have hr : r.length < 8 * 2 ^ 28 := by
        have := takeN_len 32 t [] b r h; simp [tapeCap] at hc; omega
      have hs : takeN 2147483648 r [] = none := takeN_short _ _ _ (by simpa using hr)
      simp [NARG, pass, msgLen, OShape.plain, tcShape, h, tcVerify, hv, runQ, views,
        OShape.leaves, readOpening, hs]
  · simp [NARG, hc]

/-- So no tape is accepted under an indexer key. -/
theorem narg_indexed (L : Layout K) (x : Stmt) (t : Tape) :
    NARG cfg2 P20 (index cfg2 P20 L) x t = false :=
  narg_nonmagic _ (toyVK_ne_magic 20 L) x t

/-- A magic key with a 32-byte root. -/
def vkM : VKc 1 := (fun _ => magic, List.replicate 32 0)

/-- **The S5-A7 form of `live` holds** for `toyCM`: two magic leaves (the recursion key may even be
the indexer's key of any `C`). -/
theorem magic_old_live (C : Layout K) : ∃ x' nw, aggOK cfg2 P20 x' nw = true :=
  ⟨_, _, aggOK_leaves cfg2 P20 (index cfg2 P20 C) vkM (commit_length cfg2 _) x0 x0
    (List.replicate 32 0) (List.replicate 32 0) (narg_magic _ rfl rfl _ _ rfl)
    (narg_magic _ rfl rfl _ _ rfl)⟩

/-- **But no node whose keys are indexer keys is accepted**: the benchmark's nodes never are. -/
theorem toyCM_no_indexed_node (C L : Layout K) (x' : Stmt) (nw : NodeWitness 1)
    (hL : nw.vkL = index cfg2 P20 L) (hC : nw.vkC = index cfg2 P20 C) :
    aggOK cfg2 P20 x' nw = false := by
  rcases nw with ⟨vkC, vkL, t₁, t₂, x₁, x₂, π₁, π₂⟩
  simp only at hL hC; subst hL hC
  cases t₁ <;> simp [aggOK, child, narg_indexed]

/-- **`live` fails for `toyCM`** (S5-A10), for every recursion layout `C`. -/
theorem magic_not_live (C : Layout K) :
    ¬ ∃ L x' nw, nw.vkC = index cfg2 P20 C ∧ nw.vkL = index cfg2 P20 L ∧
      aggOK cfg2 P20 x' nw = true :=
  fun ⟨L, x', nw, hC, hL, h⟩ => Bool.ne_true_of_eq_false (toyCM_no_indexed_node C L x' nw hL hC) h

/-- So `toyCM`, although secure, has no recursion entry. -/
theorem magic_no_entry (e : RecursionEntry P20 cfg2) : False := magic_not_live e.C e.live

end RecursionFast.Controls.MagicKey

/-
# Baseline submission: the protocol `P_triv` and its security proof                (UNTRUSTED)

DESIGN §7.3. `P_triv k` is the "send the tables" protocol at class `k`, for every `20 ≤ k ≤ 28`.
It is the organiser's toy protocol (`RecursionFast/Controls/Toy.lean`, `toy`, `toy_secure`),
copied and adapted rather than imported: a submission stands alone and imports only the contract
and the organiser library, never the controls. The changes against the toy are the names and the
extractor's declared fuel split (`trivExtractor`: 8 steps on the call before round 0, which is
exactly what the image runs, and 0 on the output call, which no law reads).

* **Indexer.** `VK L` is one element, `1` iff `L` is admissible at class `k`. The index oracle
  `IDX L` is the serialisation of `L` (`Library/Codec.lean`'s `eLayout`, at most `2^(k+8)`
  elements), one leaf.
* **Prover.** One round sends the serialised tables (`eWit`, at most `2^(k+10)` elements), one
  leaf; there are no challenges.
* **Verifier.** A query program (DESIGN §3.1): read leaf 0 of the index oracle and leaf 0 of the
  message (every leaf of both), parse the layout and the tables, and decide `rel` on them
  (`relBelow 2^8`, the decidable form). `triv_accepts_iff`: it accepts exactly when the tables
  parsed from the message are a witness of `relK k`.
* **Extractor.** The library's 8-instruction `firstMsgImg` (`Library/Extractor.lean`): it outputs
  round 0 in place, and the contract decodes it before round 0 as exactly the tables the verifier
  checked (`triv_extractMid`).
* **Security.** No challenge rounds, so the counting bound `RbrKS` and the error cap are vacuous
  for every `ε` (a function on an empty type; `fun _ => 0` is written). The knowledge content is
  the knowledge state function and its `next`/`full` laws: "the witness satisfies the statement"
  before the message, "the tables parsed from the message satisfy it" after (`trivKSF`).
  `triv_secure`.
-/
import RecursionFast.Contract
import RecursionFast.Library.Codec
import RecursionFast.Library.Extractor
import RecursionFast.Library.RbrSound
import Mathlib.Data.Fin.VecNotation

namespace RecursionFastCandidate
open RecursionFast RecursionFast.Codec
open scoped NNReal

section Triv
variable (k : ℕ) (hk : 20 ≤ k ∧ k ≤ 28)

/-- The single round: one message oracle of `2^(k+10)` elements in one leaf (sent in the clear
by the compilation, S3-A1). -/
def trivShape : Fin 1 → Round := fun _ => .msg ⟨k + 10, k + 10⟩

/-- The verification key: `1` iff the layout is admissible at class `k`. -/
def trivVK (L : Layout K) : Fin 1 → K := fun _ => if L.Admissible k then 1 else 0

/-- The decision on the queried leaves: the key says admissible, and the tables parsed from the
message satisfy the layout parsed from the index. -/
def trivDecide (vk : Fin 1 → K) (x : Stmt) (idx msg : List K) : Bool :=
  vk 0 == 1 && decide ((pLayout idx).1.relBelow (2 ^ 8) k x
    (pWit ((pLayout idx).1.chips.map Chip.cols) msg).1)

/-- The verifier: query leaf 0 of the index oracle (oracle 0) and of the message (oracle 1),
then decide. -/
def trivVerify (vk : Fin 1 → K) (x : Stmt) (_ : Challenges (trivShape k)) : QProg Bool :=
  .query 0 0 fun idx => .query 1 0 fun msg => .done (trivDecide k vk x idx msg)

/-- The tables parsed from the message, given the layout's column counts. -/
def trivWit (L : Layout K) (msg : OVal ⟨k + 10, k + 10⟩) : List (Table K) :=
  (pWit (L.chips.map Chip.cols) (List.ofFn msg)).1

/-- The extractor image with its declared split of `B(k)` over the two calls of a one-round
protocol: 8 steps on the call before round 0 (the image halts after its 8 instructions,
`run_firstMsgImage`) and none on the output call (`extractOut`), whose result `trivKSF` never
reads. The total, 8, is far below `B(k) = 2^(2k+16)`. -/
def trivExtractor : ExtractorImage k 1 where
  img := firstMsgImg
  img_le := by decide
  fuel := ![8, 0]
  fuel_le := by
    show 8 + (0 + 0) ≤ 2 ^ (2 * k + 16)
    exact Nat.pow_le_pow_right two_pos (Nat.le_add_left 3 (2 * k + 13))

/-- The declared 8 steps are what the image needs, on a small extractor tape (sections `[j]`,
`L`, `x`, round 0 `= [3, 4]`, `w`): with 8 steps it halts with round 0 (`run_firstMsgImage` shows
this for every tape whose round 0 is addressable), with 7 it runs out of fuel. -/
theorem trivExtractor_fuel_tight :
    run firstMsgImg (frame [[0], [1], [2], [3, 4], []]) 8 = some [3, 4] ∧
      run firstMsgImg (frame [[0], [1], [2], [3, 4], []]) 7 = none :=
  by decide +kernel

/-- **The baseline protocol** `P_triv` at class `k`. -/
abbrev P_triv : Protocol k where
  k_range := hk
  n := 1
  n_le := by decide
  shape := trivShape k
  vkLen := 1
  vkLen_le := by decide
  VK := trivVK k
  idxShape := ⟨k + 8, k + 8⟩
  IDX L := toOracle (k + 8) (eLayout L)
  shape_ok := ⟨fun _ => ⟨le_refl _, le_refl _⟩, le_refl _, le_refl _⟩
  prover := { next := fun s w _ _ => toOracle (k + 10) (eWit s.1 w),
              output := fun _ _ _ => ((), ()) }
  verify := trivVerify k
  extractor := trivExtractor k
  ε := fun _ => 0

include hk in
/-- **What the verifier decides**: the layout is admissible and the tables parsed from the
message satisfy it. -/
theorem trivDecide_iff (L : Layout K) (x : Stmt) (msg : OVal ⟨k + 10, k + 10⟩) :
    trivDecide k (trivVK k L) x (List.ofFn (toOracle (k + 8) (eLayout L))) (List.ofFn msg) =
      true ↔ L.Admissible k ∧ L.rel k x (trivWit k L msg) := by
  by_cases hL : L.Admissible k
  · have hN : ∀ C ∈ (L.normal (2 ^ 8)).chips, ∀ p ∈ C.ports, p.bus < 2 ^ 8 :=
      List.forall_mem_map.mpr hL.bus_lt
    rw [ofFn_toOracle (eLayout_length hk.1 hL)]
    simp only [trivDecide, trivVK, hL, ite_true, beq_self_eq_true, Bool.true_and,
      decide_eq_true_eq, true_and, pLayout_eLayout hk.2 hL, relBelow_iff hN,
      rel_normal_iff hL.bus_lt, trivWit]
    simp [Layout.normal, Function.comp_def]
  · simp [trivDecide, trivVK, hL]

/-- **The verifier accepts exactly the transcripts whose message parses to a witness.** -/
theorem triv_accepts_iff (s : Layout K × Stmt) (tr : FullTranscript (trivShape k)) :
    (P_triv k hk).specVerifier s tr = some () ↔ (s, trivWit k s.1 (tr 0)) ∈ relK k := by
  obtain ⟨L, x⟩ := s
  refine Iff.trans ?_ (trivDecide_iff k hk L x (tr 0))
  simp [Protocol.specVerifier, trivVerify, QProg.eval, FullTranscript.oracles, trivShape,
    Round.oracles, OShape.leaves, leaf_zero, leaf_zero (k + 10) (tr 0)]

/-- No challenge rounds. -/
theorem triv_noChal (c : ChallengeIdx (trivShape k)) : False := nomatch c.2

include hk in
/-- **The extractor before round 0**: for an admissible layout of a class in range, it returns
exactly the tables the verifier checks (`trivWit`), for every message and every witness after
round 0, within its declared 8 steps. -/
theorem triv_extractMid {L : Layout K} (hL : L.Admissible k) (x : Stmt)
    (tr : Transcript (trivShape k) (Fin.castSucc 0)) (msg : OVal ⟨k + 10, k + 10⟩)
    (w : Mid 1 (Fin.succ 0)) :
    (((trivExtractor k).toExtractor (trivShape k)).extractMid 0 (L, x) (tr.concat msg) w :
      List (Table K)) = trivWit k L msg := by
  have hL' := Layout.words_length hk.1 hL
  have h36 : 2 ^ (k + 8) ≤ 2 ^ 36 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h38 : 2 ^ (k + 10) ≤ 2 ^ 38 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h12 : 2 ^ (k + 10) ≤ 2 ^ (k + 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [firstMsg_extractMid k (trivShape k) 0 (L, x) (tr.concat msg) w
    (by simp [Round.words, trivShape]; omega) (by simp [Round.words, trivShape, witCap]; omega)
    (trivExtractor k) rfl le_rfl]
  have e : (tr.concat msg) (Fin.last 0) = msg := Transcript.concat_last tr msg
  show decTables (L.chips.map Chip.cols)
    (List.ofFn fun i => ((tr.concat msg) (Fin.last 0) i).bits) = _
  rw [e, show (List.ofFn fun i => (msg i).bits) = (List.ofFn msg).map K.bits from
    List.map_ofFn.symm, decTables_map_bits]
  rfl

/-- The knowledge state function: before the message, "`w` satisfies the statement"; after it,
"the tables parsed from the message satisfy the statement". Written with `Fin.cases` because the
witness before round 0 has type `Mid 1 0 = List (Table K)` and words after it. -/
def trivKSF : KSF (relK k) Set.univ (P_triv k hk).specVerifier
    ((P_triv k hk).extractor.toExtractor (P_triv k hk).shape) where
  toFun := fun m => Fin.cases
    (motive := fun m => Layout K × Stmt → Transcript (trivShape k) m → Mid 1 m → Prop)
    (fun s _ w => (s, w) ∈ relK k)
    (fun _ s tr _ => (s, trivWit k s.1 (tr ⟨0, Nat.succ_pos _⟩)) ∈ relK k) m
  empty := fun _ _ => Iff.rfl
  next := by
    rintro ⟨m, _⟩ ⟨L, x⟩ tr msg w h
    obtain rfl : m = 0 := Subsingleton.elim _ _
    have h' : ((L, x), trivWit k L msg) ∈ relK k := Transcript.concat_last tr msg ▸ h
    exact (triv_extractMid k hk h'.1 x tr msg w).symm ▸ h'
  full := fun s tr _ _ hV _ => (triv_accepts_iff k hk s tr).mp hV

/-- **`P_triv` is secure** (DESIGN §4): perfect completeness for `relK k`, a knowledge state
function for the image's extractor (`trivKSF`), and the counting bound and error cap, which are
vacuous without challenge rounds; at every class in range. -/
theorem triv_secure : (P_triv k hk).Secure where
  complete := by
    rintro ⟨L, x⟩ w ⟨hL, hrel⟩ ρ
    refine ⟨(triv_accepts_iff k hk _ _).mpr ⟨hL, ?_⟩, Set.mem_univ _⟩
    show L.rel k x (trivWit k L (toOracle (k + 10) (eWit L w)))
    have h28 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [trivWit, ofFn_toOracle (eWit_length hL hrel), pWit_eWit L w hrel.1
      (fun T hT => lt_of_le_of_lt (rows_le_of_rel hL hrel T hT) h28)]
    exact (rel_trim_iff hL.readsOwn hrel.1).mpr hrel
  sound := ⟨trivKSF k hk, fun _ c _ => (triv_noChal k c).elim⟩
  cap := fun c => (triv_noChal k c).elim

end Triv

end RecursionFastCandidate

/-
# Baseline submission: what the compilation makes of `P_triv`                      (UNTRUSTED)

Why the baseline is **listed, unranked** (DESIGN §7.3, O-10, S1-A12(b)), as theorems about the
organiser's compilation (`Contract/Compile.lean`), at every class in range and every
configuration (hash, arity):

* `triv_depth`: every oracle of `P_triv` has one leaf, so its Merkle tree has depth 0 at every
  arity: no authentication path, and the index root is one leaf hash. The arity changes neither
  the tape nor the verifier's work, which is why `cfg` takes the design's default arity 2.
* `triv_uncapped_length`: the honest tape (the rounds section and the openings that `prove`
  writes, before its cap check) has exactly `5 · 2^(k+11)` bytes on every instance: the message
  in the clear, `8 · 2^(k+10)` bytes, and the opening of the index oracle's one leaf,
  `8 · 2^(k+8)` bytes. At the benchmark's class `k = 24` that is `5 · 2^35` bytes (160 GiB),
  against `tapeCap = 2^20` (1 MiB, boards R and W) and the 128 KiB cap of board L.
* `triv_prove_none`: so the honest compiled prover writes no tape, on any instance.
* `triv_narg`: and the compiled verifier accepts no tape at all, since the rounds section alone
  is longer than the cap. The badge path (`lake exe verify`, indexing, the benchmark run) can
  therefore never accept a proof of this entry.
* `triv_no_entry`: so `aggOK` accepts no node and there is no recursion entry (board R) for
  `P_triv`: its field `live` fails (S5-A10).
-/
import RecursionFastCandidate.Protocol
import RecursionFast.Library.Compile

namespace RecursionFastCandidate
open RecursionFast RecursionFast.Codec

/-- Every one-leaf oracle has a Merkle tree of depth 0, at every arity. -/
theorem triv_depth (cfg : Cfg) (m : ℕ) : cfg.depth ⟨m, m⟩ = 0 := by
  simp only [Cfg.depth, Nat.sub_self, Nat.zero_add, Nat.div_eq_zero_iff]
  omega

/-- The tape the honest compiled prover writes before its cap check: `prove` without the cap. -/
def uncapped (cfg : Cfg) {k : ℕ} (P : Protocol k) (L : Layout K) (x : Stmt)
    (w : List (Table K)) : Option Tape :=
  let tr := fsTranscript cfg P L x w
  (record cfg (⟨P.idxShape, P.IDX L⟩ :: tr.oracles) (P.verify (P.VK L) x (chalOf tr))).map
    fun op => (List.ofFn fun i => (P.shape i).tapeBytes cfg (tr i)).flatten ++ op

/-- `prove` is the uncapped tape, kept only within the cap. -/
theorem prove_eq_uncapped (cfg : Cfg) {k : ℕ} (P : Protocol k) (L : Layout K) (x : Stmt)
    (w : List (Table K)) :
    prove cfg P L x w =
      (uncapped cfg P L x w).bind fun t => if t.length ≤ tapeCap then some t else none := by
  simp only [prove, uncapped]
  split <;> simp_all

section
variable (k : ℕ) (hk : 20 ≤ k ∧ k ≤ 28)

/-- **The honest tape of `P_triv` has `5 · 2^(k+11)` bytes**, on every instance and for every
configuration: the plain message (`8 · 2^(k+10)` bytes in the rounds section) and the opening of
leaf 0 of the index oracle (`8 · 2^(k+8)` bytes, with a path of depth 0); the query of the plain
message opens nothing. -/
theorem triv_uncapped_length (cfg : Cfg) (L : Layout K) (x : Stmt) (w : List (Table K)) :
    (uncapped cfg (P_triv k hk) L x w).map List.length = some (5 * 2 ^ (k + 11)) := by
  simp [uncapped, trivVerify, record, FullTranscript.oracles, trivShape, Round.oracles,
    OShape.leaves, Round.tapeBytes, OShape.plain, pathOf, triv_depth, K.bytes_length,
    Oracle.leaf_length]
  erw [List.length_ofFn]
  ring

include hk in
/-- `5 · 2^(k+11)` is beyond the tape cap at every class in range. -/
theorem triv_tape_gt_cap : tapeCap < 5 * 2 ^ (k + 11) := by
  have : 2 ^ 20 ≤ 2 ^ (k + 11) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold tapeCap; omega

/-- **The honest compiled prover of `P_triv` writes no tape**, on any instance. -/
theorem triv_prove_none (cfg : Cfg) (L : Layout K) (x : Stmt) (w : List (Table K)) :
    prove cfg (P_triv k hk) L x w = none := by
  obtain ⟨t, hu, ht⟩ := Option.map_eq_some_iff.mp (triv_uncapped_length k hk cfg L x w)
  rw [prove_eq_uncapped, hu, Option.bind_some, ht, ite_eq_right (triv_tape_gt_cap k hk).not_ge]

/-- Reading `n` bytes from a shorter tape fails (as in `Controls/Certificate.lean`). -/
theorem takeN_short : ∀ (n : ℕ) (t acc : List UInt8), t.length < n → takeN n t acc = none
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, _ => rfl
  | n + 1, _ :: t, _, h => takeN_short n t _ (Nat.lt_of_succ_lt_succ h)

/-- **The compiled verifier of `P_triv` accepts no tape**, for every configuration, key and
statement: a tape within the cap is shorter than the plain message it must start with. -/
theorem triv_narg (cfg : Cfg) (vkc : VKc 1) (x : Stmt) (t : Tape) :
    NARG cfg (P_triv k hk) vkc x t = false := by
  by_cases ht : t.length ≤ tapeCap
  · have hm : msgLen ⟨k + 10, k + 10⟩ = 8 * 2 ^ (k + 10) := by simp [msgLen, OShape.plain]
    have hlt : t.length < msgLen ⟨k + 10, k + 10⟩ := by
      have : 2 ^ 20 ≤ 2 ^ (k + 10) := Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold tapeCap at ht; omega
    simp [NARG, trivShape, pass, takeN_short _ t [] hlt]
  · simp [NARG, ht]

/-- **Hence `P_triv` has no recursion entry** (board R), at any class and configuration:
`aggOK` accepts no node, so the field `live` (S5-A10) cannot hold (as `toy_no_entry` for the
organiser's toy). -/
theorem triv_no_entry (cfg : Cfg) (e : RecursionEntry (P_triv k hk) cfg) : False := by
  obtain ⟨_, x', nw, _, _, h⟩ := e.live
  cases ht : nw.t₂ <;> simp [aggOK, child, ht, triv_narg] at h

end

end RecursionFastCandidate

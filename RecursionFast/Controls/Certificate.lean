/-
# Controls: submissions and certificates (`Contract/Certificate.lean`)

* `toy_certificate` (positive): the toy protocol (`Controls/Toy.lean`, secure at every class in
  range) at class 20 with BLAKE2s at arity 2 is a leaf-board submission with a certificate for the
  declared claim `⟨20, blake2s, 2⟩`; `toy_certificate_arity` (negative): none for arity 4.
* `toy_no_entry` (negative, S5-A2 → S5-A7): the toy's one message is sent in the clear,
  `8·2^30` bytes, beyond the tape cap, so `NARG` accepts no tape (`toy_narg`) and `aggOK` no node
  (`toy_aggOK`). Before S5-A7 this made a vacuous recursion entry: with the unsatisfiable layout
  `unsat`, `fits`, `sound` and `complete` all hold (`toy_vacuous_fields`), and the toy is secure.
  The field `live` now excludes it: the toy has no recursion entry at all, whatever the layout and
  decoder. `live` must also name the indexer's keys (S5-A10, `Controls/MagicKey.lean`). The
  positive side of `live` is `cmpToy_live` in `Controls/Recursion.lean` and the library's
  `live_of_secure`; there is no positive entry (§7.3).
-/
import RecursionFast.Contract.Certificate
import RecursionFast.Controls.Toy
import RecursionFast.Controls.Negative
import RecursionFast.Controls.CompileToy

namespace RecursionFast.Controls.Certificate
open RecursionFast RecursionFast.Controls RecursionFast.Controls.Compile

/-- Class 20 is in range. -/
theorem h20 : 20 ≤ 20 ∧ 20 ≤ 28 := ⟨le_rfl, by decide⟩

/-- The toy protocol at class 20, compiled with BLAKE2s at arity 2. -/
def toySub : Submission 20 := ⟨toy 20 h20, cfg2, toy_secure 20 h20⟩

/-- **Positive**: the toy submission has a certificate for its declared claim. -/
theorem toy_certificate : Certificate ⟨20, .blake2s, 2⟩ toySub := ⟨⟨rfl, rfl⟩⟩

/-- No certificate for a claim with another arity. -/
theorem toy_certificate_arity : ¬ Certificate ⟨20, .blake2s, 4⟩ toySub :=
  fun h => absurd h.cfg.2 (by decide)

/-! ## The toy accepts no node, so it has no recursion entry (S5-A2, S5-A7) -/

/-- Reading `n` bytes from a shorter tape fails. -/
theorem takeN_short : ∀ (n : ℕ) (t acc : List UInt8), t.length < n → takeN n t acc = none
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], _, _ => rfl
  | n + 1, _ :: t, _, h => takeN_short n t _ (Nat.lt_of_succ_lt_succ h)

/-- The compiled toy accepts no tape: its plain message alone exceeds the tape cap. -/
theorem toy_narg (vkc : VKc 1) (x : Stmt) (t : Tape) : NARG cfg2 (toy 20 h20) vkc x t = false := by
  by_cases ht : t.length ≤ tapeCap
  · simp [NARG, toy, toyShape, pass, takeN_short (msgLen ⟨30, 30⟩) t [] (ht.trans_lt (by decide))]
  · simp [NARG, ht]

/-- So the compiled toy's `aggOK` accepts no node. -/
theorem toy_aggOK (x' : Stmt) (nw : NodeWitness 1) : aggOK cfg2 (toy 20 h20) x' nw = false := by
  cases h : nw.t₂ <;> simp [aggOK, child, h, toy_narg]

/-- With the unsatisfiable layout `unsat`, every field of a recursion entry for the toy but
`live` holds, for any decoder: `fits`, and `sound` and `complete` vacuously. -/
theorem toy_vacuous_fields (decode : List (Table K) → NodeWitness 1) :
    unsat.Admissible 20 ∧
    (∀ x' w, unsat.rel 20 x' w → aggOK cfg2 (toy 20 h20) x' (decode w) = true) ∧
    (∀ x' nw, aggOK cfg2 (toy 20 h20) x' nw = true → ∃ w, unsat.rel 20 x' w ∧ decode w = nw) :=
  ⟨unsat_admissible_of 20, fun x' w hw => absurd hw (unsat_neg 20 x' w),
    fun x' nw h => absurd h (Bool.ne_true_of_eq_false (toy_aggOK x' nw))⟩

/-- **Negative (S5-A7, S5-A10)**: but `live` fails, so the toy has no recursion entry. -/
theorem toy_no_entry (e : RecursionEntry (toy 20 h20) cfg2) : False :=
  let ⟨_, x', nw, _, _, h⟩ := e.live; Bool.ne_true_of_eq_false (toy_aggOK x' nw) h

/-- Hence no recursion-board submission is built on the toy at class 20 with `cfg2`. -/
theorem toy_no_submissionR (S : SubmissionR 20) (hP : S.P = toy 20 h20) (hc : S.cfg = cfg2) :
    False := toy_no_entry (hP ▸ hc ▸ S.entry)

end RecursionFast.Controls.Certificate

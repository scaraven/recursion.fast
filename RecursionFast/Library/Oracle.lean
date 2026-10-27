/-
  RecursionFast.Library.Oracle  (UNTRUSTED, kernel-checked)

  Query programs (`Contract/Oracle.lean`) run against a full oracle function.

  * `OProg.run H p`: the result of `p` when the oracle is the function `H`. It was v3's contract
    definition, used there by the instantiated verifier `Vb` only; v4's contract runs a verifier
    on a trace (`runSeq`) and on a log (`runLog`), and `run` serves the library: perfect
    completeness (`Library/Completeness.lean`) and the facts below.
  * `runLog_eq_run`: a log that agrees with the oracle `H` and contains every query a program asks
    under `H` makes `runLog` return the program's result under `H`: the verifier's decision read
    from the query log, as `KS` reads it, is the verifier actually run against the oracle.
  * `runLog_queries`: the log of a program's own run is such a log.
  * `run_bind`, `queries_bind`, `bind_assoc`: a composed program's result and queries under `H`
    (completeness, V3-S2R-A2; the knowledge-soundness game, V4-A10).
  * `Consistent H L`: the oracle function `H` agrees with the table `L` (moved from
    `Library/Completeness.lean`); `exists_consistent`, `consistent_append`,
    `consistent_append_self`: a lazily sampled run, extended by a fresh answer, stays consistent
    with some function. The functional query bounds of `KS` apply to a lazy run through them.
-/
import RecursionFast.Contract.Oracle

namespace RecursionFast.OProg
variable {α : Type}

/-- The result of the program when the oracle is the function `H`. -/
def run (H : ByteArray → Digest) : OProg α → α
  | ret a => a
  | query q k => (k (H q)).run H

/-- **A log consistent with `H` that contains the run's queries answers the run.** -/
theorem runLog_eq_run {H : ByteArray → Digest} {L : Log} (p : OProg α)
    (hc : ∀ e ∈ L, e.2 = H e.1) (hq : ∀ q ∈ p.queries H, q ∈ L.map Prod.fst) :
    p.runLog L = some (p.run H) := by
  induction p with
  | ret a => rfl
  | query q k ih =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hq q (List.mem_cons_self ..))
    cases hf : L.find? (fun x => decide (x.1 = e.1)) with
    | none => simpa using List.find?_eq_none.mp hf e he
    | some e' =>
      have hq' : e'.1 = e.1 := by simpa using List.find?_some hf
      have ha : e'.2 = H e.1 := by rw [hc e' (List.mem_of_find?_eq_some hf), hq']
      simp only [runLog, run, hf, Option.bind_some, ha]
      exact ih (H e.1) fun q' h' => hq q' (List.mem_cons_of_mem _ h')

/-- The log of a program's own run under `H` (its queries with `H`'s answers) answers the run. -/
theorem runLog_queries (H : ByteArray → Digest) (p : OProg α) :
    p.runLog ((p.queries H).map fun q => (q, H q)) = some (p.run H) :=
  runLog_eq_run p (by simp) (by simp)

/-- Running `p.bind f` under `H` runs `p`, then `f` on its result. -/
theorem run_bind {β : Type} (H : ByteArray → Digest) (p : OProg α) (f : α → OProg β) :
    (p.bind f).run H = (f (p.run H)).run H := by
  induction p with
  | ret a => rfl
  | query q k ih => exact ih (H q)

/-- Binding is associative. -/
theorem bind_assoc {β γ : Type} (p : OProg α) (f : α → OProg β) (g : β → OProg γ) :
    (p.bind f).bind g = p.bind fun x => (f x).bind g := by
  induction p with
  | ret a => rfl
  | query q k ih => exact congrArg (query q) (funext ih)

/-- Under `H`, `p.bind f` asks `p`'s queries, then those of `f` on `p`'s result. -/
theorem queries_bind {β : Type} (H : ByteArray → Digest) (p : OProg α) (f : α → OProg β) :
    (p.bind f).queries H = p.queries H ++ (f (p.run H)).queries H := by
  induction p with
  | ret a => rfl
  | query q k ih => exact congrArg (q :: ·) (ih (H q))

end RecursionFast.OProg

namespace RecursionFast

/-- The oracle function `H` agrees with the table `L` (read by first match). -/
def Consistent (H : ByteArray → Digest) (L : Log) : Prop :=
  ∀ q e, L.find? (fun e => e.1 = q) = some e → H q = e.2

theorem exists_consistent (L : Log) : ∃ H, Consistent H L :=
  ⟨fun q => ((L.find? fun e => e.1 = q).map Prod.snd).getD (Vector.replicate 32 0),
    fun _ _ h => by simp [h]⟩

theorem consistent_append {H : ByteArray → Digest} {L : Log} {q : ByteArray} {a : Digest}
    (hf : L.find? (fun e => e.1 = q) = none) (h : Consistent H (L ++ [(q, a)])) :
    Consistent H L ∧ H q = a :=
  ⟨fun q' e he => h q' e (by simp [List.find?_append, he]),
    h q (q, a) (by simp [List.find?_append, hf])⟩

/-- A function consistent with `L` is consistent with `L` followed by its own answer to `q`. -/
theorem consistent_append_self {H : ByteArray → Digest} {L : Log} {q : ByteArray}
    (h : Consistent H L) :
    Consistent H (L ++ [(q, H q)]) := by
  intro q' e he
  rw [List.find?_append] at he
  cases hL : L.find? (fun e => decide (e.1 = q')) with
  | some e' => rw [hL] at he; exact (Option.some.inj he) ▸ h q' e' hL
  | none =>
    rw [hL, Option.none_or] at he
    by_cases hq : q = q'
    · subst hq; simp at he; rw [← he]
    · simp [hq] at he

end RecursionFast

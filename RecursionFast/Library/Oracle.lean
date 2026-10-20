/-
  RecursionFast.Library.Oracle  (UNTRUSTED, kernel-checked)

  Facts about query programs (`Contract/Oracle.lean`).

  * `runLog_eq_run`: a log that agrees with the oracle `H` and contains every query a program asks
    under `H` makes `runLog` return the program's result under `H`. This is the step of the paper
    theorem (DESIGN-v3 §4.5) from the knowledge state's `final` law, which reads the verifier's
    decision from the log, to the verifier actually run against the random oracle.
  * `runLog_queries`: the log of a program's own run is such a log.
  * `run_bind`: a composed program's result under `H` (completeness, V3-S2R-A2).
-/
import RecursionFast.Contract.Oracle

namespace RecursionFast.OProg
variable {α : Type}

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

end RecursionFast.OProg

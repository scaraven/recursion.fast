/- S1 review probe (S1-M1), turned positive in the S1 fix pass.

Originally `Protocol.verify` received every oracle as a total function, and `readsAll` (a legal
value of that field) depended on every position of a message, so a BCS compiler had nothing to
open. After the fix (S1-A8) the verifier is a query program (`QProg`), and what a run reads is
observable: `QProg.reads p os` lists the `(oracle, leaf)` pairs the run on `os` queries, and
`eval_local` shows the result depends only on those leaves (and on the leaf counts of the
queried oracles). This is exactly what the compiled argument opens. -/
import RecursionFast.Contract.Protocol

open RecursionFast

namespace S1Probe

/-- The `(oracle, leaf)` pairs a run reads, in order. -/
def _root_.RecursionFast.QProg.reads {α : Type} : QProg α → List Oracle → List (ℕ × ℕ)
  | .done _, _ => []
  | .query j l cont, os => (j, l) :: match os[j]? with
    | some o => if l < o.shape.leaves then (cont (o.leaf l)).reads os else []
    | none => []

/-- What an oracle list shows at `(j, l)`: the oracle's leaf count and its leaf `l`. -/
def seen (os : List Oracle) (jl : ℕ × ℕ) : Option (ℕ × List K) :=
  os[jl.1]?.map fun o => (o.shape.leaves, o.leaf jl.2)

/-- **Locality**: two oracle lists that show the same at every `(oracle, leaf)` the run on `os`
reads give the same result. -/
theorem eval_local {α : Type} (p : QProg α) (os os' : List Oracle)
    (h : ∀ jl ∈ p.reads os, seen os jl = seen os' jl) : p.eval os = p.eval os' := by
  induction p with
  | done a => rfl
  | query j l cont ih =>
    have hj := h (j, l) (by simp [QProg.reads])
    simp only [seen] at hj
    cases hos : os[j]? with
    | none =>
      rw [hos] at hj
      cases hos' : os'[j]? with
      | none => simp [QProg.eval, hos, hos']
      | some o' => simp [hos'] at hj
    | some o =>
      rw [hos] at hj
      cases hos' : os'[j]? with
      | none => simp [hos'] at hj
      | some o' =>
        simp only [hos', Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨hlv, hlf⟩ := hj
        simp only [QProg.eval, hos, hos', ← hlv, ← hlf]
        split_ifs with hl
        · refine ih _ fun jl hjl => h jl ?_
          rw [QProg.reads, hos]
          exact List.mem_cons_of_mem _ (by simp only [hl, ↓reduceIte]; exact hjl)
        · rfl

end S1Probe

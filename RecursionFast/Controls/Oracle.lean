/-
# Controls: query programs (`Contract/Oracle.lean`), positive and negative

A toy oracle `H₀` (answer: the query's length, repeated; no hashing) and a two-query program
`prog` whose second query depends on the first answer.

`runLog` (v3's controls). Positive: `prog_queries` (under `H₀` the program asks `[01]`, then
`[01 01]`, built from the answer), `prog_run` (its result under `H₀`; `run` is now
`Library/Oracle.lean`'s), `prog_runLog` and `prog_runLog'` (the log of its own run answers it),
`prog_runLog_first` (with two entries for the first query, the first is used). Negative:
`prog_runLog_miss` (a log without the second query gives `none`), `runLog_reads_log` (other
answers, another result: `runLog` reads only the log).

`runSeq` (new, V4-4, V4-A3). Positive: `prog_runSeq` (the trace of the run, in order, gives the
run's result), `prog_runSeq'` (the honest trace of every program, `Library/Trace.lean`'s
`runSeq_queries`), `prog_runLog_of_runSeq` (the bridge to the log, on a log with extra entries).
Negative: `prog_runSeq_swapped` (the right entries in the wrong order), `prog_runSeq_short` (the
trace runs out), `prog_runSeq_extra` (**a left-over entry is rejected**: exact consumption,
V4-A3), `prog_runSeq_wrong_query` (an entry for another query), `runSeq_reads_trace` (other
answers in the trace, another result), `ret_runSeq_nonempty` (a program that asks nothing
accepts only the empty trace, for every trace entry).
-/
import RecursionFast.Library.Trace

namespace RecursionFast.Controls.Oracle
open RecursionFast

/-- A toy oracle: the query's length (mod 256), repeated 32 times. -/
def H₀ (q : ByteArray) : Digest := Vector.replicate 32 q.size.toUInt8

/-- The first query `[01]`. -/
def q₁ : ByteArray := ⟨#[1]⟩

/-- Two queries: `[01]`, then the first two bytes of its answer; return both answers. -/
def prog : OProg (Digest × Digest) :=
  .query q₁ fun a => .query ⟨#[a[0], a[1]]⟩ fun b => .ret (a, b)

/-! ## `runLog` and `run` -/

theorem prog_queries : prog.queries H₀ = [⟨#[1]⟩, ⟨#[1, 1]⟩] := by decide

theorem prog_run : prog.run H₀ = (Vector.replicate 32 1, Vector.replicate 32 2) := by decide

theorem prog_runLog :
    prog.runLog [(⟨#[1]⟩, Vector.replicate 32 1), (⟨#[1, 1]⟩, Vector.replicate 32 2)] =
      some (prog.run H₀) := by decide

theorem prog_runLog' : prog.runLog ((prog.queries H₀).map fun q => (q, H₀ q)) =
    some (prog.run H₀) := OProg.runLog_queries H₀ prog

/-- With two entries for `[01]`, the first one's answer is used. -/
theorem prog_runLog_first :
    prog.runLog [(⟨#[1]⟩, Vector.replicate 32 7), (⟨#[1]⟩, Vector.replicate 32 1),
      (⟨#[7, 7]⟩, Vector.replicate 32 9)] =
      some (Vector.replicate 32 7, Vector.replicate 32 9) := by decide

/-- A log without the second query: `none`. -/
theorem prog_runLog_miss : prog.runLog [(⟨#[1]⟩, Vector.replicate 32 1)] = none := by decide

/-- `runLog` reads the log, not the oracle: other answers, another result. -/
theorem runLog_reads_log :
    prog.runLog [(⟨#[1]⟩, Vector.replicate 32 7), (⟨#[7, 7]⟩, Vector.replicate 32 9)] ≠
      some (prog.run H₀) := by decide

/-! ## `runSeq` -/

/-- The run's trace under `H₀`. -/
def tr₀ : Trace := [(⟨#[1]⟩, Vector.replicate 32 1), (⟨#[1, 1]⟩, Vector.replicate 32 2)]

/-- **The trace of the run, in order, gives the run's result.** -/
theorem prog_runSeq : prog.runSeq tr₀ = some (prog.run H₀) := by decide

/-- The honest trace of every program gives its result (`Library/Trace.lean`). -/
theorem prog_runSeq' : prog.runSeq ((prog.queries H₀).map fun q => (q, H₀ q)) =
    some (prog.run H₀) := OProg.runSeq_queries H₀ prog

/-- The two entries in the wrong order: rejected. -/
theorem prog_runSeq_swapped : prog.runSeq tr₀.reverse = none := by decide

/-- The trace runs out: rejected. -/
theorem prog_runSeq_short : prog.runSeq (tr₀.take 1) = none := by decide

/-- **A left-over entry is rejected** (exact consumption, V4-A3). -/
theorem prog_runSeq_extra : prog.runSeq (tr₀ ++ [(⟨#[5]⟩, Vector.replicate 32 5)]) = none := by
  decide

/-- An entry for another query: rejected. -/
theorem prog_runSeq_wrong_query :
    prog.runSeq [(⟨#[2]⟩, Vector.replicate 32 1), (⟨#[1, 1]⟩, Vector.replicate 32 2)] = none := by
  decide

/-- `runSeq` reads the trace's answers: other answers, another result. -/
theorem runSeq_reads_trace :
    prog.runSeq [(⟨#[1]⟩, Vector.replicate 32 7), (⟨#[7, 7]⟩, Vector.replicate 32 9)] =
      some (Vector.replicate 32 7, Vector.replicate 32 9) := by decide

/-- A program that asks nothing accepts only the empty trace. -/
theorem ret_runSeq_nonempty {α : Type} (a : α) (e : ByteArray × Digest) (tr : Trace) :
    (OProg.ret a).runSeq (e :: tr) = none := OProg.runSeq_ret_cons a e tr

/-- **The bridge** on a functional log with an extra entry: the trace's verdict is the log's. -/
theorem prog_runLog_of_runSeq :
    prog.runLog (tr₀ ++ [(⟨#[5]⟩, Vector.replicate 32 5)]) = some (prog.run H₀) :=
  OProg.runLog_of_runSeq (by unfold Log.Functional; decide) prog tr₀ prog_runSeq
    fun _ he => List.mem_append_left _ he

end RecursionFast.Controls.Oracle

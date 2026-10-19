/-
# Controls: query programs (`Contract/Oracle.lean`), positive and negative

A toy oracle `H₀` (answer: the query's length, repeated; no hashing) and a two-query program
`prog` whose second query depends on the first answer.

Positive:
* `prog_queries`: under `H₀` the program asks `[01]`, then `[01 01]` (built from the answer).
* `prog_run`: its result under `H₀`.
* `prog_runLog`: the log of its own run answers it with the same result (also an instance of
  `Library/Oracle.lean`'s `runLog_queries`, `prog_runLog'`).
* `prog_runLog_first`: with two entries for the first query, the first entry's answer is used.

Negative:
* `prog_runLog_miss`: a log without the second query gives `none`.
* `runLog_reads_log`: a log with other answers gives another result than the run under `H₀`:
  `runLog` reads only the log.
-/
import RecursionFast.Library.Oracle

namespace RecursionFast.Controls.Oracle
open RecursionFast

/-- A toy oracle: the query's length (mod 256), repeated 32 times. -/
def H₀ (q : ByteArray) : Digest := Vector.replicate 32 q.size.toUInt8

/-- The first query `[01]`. -/
def q₁ : ByteArray := ⟨#[1]⟩

/-- Two queries: `[01]`, then the first two bytes of its answer; return both answers. -/
def prog : OProg (Digest × Digest) :=
  .query q₁ fun a => .query ⟨#[a[0], a[1]]⟩ fun b => .ret (a, b)

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

end RecursionFast.Controls.Oracle

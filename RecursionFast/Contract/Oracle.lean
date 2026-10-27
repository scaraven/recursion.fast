/-
# Contract: query programs over one random oracle                                  (TRUSTED)

DESIGN-v3 §3.1, V3-2; v4 adds `runSeq` (V4-4). The submitted verifier and prover are **query
programs**: computations that ask one oracle `ByteArray → Digest` and return a value. `OProg` is
inductive, so every program terminates and asks finitely many queries. A program is read in three
ways:
* against a partial table of answers (`runLog`, the first entry for each query): knowledge
  soundness (`Security.lean`, `KS`) reads the verifier's decision from the final query log;
* against a lazily sampled random oracle (`Security.lean`, `prob`): the games of completeness and
  of knowledge soundness;
* against a **trace**, in order (`runSeq`): the `i`-th query is answered by the `i`-th entry,
  which must be for that query. This is how `acc` (`Certificate.lean`) runs a verifier on a signed
  proof, and how a node circuit replays a child's signed trace: in one pass, with no lookup
  (V4-4). The trace must be used up exactly (V4-A3): a signed trace is the verifier's queries and
  nothing else, so its length, and the work of hashing it, is the verifier's own (the module
  header of `Certificate.lean` says why that matters).
`queries` lists the queries a program asks under an oracle function (the bounds `qV` and `Q` of
`KS`), and `bind` runs one program after another against one oracle (completeness runs the prover,
then the verifier, V3-S2R-A2; knowledge soundness the adversary, then the verifier, V4-A10).
v3's `run` (the result under an oracle function) left the contract with `Vb`, its only trusted
user; it is in `Library/Oracle.lean`.
-/
import RecursionFast.Contract.Relation

namespace RecursionFast

/-- A computation that queries one oracle `ByteArray → Digest` and returns an `α`. -/
inductive OProg (α : Type) where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Ask the oracle `q`, continue with its answer. -/
  | query (q : ByteArray) (k : Digest → OProg α)

/-- A query log: oracle answers to some queries, in the order asked. It is the type of a trace
(`Relation.lean`); the two names say how it is read: a log by lookup (`runLog`, the first
entry for a query), a trace in order (`runSeq`). -/
abbrev Log := Trace

namespace OProg
variable {α : Type}

/-- The result of the program when every query is answered from the log `L` (the first entry
for that query); `none` if it asks a query `L` does not answer. -/
def runLog (L : Log) : OProg α → Option α
  | ret a => some a
  | query q k => (L.find? fun e => e.1 = q).bind fun e => (k e.2).runLog L

/-- **The result of the program on the trace `tr`**: its queries answered in order by the
entries of `tr`, each of which must be for the query asked; `none` on a mismatch, if the trace
runs out, or if entries are left over. -/
def runSeq : Trace → OProg α → Option α
  | [], ret a => some a
  | _ :: _, ret _ => none
  | (q', a) :: tr, query q k => if q' = q then runSeq tr (k a) else none
  | [], query _ _ => none

/-- The queries the program asks, in order, when the oracle is `H`. -/
def queries (H : ByteArray → Digest) : OProg α → List ByteArray
  | ret _ => []
  | query q k => q :: (k (H q)).queries H

/-- The program that runs `p` and then `f` on its result, against the same oracle. -/
def bind {β : Type} : OProg α → (α → OProg β) → OProg β
  | ret a, f => f a
  | query q k, f => query q fun d => (k d).bind f

end OProg

end RecursionFast

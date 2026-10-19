/-
# Contract: query programs over one random oracle                                  (TRUSTED)

DESIGN-v3 §3.1, V3-2. The submitted verifier and prover are **query programs**: computations
that ask one oracle `ByteArray → Digest` and return a value. `OProg` is inductive, so every
program terminates and asks finitely many queries. A program is run against a full oracle
function (`run`; the theorem quantifies over every function, the harness instantiates BLAKE2s,
`Certificate.lean`) or against a partial table of answers (`runLog`; the knowledge-soundness
laws of `Security.lean` read a verifier's decision from the query log alone).
-/
import RecursionFast.Contract.Relation

namespace RecursionFast

/-- A computation that queries one oracle `ByteArray → Digest` and returns an `α`. -/
inductive OProg (α : Type) where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Ask the oracle `q`, continue with its answer. -/
  | query (q : ByteArray) (k : Digest → OProg α)

/-- A query log: oracle answers to some queries, in the order asked. -/
abbrev Log := List (ByteArray × Digest)

namespace OProg
variable {α : Type}

/-- The result of the program when the oracle is the function `H`. -/
def run (H : ByteArray → Digest) : OProg α → α
  | ret a => a
  | query q k => (k (H q)).run H

/-- The result of the program when every query is answered from the log `L` (the first entry
for that query); `none` if it asks a query `L` does not answer. -/
def runLog (L : Log) : OProg α → Option α
  | ret a => some a
  | query q k => (L.find? fun e => e.1 = q).bind fun e => (k e.2).runLog L

/-- The queries the program asks, in order, when the oracle is `H`. -/
def queries (H : ByteArray → Digest) : OProg α → List ByteArray
  | ret _ => []
  | query q k => q :: (k (H q)).queries H

end OProg

end RecursionFast

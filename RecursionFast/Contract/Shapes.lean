/-
# Contract: round shapes, transcripts, oracles                                  (TRUSTED)

A protocol is a list of **contract-fixed round shapes** (DESIGN §3.1, A2-C1/C2/C3):
* `msg o`: the prover sends a vector of `2^o.logLen` elements of `K` (an oracle). The verifier
  reads it only through `QProg.query` (`Protocol.lean`), a leaf of `2^o.logLeaf` elements at a
  time. Every vector of that length is a possible message: there is no submitter type and no
  serialiser, so the security statements quantify over every string an adversary can commit to.
* `chal nE idx`: the verifier sends `nE` uniform elements of E and, for each `b` in `idx`, a
  uniform `b`-bit index. No K-valued challenges.

Lengths and leaves are powers of two (DESIGN §3.1), stored by their exponents. A transcript
prefix of length `m` is a dependent function on `Fin m`, as in ArkLib's
`ProtocolSpec.Transcript`. Carried over from v0.3 verbatim minus deletions (S9-A1:
`FullTranscript.tapeWords`, `Inhabited Oracle`) and with these docstrings updated (S9-A3).
-/
import RecursionFast.Contract.Field
import Mathlib.Data.Fin.Tuple.Basic

namespace RecursionFast

/-- Contract round cap (DESIGN §3.1): every protocol has at most `2^14` rounds. -/
def roundCap : ℕ := 2 ^ 14

/-- Shape of an oracle: `2^logLen` elements of K, read in leaves of `2^logLeaf` elements, so a
query opens one of `2^(logLen - logLeaf)` leaves (Merkle depth `logLen - logLeaf`). -/
structure OShape where
  logLen : ℕ
  logLeaf : ℕ
  deriving DecidableEq

/-- Contents of an oracle of shape `o`. -/
abbrev OVal (o : OShape) := Fin (2 ^ o.logLen) → K

/-- A round of the contract's fixed menu. -/
inductive Round where
  /-- The prover sends an oracle of shape `o`. -/
  | msg (o : OShape)
  /-- The verifier sends `nE` elements of E and one `b`-bit index for each `b ∈ idx`. -/
  | chal (nE : ℕ) (idx : List ℕ)
  deriving DecidableEq

/-- What is sent in a round: a raw K-vector, or (E-vector, indices). -/
def Round.Ty : Round → Type
  | .msg o => OVal o
  | .chal nE idx => (Fin nE → E) × ((j : Fin idx.length) → BitVec (idx.get j))

/-- Whether the prover speaks in this round. -/
def Round.isMsg : Round → Bool
  | .msg _ => true
  | .chal _ _ => false

variable {n : ℕ} (sh : Fin n → Round)

/-- Transcript prefix of length `m`: the values of rounds `0, …, m-1`. -/
abbrev Transcript (m : Fin (n + 1)) := (i : Fin m) → (sh (Fin.castLE (Nat.le_of_lt_succ m.isLt) i)).Ty

/-- A full transcript: a value for every round. -/
abbrev FullTranscript := (i : Fin n) → (sh i).Ty

/-- The empty transcript. -/
def Transcript.empty : Transcript sh 0 := fun i => Fin.elim0 i

/-- Append the value of round `m` to a prefix of length `m`. -/
def Transcript.concat {sh : Fin n → Round} {m : Fin n} (tr : Transcript sh m.castSucc) (a : (sh m).Ty) :
    Transcript sh m.succ :=
  Fin.snoc (α := fun i : Fin (m.val + 1) => (sh (Fin.castLE m.isLt i)).Ty) tr a

/-- Indices of prover rounds. -/
abbrev MessageIdx := {m : Fin n // (sh m).isMsg = true}
/-- Indices of verifier (challenge) rounds. -/
abbrev ChallengeIdx := {m : Fin n // (sh m).isMsg = false}
/-- A choice of all challenges. -/
abbrev Challenges := (c : ChallengeIdx sh) → (sh c.1).Ty

/-- An oracle as the verifier's query program sees it: a shape and contents. -/
structure Oracle where
  shape : OShape
  data : OVal shape

/-- Element `p` of an oracle (`0` beyond its length; `QProg.eval` reads only leaves below
`leaves`, so never there). -/
def Oracle.get (o : Oracle) (p : ℕ) : K := if h : p < 2 ^ o.shape.logLen then o.data ⟨p, h⟩ else 0

/-- Number of leaves, `2^(logLen - logLeaf)`. -/
def OShape.leaves (o : OShape) : ℕ := 2 ^ (o.logLen - o.logLeaf)

/-- Leaf `l`: elements `l·2^logLeaf, …, (l+1)·2^logLeaf - 1`. -/
def Oracle.leaf (o : Oracle) (l : ℕ) : List K :=
  List.ofFn fun t : Fin (2 ^ o.shape.logLeaf) => o.get (l * 2 ^ o.shape.logLeaf + t.val)

/-- The oracles a round contributes (one for a `msg` round). -/
def Round.oracles : (r : Round) → r.Ty → List Oracle
  | .msg o, v => [⟨o, v⟩]
  | .chal _ _, _ => []

/-- The words a challenge round contributes to the extractor's tape (`Extractor.lean`): E
elements as 3 limbs each, then each index zero-extended to one word (`b ≤ 64` is a shape cap,
`Round.Admissible`). Prover rounds contribute none. -/
def Round.tapeWords : (r : Round) → r.Ty → List Word
  | .msg _, _ => []
  | .chal nE idx, (es, is) =>
      (List.ofFn fun j : Fin nE => (es j).toWords).flatten ++
        List.ofFn fun j : Fin idx.length => (is j).setWidth 64

/-- The prover messages of a transcript, as oracles `1, 2, …` in round order. -/
def FullTranscript.oracles {sh : Fin n → Round} (tr : FullTranscript sh) : List Oracle :=
  (List.ofFn fun i => (sh i).oracles (tr i)).flatten

end RecursionFast

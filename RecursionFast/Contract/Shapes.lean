/-
# Contract: round shapes, transcripts, oracles                                  (TRUSTED)

A protocol is a list of **contract-fixed round shapes** (DESIGN §3, A2-C1/C2/C3):
* `msg o`: the prover sends a raw vector `Fin 2^o.logLen → K` (an oracle, read by QUERY in
  leaves of `2^o.logLeaf` elements). No submitter types, no serializer: every raw vector is a
  possible message, so `Agrees` (∀ transcripts) covers every string an adversary can commit to.
* `chal nE idx`: the verifier sends `nE` uniform elements of E and, for each `b` in `idx`, a
  uniform `b`-bit index. No K-valued challenges.

Lengths and leaves are powers of two (DESIGN §7: "`leaf_j | ℓ_j` (powers of 2)"), stored by
their exponents. A transcript prefix of length `m` is a dependent function on `Fin m`, as in
ArkLib's `ProtocolSpec.Transcript` (so the bridge is definitional).
-/
import RecursionFast.Contract.Field
import Mathlib.Data.Fin.Tuple.Basic

namespace RecursionFast

/-- Contract round cap (DESIGN §3/§5): every protocol and reduction has at most `2^14` rounds. -/
def roundCap : ℕ := 2 ^ 14

/-- Shape of an oracle: `2^logLen` elements of K, read in leaves of `2^logLeaf` elements, so a
QUERY opens one of `2^(logLen - logLeaf)` leaves (Merkle depth `logLen - logLeaf`). -/
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

/-- An oracle as the machine sees it: a shape and contents. -/
structure Oracle where
  shape : OShape
  data : OVal shape

instance : Inhabited Oracle := ⟨⟨⟨0, 0⟩, fun _ => 0⟩⟩

/-- Element `p` of an oracle (`0` beyond its length; QUERY never reads there). -/
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

/-- The tape words a round contributes: E elements as 3 limbs each, then each index
zero-extended to one word (`b ≤ 64` is an admission rule). Prover rounds contribute none. -/
def Round.tapeWords : (r : Round) → r.Ty → List Word
  | .msg _, _ => []
  | .chal nE idx, (es, is) =>
      (List.ofFn fun j : Fin nE => (es j).toWords).flatten ++
        List.ofFn fun j : Fin idx.length => (is j).setWidth 64

/-- The prover messages of a transcript, as oracles `1, 2, …` in round order. -/
def FullTranscript.oracles {sh : Fin n → Round} (tr : FullTranscript sh) : List Oracle :=
  (List.ofFn fun i => (sh i).oracles (tr i)).flatten

/-- The challenges of a transcript, as tape words in round order. -/
def FullTranscript.tapeWords {sh : Fin n → Round} (tr : FullTranscript sh) : List Word :=
  (List.ofFn fun i => (sh i).tapeWords (tr i)).flatten

end RecursionFast

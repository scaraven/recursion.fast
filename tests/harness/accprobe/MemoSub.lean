/-
  A memoising probe submission for the badge's warm-up (`tests/harness/accprobe/run.py`; review R7
  HIGH-1; not an entry, not certified). Its verifier does about 0.5 to 1 s of work that depends on
  the statement only, memoised across checks in one process by a closed term: a lazy binary trie of
  `Thunk`s over the statement's 256 bits, built once per process (pure, total, no `unsafe`, no
  attribute beyond `noinline`). A process that has checked the same statement before answers in
  under a millisecond. The runner used to warm a judged run with the judged input itself (the final
  output checked as `[item, item]`, a re-timing as `[item, item, item]`), so this verifier passed
  the 128 ms cap; warmed with the organiser's own input, in fresh processes, it is judged slow.
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.Challenge
open RecursionFast

/-- The statement the probe accepts: 32 zero bytes. -/
def target : Digest := Vector.replicate 32 0

/-- About half a second of work seeded by `s`. -/
def heavy (s : UInt64) : UInt64 := Id.run do
  let mut y := s
  for _ in [:536870912] do
    y := y * 6364136223846793005 + 1442695040888963407
  return y

/-- A seed from a bit path. -/
def seedOf (p : List Bool) : UInt64 := p.foldl (fun a b => 2 * a + (if b then 1 else 0)) 7

/-- A lazy binary trie: each leaf's value is `heavy` of its path, each child built on demand. -/
inductive Node where
  | leaf : Thunk UInt64 → Node
  | br : Thunk Node → Thunk Node → Node

/-- The trie of depth `d` below the path `p`. -/
def mkNode : Nat → List Bool → Node
  | 0, p => .leaf (Thunk.mk fun _ => heavy (seedOf p))
  | d + 1, p => .br (Thunk.mk fun _ => mkNode d (false :: p)) (Thunk.mk fun _ => mkNode d (true :: p))

/-- The root: a closed term, so one object for the life of the process. -/
@[noinline] def root : Node := mkNode 256 []

/-- The statement's 256 bits. -/
def bitsOf (c : Digest) : List Bool :=
  (List.range 256).map fun i => (c.toArray.getD (i / 8) 0).toNat >>> (i % 8) % 2 == 1

/-- Walk the trie along the bits. -/
def walk : List Bool → Node → UInt64
  | [], .leaf v => v.get
  | [], .br _ _ => 0
  | _ :: _, .leaf v => v.get
  | b :: bs, .br z o => walk bs (if b then o.get else z.get)

/-- Semantically `c == target && π.size == 7 && heavy (seedOf (path of c)) != 0`. -/
def memoV (c : Digest) (π : Proof) : Bool :=
  c == target && π.size == 7 && walk (bitsOf c) root != 0

/-- The probe submission. -/
def submission : Submission :=
  { WitnessSending.submission with V := fun _ c π => .ret (memoV c π), qV := 0 }

end RecursionFast.Challenge

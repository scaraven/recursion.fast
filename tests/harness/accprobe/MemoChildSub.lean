/-
  A probe submission whose verifier memoises its child's acceptance across the checks of one process
  (`tests/harness/accprobe/run.py`; review LR2 M1; not an entry, not certified). In the stream,
  output `i + 1` is a node proof over `c_i` and the next leaf, and a recursive verifier checks `π_i`
  inside it again. This one stands for that: the proof of a leaf (`leafTarget`, 7 bytes) and the
  proof of a node over it (`nodeTarget`, 8 bytes) both cost about 0.5 to 1 s of work on the leaf's
  statement, the "child check", memoised in one process by a closed term (the lazy trie of `Thunk`s
  of `MemoSub.lean`; pure, total, no `unsafe`, no attribute beyond `noinline`). A process that has
  checked the leaf answers the node in under a millisecond. The runner used to judge a batch of
  intermediate outputs in one process (outputs `i` and `i + 1` side by side), so the node's check
  answered from the memo; judged on its own, in three fresh processes, each output pays its child.
-/
import RecursionFast.Library.WitnessSending

namespace RecursionFast.Challenge
open RecursionFast

/-- The leaf's statement: 32 zero bytes. -/
def leafTarget : Digest := Vector.replicate 32 0

/-- The node's statement: 32 bytes `0x01`. -/
def nodeTarget : Digest := Vector.replicate 32 1

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

/-- Semantically `(c == leafTarget && π.size == 7 || c == nodeTarget && π.size == 8) && heavy …`:
the leaf and the node over it both check the leaf (the child check, on the leaf's statement,
memoised in the trie for the life of the process). -/
def memoChildV (c : Digest) (π : Proof) : Bool :=
  (c == leafTarget && π.size == 7 || c == nodeTarget && π.size == 8) && walk (bitsOf leafTarget) root != 0

/-- The probe submission. -/
def submission : Submission :=
  { WitnessSending.submission with V := fun _ c π => .ret (memoChildV c π), qV := 0 }

end RecursionFast.Challenge

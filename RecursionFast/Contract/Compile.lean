/-
# Contract: the compiled argument (BCS + Fiat–Shamir)           (TRUSTED by review, DESIGN §3.2)

The organiser's compilation of a holographic IOP `P : Protocol k` into a non-interactive argument:
every prover oracle is Merkle-committed (BCS) or sent in the clear, every challenge is squeezed
from a hash-chain sponge (Fiat–Shamir), and every `query` of the verifier's query program becomes a
leaf plus an authentication path on the proof tape. `NARG cfg P vkc x t` is the executed verifier
(total, deterministic). The honest compiled prover `prove` and the completeness theorem
`narg_complete` are in `Library/Compile.lean` (no trusted statement uses the prover).

**Bytes.** An element of `K` is 8 bytes, little-endian (`K.toBytes`, Rust `u64::to_le_bytes`); a
vector, a leaf or the statement `x` (32 elements, 256 bytes) is its elements in order; a digest is
the 32 bytes the hash outputs. `H = cfg.hash.run`; every menu hash has 32-byte digests. There are
no length fields: every length is fixed by the shape.

**Key.** The compiled key is `VKc = (VK L, root)`, `root` the Merkle root of the index oracle
`IDX L` (oracle 0), committed by the indexer (`index`) with the same `cfg` (hash and arity) as the
prover's oracles. Its bytes (`VKc.toBytes`) are the `vkLen` elements of `VK L`, then the 32-byte
root. The key digest is `D = H(key bytes)` (`VKc.digest`, DESIGN §5.1). `NARG` rejects a key whose
root is not 32 bytes.

**Merkle tree** of an oracle `o` (shape `logLen`, `logLeaf`) at arity `A = cfg.arity`. Its leaves
are the `2^(logLen - logLeaf)` leaves `Oracle.leaf`, of `2^logLeaf` elements each. The tree has
`depth = ⌈(logLen - logLeaf) / log₂ A⌉` levels (the least `d` with `2^(logLen - logLeaf) ≤ A^d`)
and `A^depth` positions at height 0: position `p` is `H(bytes of leaf p)` if `p` is a leaf, else
the zero digest (32 zero bytes). Node `p` at height `h + 1` is `H(n_{A·p} ‖ … ‖ n_{A·p + A - 1})`,
the `A` nodes `A·p, …, A·p + A - 1` at height `h`; this holds for every internal node, including
one whose children are all padding (at height 1 it is `H(0^(32·A))`, not the zero digest). The
root is node 0 at height `depth`. `commit` computes this root without hashing a subtree whose
positions are all padding, or all leaves whose elements are all zero: such a subtree's digest is
the same at every place, the tower `H(A copies of the one below)` above the zero digest or above
`H(the all-zero leaf)` (S9F-M4; `commit_eq_commitDense` in `Library/Compile.lean` proves the root
equal to the dense recursion). There is no leaf/node tag (S3-A2): binding at a fixed depth
reduces to collision resistance, as the depth and the input length at every level are fixed by
the shape (`opening_binding`, `Library/Compile.lean`: two accepted openings of one position under
one root carry the same leaf, or the hash has a collision). Absorb and squeeze inputs have length
`1 mod 8` and tree inputs `0 mod 8`; the key digest `D` is in the tree's length domain, which is
harmless because the indexer fixes its input.

**Sponge** (a hash chain; S3-A3). The state is a digest. `s₀ = D`, then `x` is absorbed. Absorbing
`m`: `s ← H(0x00 ‖ s ‖ m)`. Squeezing `b` bytes: `⌈b/32⌉` times `s ← H(0x01 ‖ s)`; the output is
the successive states, truncated to `b` bytes.

**Rounds**, in order. Prover round `msg o`: if `o` has one leaf (`logLeaf = logLen`) it is
**plain**: its `2^logLen` elements (`8·2^logLen` bytes) are sent in the clear; otherwise its root
(32 bytes) is sent. Those bytes are absorbed. Challenge round `chal nE idx`: `24·nE + 8·|idx|`
bytes are squeezed and read as elements `k_0, k_1, …` of `K`; `E` element `j` is
`k_{3j} + k_{3j+1}·y + k_{3j+2}·y²` (bytes `24j … 24j+23`) and index `j` is `k_{3·nE+j}` reduced
mod `2^b` (its low `b` bits, bytes `24·nE + 8j …`; exactly uniform as `b ≤ 64`, no rejection).

**Tape grammar** (`|tape| ≤ tapeCap = 2^20`; leftover bytes reject):
```
tape     ::= rounds openings
rounds   ::= for each prover round in order: its plain elements | its root
openings ::= for each query (j, l) the run of P.verify vk x chal makes, in order:
               nothing                      if oracle j ≥ 1 is plain (the leaf is its elements)
               leaf  path                   otherwise
leaf     ::= the 2^logLeaf elements of leaf l of oracle j
path     ::= depth levels, leaf level first; each level the A - 1 sibling digests of the
             current node, in increasing position (the node itself omitted)
```
Oracle `j ≥ 1` is the prover's `j`-th oracle in round order (`FullTranscript.oracles`), as in
`Protocol.specVerifier`. A query of an oracle that does not exist, or of a leaf `l` with
`l ≥ 2^(logLen - logLeaf)`, rejects, so a padding position is never opened. A repeated query is
opened again (no batching, S3-A4).
-/
import RecursionFast.Contract.Protocol
import RecursionFast.Contract.Hash.Blake2s

namespace RecursionFast

/-! ## Configuration -/

/-- The hash menu (DESIGN §3.2). It grows only by organiser PRs that add a Lean specification. -/
inductive HashId where
  /-- BLAKE2s-256 (RFC 7693, unkeyed, 32-byte digest; `Hash/Blake2s.lean`). -/
  | blake2s
  deriving DecidableEq, Repr

/-- The hash function named by a menu entry. Every menu hash has 32-byte digests. -/
def HashId.run : HashId → List UInt8 → List UInt8
  | .blake2s => blake2s256

/-- A compilation configuration, chosen by the submitter: the hash and the Merkle arity. -/
structure Cfg where
  /-- The hash of the Merkle trees and of the sponge. -/
  hash : HashId
  /-- The Merkle tree arity. -/
  arity : ℕ
  /-- The arity menu: 2, 4, 8 or 16. -/
  arity_ok : arity = 2 ∨ arity = 4 ∨ arity = 8 ∨ arity = 16

/-- A proof: a byte string. -/
abbrev Tape := List UInt8

/-- A digest (32 bytes for every menu hash). -/
abbrev Digest := List UInt8

/-- The tape cap: `2^20` bytes (1 MiB, DESIGN §6.5). -/
def tapeCap : ℕ := 2 ^ 20

/-- The digest of a padding position of a Merkle tree: 32 zero bytes. -/
def zeroDigest : Digest := List.replicate 32 0

/-! ## Byte encodings -/

/-- The 8 little-endian bytes of an element (`K.toBytes` as `UInt8`s). -/
def K.bytes (a : K) : List UInt8 := a.toBytes.map UInt8.ofBitVec

/-- The word whose little-endian bytes are the first 8 bytes of `b` (Rust `u64::from_le_bytes`;
missing bytes are 0). -/
def wordOfBytes (b : List UInt8) : Word :=
  (b.take 8).foldr (fun (c : UInt8) (w : Word) => w <<< 8 ||| c.toBitVec.setWidth 64) 0

/-- The element whose encoding is the first 8 bytes of `b`. -/
def K.ofBytes (b : List UInt8) : K := ⟨wordOfBytes b⟩

/-- The elements encoded by `b`, 8 bytes each (a trailing partial element is dropped). -/
def kList (b : List UInt8) : List K := go b []
where
  /-- Tail-recursive loop with the elements read so far, reversed. -/
  go : List UInt8 → List K → List K
    | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: r, acc =>
      go r (K.ofBytes [c0, c1, c2, c3, c4, c5, c6, c7] :: acc)
    | _, acc => acc.reverse

/-- The canonical bytes of a statement: its 32 elements in order (256 bytes). -/
def stmtBytes (x : Stmt) : List UInt8 := (List.ofFn x).flatMap K.bytes

/-- The compiled verification key: the protocol's key `VK L` and the root of the index oracle. -/
abbrev VKc (vkLen : ℕ) := (Fin vkLen → K) × Digest

/-- The canonical bytes of a compiled key: the elements of `VK L` in order, then the index root. -/
def VKc.toBytes {vkLen : ℕ} (vkc : VKc vkLen) : List UInt8 :=
  (List.ofFn vkc.1).flatMap K.bytes ++ vkc.2

/-- **The key digest** `D` of DESIGN §5.1: the hash of the key bytes (the `VK L` elements, then the
index root). It seeds the sponge, and a recursion statement's `d0`/`d1` hold it. -/
def VKc.digest (cfg : Cfg) {vkLen : ℕ} (vkc : VKc vkLen) : Digest := cfg.hash.run vkc.toBytes

/-! ## Merkle commitments (BCS) -/

/-- Whether a prover oracle is sent in the clear: it has a single leaf (`logLeaf = logLen`). -/
def OShape.plain (o : OShape) : Bool := o.logLeaf == o.logLen

/-- `log₂` of the arity: 1, 2, 3 or 4. -/
def Cfg.logArity (cfg : Cfg) : ℕ :=
  match cfg.arity with
  | 2 => 1
  | 4 => 2
  | 8 => 3
  | _ => 4

/-- The depth of the Merkle tree of an oracle: `⌈(logLen - logLeaf) / log₂ A⌉`, the least `d` with
`2^(logLen - logLeaf) ≤ A^d` (`Library/Compile.lean`, `depth_spec`). -/
def Cfg.depth (cfg : Cfg) (o : OShape) : ℕ :=
  (o.logLen - o.logLeaf + cfg.logArity - 1) / cfg.logArity

/-- The digest of a leaf: the hash of its bytes. -/
def leafHash (cfg : Cfg) (leaf : List K) : Digest := cfg.hash.run (leaf.flatMap K.bytes)

/-- The digests of a uniform subtree at heights `0, 1, …, n - 1`, from its height-0 digest `d`:
each is the hash of `A` copies of the one below. -/
def tower (cfg : Cfg) (d : Digest) : ℕ → List Digest
  | 0 => []
  | n + 1 => d :: tower cfg (cfg.hash.run (List.replicate cfg.arity d).flatten) n

/-- Node `p` at height `h` of the Merkle tree of `o` (the header's tree), and whether it is
**empty**: every position below it is a leaf of `o` whose elements are all zero. An empty node's
digest is read from `tE` (the tower of the all-zero leaf's digest), an all-padding node's from
`tZ` (the tower of the zero digest); only the other nodes are hashed. -/
def nodeS (cfg : Cfg) (o : Oracle) (tE tZ : List Digest) : ℕ → ℕ → Digest × Bool
  | 0, p =>
    if p < o.shape.leaves then
      let lf := o.leaf p
      if lf.all (· == 0) then (tE.getD 0 [], true) else (leafHash cfg lf, false)
    else (tZ.getD 0 [], false)
  | h + 1, p =>
    if o.shape.leaves ≤ cfg.arity ^ (h + 1) * p then (tZ.getD (h + 1) [], false) else
      let cs := (List.range cfg.arity).map fun i => nodeS cfg o tE tZ h (cfg.arity * p + i)
      if cs.all (·.2) then (tE.getD (h + 1) [], true)
      else (cfg.hash.run (cs.map (·.1)).flatten, false)

/-- The Merkle root of an oracle: node 0 at height `depth`. It costs the reads of `o` plus at most
`depth` hashes per non-empty leaf and per level of the padding boundary, whatever the oracle's
size (S9F-M4); its value is the dense tree's (`Library/Compile.lean`, `commit_eq_commitDense`). -/
def commit (cfg : Cfg) (o : Oracle) : Digest :=
  let d := cfg.depth o.shape
  (nodeS cfg o (tower cfg (leafHash cfg (List.replicate (2 ^ o.shape.logLeaf) 0)) (d + 1))
    (tower cfg zeroDigest (d + 1)) d 0).1

/-- Climb an authentication path from digest `d` at position `p`: at each level insert `d` among
the `A - 1` siblings at position `p mod A`, hash the `A` digests, and move to position `p / A`. -/
def climb (cfg : Cfg) : Digest → ℕ → List (List Digest) → Digest
  | d, _, [] => d
  | d, p, sib :: path => climb cfg
      (cfg.hash.run (sib.take (p % cfg.arity) ++ d :: sib.drop (p % cfg.arity)).flatten)
      (p / cfg.arity) path

/-- Whether `path` authenticates `leaf` as leaf `l` under `root`. -/
def verifyPath (cfg : Cfg) (root : Digest) (l : ℕ) (leaf : List K) (path : List (List Digest)) :
    Bool :=
  climb cfg (leafHash cfg leaf) l path == root

/-- **The indexer**: the protocol's key and the root of its index oracle `IDX L`. -/
def index (cfg : Cfg) {k : ℕ} (P : Protocol k) (L : Layout K) : VKc P.vkLen :=
  (P.VK L, commit cfg ⟨P.idxShape, P.IDX L⟩)

/-! ## Fiat–Shamir sponge -/

/-- Absorb `m` into the state `s`: `H(0x00 ‖ s ‖ m)`. -/
def absorb (cfg : Cfg) (s : Digest) (m : List UInt8) : Digest := cfg.hash.run (0 :: s ++ m)

/-- Squeeze `len` bytes from `s`: `⌈len/32⌉` ratchet steps `s ← H(0x01 ‖ s)`; the output is the
successive states, truncated to `len` bytes; the new state is the last one. -/
def squeeze (cfg : Cfg) (s : Digest) (len : ℕ) : List UInt8 × Digest := go ((len + 31) / 32) s []
where
  /-- `b` more steps from `s`, with the states output so far, reversed. -/
  go : ℕ → Digest → List Digest → List UInt8 × Digest
    | 0, s, acc => (acc.reverse.flatten.take len, s)
    | b + 1, s, acc => let s := cfg.hash.run (1 :: s); go b s (s :: acc)

/-- The sponge state after the key and the statement: `x` absorbed into the key digest `D`. -/
def seed (cfg : Cfg) {vkLen : ℕ} (vkc : VKc vkLen) (x : Stmt) : Digest :=
  absorb cfg (vkc.digest cfg) (stmtBytes x)

/-- The number of bytes a challenge round squeezes: 24 per `E` element, 8 per index. -/
def Round.chalLen : Round → ℕ
  | .msg _ => 0
  | .chal nE idx => 24 * nE + 8 * idx.length

/-- The challenge of a round from its squeezed bytes read as elements `ks` of `K`: `E` element `j`
is `⟨ks[3j], ks[3j+1], ks[3j+2]⟩`, index `j` the low `b` bits of `ks[3·nE + j]`. (A prover round
has no challenge; `0`.) -/
def Round.decodeK : (r : Round) → Array K → r.Ty
  | .msg _, _ => fun _ => 0
  | .chal nE idx, ks => (fun j => ⟨ks.getD (3 * j) 0, ks.getD (3 * j + 1) 0, ks.getD (3 * j + 2) 0⟩,
      fun j => (ks.getD (3 * nE + j) 0).bits.setWidth (idx.get j))

/-- The challenge a round's squeezed bytes encode. -/
def Round.decode (r : Round) (b : List UInt8) : r.Ty := r.decodeK (kList b).toArray

/-! ## The verifier -/

/-- Read exactly `n` bytes (`none` if the tape is shorter); `acc` holds the bytes read, reversed. -/
def takeN : ℕ → Tape → List UInt8 → Option (List UInt8 × Tape)
  | 0, t, acc => some (acc.reverse, t)
  | _ + 1, [], _ => none
  | n + 1, c :: t, acc => takeN n t (c :: acc)

/-- Read `n` items with the reader `r`. -/
def readMany {α : Type} (r : Tape → Option (α × Tape)) : ℕ → Tape → Option (List α × Tape)
  | 0, t => some ([], t)
  | n + 1, t => match r t with
    | some (a, t) => (readMany r n t).map fun p => (a :: p.1, p.2)
    | none => none

/-- Read one opening of an oracle of shape `o`: a leaf of `2^logLeaf` elements, then `depth` levels
of `A - 1` digests. -/
def readOpening (cfg : Cfg) (o : OShape) (t : Tape) : Option (List K × List (List Digest) × Tape) :=
  match takeN (8 * 2 ^ o.logLeaf) t [] with
  | some (leaf, t) =>
    (readMany (readMany (fun t => takeN 32 t []) (cfg.arity - 1)) (cfg.depth o) t).map fun p =>
      (kList leaf, p.1, p.2)
  | none => none

/-- The bytes a prover round puts in the rounds section: plain elements or the root. -/
def msgLen (o : OShape) : ℕ := if o.plain then 8 * 2 ^ o.logLen else 32

/-- The Fiat–Shamir pass over the rounds `rs` from sponge state `s`: a prover round reads its bytes
from the tape and absorbs them; a challenge round squeezes its bytes. Returns the bytes of every
round (read or squeezed, in order, appended to `es`) and the rest of the tape. -/
def pass (cfg : Cfg) : List Round → Digest → Tape → Array (List UInt8) →
    Option (Array (List UInt8) × Tape)
  | [], _, t, es => some (es, t)
  | .msg o :: rs, s, t, es => match takeN (msgLen o) t [] with
    | some (b, t) => pass cfg rs (absorb cfg s b) t (es.push b)
    | none => none
  | .chal nE idx :: rs, s, t, es => match squeeze cfg s (Round.chal nE idx).chalLen with
    | (b, s) => pass cfg rs s t (es.push b)

/-- The challenges of a pass, from every round's bytes read as elements of `K` (`ks`, computed
once): round `c`'s challenge decoded. -/
def chals {n : ℕ} (sh : Fin n → Round) (ks : Array (Array K)) : Challenges sh :=
  fun c => (sh c.1).decodeK (ks.getD c.1 #[])

/-- What the verifier holds of an oracle: its root, or (plain) its elements. -/
inductive View where
  /-- A Merkle-committed oracle of shape `o` with root `r`. -/
  | root (o : OShape) (r : Digest)
  /-- A plain oracle of shape `o` with elements `ws`. -/
  | plain (o : OShape) (ws : List K)

/-- The views of a round's oracles, from the round's bytes. -/
def roundViews : Round → List UInt8 → List View
  | .msg o, b => [if o.plain then .plain o (kList b) else .root o b]
  | .chal _ _, _ => []

/-- The views of all oracles: the index oracle with root `root0`, then the prover's, in round
order. -/
def views {k : ℕ} (P : Protocol k) (root0 : Digest) (es : Array (List UInt8)) : Array View :=
  (View.root P.idxShape root0 ::
    (List.ofFn fun i : Fin P.n => roundViews (P.shape i) (es.getD i.val [])).flatten).toArray

/-- Run a query program against the openings on the tape: a query of a plain oracle reads its
elements; any other query reads an opening, which must authenticate under the oracle's root. Out
of range queries, short or malformed openings, failed paths and leftover bytes give `none`. -/
def runQ (cfg : Cfg) (vs : Array View) : QProg Bool → Tape → Option Bool
  | .done b, [] => some b
  | .done _, _ :: _ => none
  | .query j l cont, t => match vs[j]? with
    | some (.plain o ws) => if l < o.leaves then runQ cfg vs (cont ws) t else none
    | some (.root o r) =>
      if l < o.leaves then
        match readOpening cfg o t with
        | some (leaf, path, t) =>
          if verifyPath cfg r l leaf path then runQ cfg vs (cont leaf) t else none
        | none => none
      else none
    | none => none

/-- **The compiled verifier.** Accept iff the tape is within the cap, the key's index root has 32
bytes, the rounds section parses, and the query program, on the Fiat–Shamir challenges, accepts
against the openings with no bytes left over. `vkc` is any compiled key: on the badge path it is
the indexer's output (`index`); in `aggOK` it is a key from the node's witness, bound to the
statement only by its digest. -/
def NARG (cfg : Cfg) {k : ℕ} (P : Protocol k) (vkc : VKc P.vkLen) (x : Stmt) (t : Tape) : Bool :=
  decide (t.length ≤ tapeCap) && vkc.2.length == 32 &&
    match pass cfg (List.ofFn P.shape) (seed cfg vkc x) t #[] with
    | some (es, t) =>
      let ks := es.map fun b => (kList b).toArray
      runQ cfg (views P vkc.2 es) (P.verify vkc.1 x (chals P.shape ks)) t == some true
    | none => false

end RecursionFast

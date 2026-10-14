/-
# Contract: the fields K = GF(2^64) and E = GF(2^192)            (TRUSTED, Lean core only)

`K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, in the polynomial basis: bit `i` of a 64-bit word
is the coefficient of `x^i`. Every 64-bit word is an element, so every 8-byte string is a
canonical encoding.

`E = K[y] / (y^3 + y + 1) = GF(2^192)`, three K-limbs `c0 + c1·y + c2·y²`. E is the only
challenge field (DESIGN §2–3): a K-valued challenge has error `≥ 2^-64` and cannot meet the cap.

Nothing here is a claim to be believed: the field axioms, `|K| = 2^64`, `|E| = 2^192`, the
irreducibility of both moduli and the identification with Mathlib's `AdjoinRoot` and with
CompPoly's `BF64`/`BF64.Ext3` (by `rfl`) are theorems of the untrusted library
(`RecursionFast/Library/Field.lean`). The arithmetic is CompPoly's `carryLessMul`/`foldStep`/
`reduce` restated, so the bridge is definitional.
-/

namespace RecursionFast

/-- A 64-bit machine word (also the unit of the tape and of oracle leaves). -/
abbrev Word := BitVec 64

/-- An element of `K = GF(2^64)`: bit `i` of `bits` is the coefficient of `x^i`. -/
structure K where
  bits : Word
  deriving DecidableEq

namespace K

/-- Carry-less product of two polynomials of degree `< 64` over GF(2), as a 128-bit word
(schoolbook shift-and-xor). Also the semantics of the Zbc instructions (`Machine.lean`). -/
def clmul (a b : Word) : BitVec 128 :=
  Fin.foldl 64 (fun acc i => if a.getLsbD i then acc ^^^ (b.zeroExtend 128 <<< (i : Nat)) else acc) 0

/-- One reduction fold `hi·x^64 + lo ↦ hi·(x^4 + x^3 + x + 1) + lo` (`x^64 ≡ 0x1B`). -/
def fold (t : BitVec 128) : BitVec 128 :=
  clmul ((t >>> 64).setWidth 64) 0x1B ^^^ (t.setWidth 64).zeroExtend 128

/-- Reduction modulo `x^64 + x^4 + x^3 + x + 1`: two folds bring the degree below 64. -/
def reduce (t : BitVec 128) : Word := (fold (fold t)).setWidth 64

instance : Zero K := ⟨⟨0⟩⟩
instance : One K := ⟨⟨1⟩⟩
/-- Addition = subtraction = xor (characteristic 2); negation is the identity. -/
instance : Add K := ⟨fun a b => ⟨a.bits ^^^ b.bits⟩⟩
instance : Sub K := ⟨fun a b => ⟨a.bits ^^^ b.bits⟩⟩
instance : Neg K := ⟨fun a => a⟩
/-- Multiplication: carry-less product, then reduction. -/
instance : Mul K := ⟨fun a b => ⟨reduce (clmul a.bits b.bits)⟩⟩

/-- Canonical encoding: the 8 little-endian bytes of `bits` (Rust `u64::to_le_bytes`). On the
machine an element is one doubleword, which memory stores little-endian, i.e. these bytes. -/
def toBytes (a : K) : List (BitVec 8) := List.ofFn fun i : Fin 8 => (a.bits >>> (8 * i.val)).setWidth 8

end K

/-- An element `c0 + c1·y + c2·y²` of `E = K[y]/(y^3 + y + 1) = GF(2^192)`. -/
structure E where
  c0 : K
  c1 : K
  c2 : K
  deriving DecidableEq

namespace E

instance : Zero E := ⟨⟨0, 0, 0⟩⟩
instance : One E := ⟨⟨1, 0, 0⟩⟩
instance : Add E := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩⟩
/-- Schoolbook product folded by `y^3 = y + 1`, `y^4 = y^2 + y` (9 products in K). -/
instance : Mul E := ⟨fun a b =>
  let p3 := a.c1 * b.c2 + a.c2 * b.c1
  let p4 := a.c2 * b.c2
  ⟨a.c0 * b.c0 + p3, a.c0 * b.c1 + a.c1 * b.c0 + p3 + p4, a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + p4⟩⟩

/-- Canonical encoding as words: limbs `c0, c1, c2` in this order (24 bytes, each limb LE). -/
def toWords (a : E) : List Word := [a.c0.bits, a.c1.bits, a.c2.bits]

/-- Canonical 24-byte encoding: limbs `c0, c1, c2`, each 8 bytes little-endian. -/
def toBytes (a : E) : List (BitVec 8) := a.c0.toBytes ++ a.c1.toBytes ++ a.c2.toBytes

end E

end RecursionFast

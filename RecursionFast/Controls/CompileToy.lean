/-
# Control protocol for the compiled argument (`Contract/Compile.lean`)

`cmpToy : Protocol 20` is the small, deliberately insecure protocol S1-A12(b) asks for (`Secure`
is not required of a compile control; the toy of `Controls/Toy.lean` sends `2^(k+10)` elements,
which the kernel cannot hash). Index oracle: 2 leaves of 1 element (`100`, `101`). Rounds: the
prover sends a 4-leaf oracle of 1 element per leaf (`p ↦ p + 7`, Merkle-committed); the verifier
sends one `E` element `e` and one 2-bit index `i`; the prover sends one element `m` in the clear
(a plain oracle). The verifier reads `m` and rejects unless `m = e.c0 + vk 0 + x 0`, then reads
leaf `i` of oracle 1 and leaf `i mod 2` of the index, and accepts iff they are `i + 7` and
`i mod 2 + 100`.

This file holds the protocol, the tapes and the key (as byte-list literals: the kernel decodes a
`String` slowly), the evaluated cross-checks (`#guard`: each literal equals the independent Python
reference `probes/s3/compile_ref.py`, which uses `hashlib.blake2s`; the honest prover's tape at
arity 2 and 4 equals it; the arity-4 tape is accepted), `index_eq`, and `digest_kat` (the key
digest `D`, S3-M1). The kernel runs are in `Controls/Compile.lean` (honest and Merkle side) and
`Controls/CompileFS.lean` (Fiat–Shamir), two files so that they build in parallel.

Byte offsets in the honest tape at arity 2 (152 bytes): `0–31` root of oracle 1, `32–39` the plain
element, `40–47` leaf `i` of oracle 1, `48–111` its path (2 levels × 1 digest), `112–119` leaf
`i mod 2` of the index, `120–151` its path.
-/
import RecursionFast.Library.Compile
import RecursionFast.Library.Extractor

namespace RecursionFast.Controls.Compile
open RecursionFast

/-! ## The control protocol -/

/-- Rounds: a 4-leaf oracle, a challenge (one `E` element, one 2-bit index), a plain element. -/
def cmpShape : Fin 3 → Round
  | 0 => .msg ⟨2, 0⟩
  | 1 => .chal 1 [2]
  | 2 => .msg ⟨0, 0⟩

/-- The key: one constant element. -/
def cmpVK (_ : Layout K) : Fin 1 → K := fun _ => ⟨0x1234⟩

/-- The index oracle: 2 leaves, `100` and `101`. -/
def cmpIDX (_ : Layout K) : OVal ⟨1, 0⟩ := fun p => ⟨BitVec.ofNat 64 (p.val + 100)⟩

/-- The verifier: read the plain element `m` and reject unless `m = e.c0 + vk 0 + x 0`; then read
leaf `i` of oracle 1 and leaf `i mod 2` of the index, and accept iff they are `i + 7` and
`i mod 2 + 100`. (Checking the plain element first makes the Fiat–Shamir negatives cheap.) -/
def cmpVerify (vk : Fin 1 → K) (x : Stmt) (ρ : Challenges cmpShape) : QProg Bool :=
  let c := ρ ⟨1, rfl⟩
  let i := (c.2 ⟨0, by decide⟩).toNat
  .query 2 0 fun m => if m != [(c.1 0).c0 + vk 0 + x 0] then .done false else
    .query 1 i fun a => .query 0 (i % 2) fun b =>
      .done (a == [⟨BitVec.ofNat 64 (i + 7)⟩] && b == [⟨BitVec.ofNat 64 (i % 2 + 100)⟩])

/-- The honest answer to the challenge `e`. -/
def answer (L : Layout K) (x : Stmt) (e : E) : K := e.c0 + cmpVK L 0 + x 0

/-- The honest prover: the oracle `p ↦ p + 7`, then the answer. -/
def cmpNext (s : Layout K × Stmt) (_ : List (Table K)) (m : MessageIdx cmpShape)
    (tr : Transcript cmpShape m.1.castSucc) : (cmpShape m.1).Ty :=
  match m, tr with
  | ⟨0, _⟩, _ => (fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩ : OVal ⟨2, 0⟩)
  | ⟨1, h⟩, _ => absurd h (by decide)
  | ⟨2, _⟩, tr => (fun _ => answer s.1 s.2 ((tr (1 : Fin 2)).1 ⟨0, by decide⟩) : OVal ⟨0, 0⟩)

/-- **The control protocol** (class 20, not secure). -/
def cmpToy : Protocol 20 where
  k_range := by decide
  n := 3
  n_le := by decide
  shape := cmpShape
  vkLen := 1
  vkLen_le := by decide
  VK := cmpVK
  idxShape := ⟨1, 0⟩
  IDX := cmpIDX
  shape_ok := ⟨fun j => match j with
    | 0 => ⟨by decide, by decide⟩
    | 1 => fun b hb => by simp at hb; omega
    | 2 => ⟨by decide, by decide⟩, by decide, by decide⟩
  prover := { next := cmpNext, output := fun _ _ _ => ((), ()) }
  verify := cmpVerify
  extractor := firstMsgImage 20 3  -- any image and split: not claimed secure
  ε := fun _ => 0

/-- BLAKE2s, arity 2. -/
def cfg2 : Cfg := ⟨.blake2s, 2, by decide⟩
/-- BLAKE2s, arity 4. -/
def cfg4 : Cfg := ⟨.blake2s, 4, by decide⟩

/-- A layout (the toy ignores it). -/
def L0 : Layout K := ⟨[], fun _ => .eq, 0⟩
/-- A statement with distinct elements: `x i = 257 i`. -/
def x0 : Stmt := fun i => ⟨BitVec.ofNat 64 (i.val * 0x0101)⟩

/-! ## Bytes -/

/-- The value of a lowercase hex digit. -/
def hexDigit (c : Char) : Nat := if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

/-- The bytes written by a list of lowercase hex digits. -/
def hexBytes : List Char → List UInt8
  | a :: b :: r => (16 * hexDigit a + hexDigit b).toUInt8 :: hexBytes r
  | _ => []

/-- The bytes written by a lowercase hex string (used by `#guard`s only: the kernel decodes a
`String` slowly). -/
def hex (s : String) : List UInt8 := hexBytes s.toList

/-- Bytes as a lowercase hex string. -/
def toHex (b : List UInt8) : String := String.join (b.map fun c =>
  let s := String.ofList (Nat.toDigits 16 c.toNat); if s.length < 2 then "0" ++ s else s)

/-- Flip bit 0 of byte `i`. -/
def flip (t : Tape) (i : ℕ) : Tape := t.modify i (· ^^^ 1)

/-- The honest tape at arity 2 (152 bytes): `prove cfg2 cmpToy L0 x0 []` and the Python reference
`probes/s3/compile_ref.py` (both `#guard`ed below). -/
def tape2 : Tape :=
  [0x60, 0x04, 0xbd, 0xd3, 0x0c, 0xf0, 0x06, 0xe9, 0x2e, 0xc9, 0x66, 0xda,
   0x6a, 0x25, 0x7f, 0x20, 0xf6, 0xf4, 0x2b, 0xa1, 0xca, 0xdd, 0xb6, 0xec,
   0xfb, 0x16, 0x2e, 0x2f, 0x69, 0x8a, 0x6a, 0xef, 0x96, 0xeb, 0x4d, 0x6b,
   0xcf, 0x63, 0xb0, 0x88, 0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0xf4, 0x4b, 0x94, 0x0e, 0x2f, 0x26, 0x2b, 0x47, 0x36, 0xb9, 0x53, 0xbe,
   0x32, 0xcf, 0xf7, 0x68, 0xac, 0x40, 0x2e, 0x77, 0x34, 0xb2, 0xed, 0x85,
   0xe2, 0x90, 0x2b, 0x8e, 0x2f, 0x25, 0xeb, 0xc8, 0x10, 0x17, 0xe4, 0xde,
   0x4a, 0xa2, 0xb9, 0x84, 0x3e, 0x2a, 0xfc, 0xbd, 0xfd, 0x7a, 0x8f, 0x8f,
   0x5b, 0xa9, 0xf7, 0xc5, 0xcb, 0x5c, 0x4b, 0x70, 0x38, 0xe6, 0xa3, 0x0c,
   0xca, 0x2f, 0x47, 0x6f, 0x64, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x4a, 0x36, 0x50, 0xaa, 0xac, 0x41, 0xfb, 0x21, 0xac, 0x53, 0x74, 0xd5,
   0x56, 0x2e, 0x6c, 0x83, 0x69, 0x97, 0x32, 0x61, 0x09, 0x15, 0x85, 0xe9,
   0x5f, 0x41, 0xed, 0x6e, 0x35, 0xb8, 0x59, 0x5b]

/-- The compiled key at arity 2: `VK L0` and the index root (`index_eq`; Python: the same root). -/
def vkc2 : VKc 1 :=
  (cmpVK L0, [0x09, 0xb9, 0x0c, 0x7d, 0xb0, 0x5d, 0x85, 0x9d, 0x13, 0x3d, 0x27, 0x12,
    0x99, 0x2b, 0xa0, 0x61, 0x75, 0x01, 0xcc, 0x91, 0x47, 0x0a, 0xfc, 0xe1,
    0xed, 0x8c, 0x99, 0xa9, 0x95, 0x53, 0xd6, 0xf8])

/-- The statement with bit 0 of `x 31` flipped (the verifier never reads `x 31`). -/
def x1 : Stmt := fun i => if i = 31 then ⟨(x0 i).bits ^^^ 1⟩ else x0 i

/-- A cheating prover: it commits to the oracle `p ↦ p + 1000`, but answers the challenges of the
honest root, with valid openings of its own oracle under its own root. -/
def cheat : Tape :=
  let other : Oracle := ⟨⟨2, 0⟩, fun p => ⟨BitVec.ofNat 64 (p.val + 1000)⟩⟩
  let idxO : Oracle := ⟨⟨1, 0⟩, cmpIDX L0⟩
  match pass cfg2 (List.ofFn cmpShape) (seed cfg2 vkc2 x0) tape2 #[] with
  | some (es, _) =>
    let c := chals cmpShape (es.map fun b => (kList b).toArray) ⟨1, rfl⟩
    let i := (c.2 ⟨0, by decide⟩).toNat
    commit cfg2 other ++ (answer L0 x0 (c.1 0)).bytes ++
      (other.leaf i).flatMap K.bytes ++ (pathOf cfg2 other i).flatten.flatten ++
      (idxO.leaf (i % 2)).flatMap K.bytes ++ (pathOf cfg2 idxO (i % 2)).flatten.flatten
  | none => []

/-- `cheat`, as `#guard`ed below and as the Python reference computes it (`cheat_tape`). -/
def cheatTape : Tape :=
  [0xce, 0xac, 0x3a, 0x7c, 0xae, 0x95, 0x6c, 0xf1, 0x43, 0x2e, 0xc4, 0x4c,
   0x0a, 0xeb, 0x65, 0x46, 0x13, 0x16, 0xa9, 0x8b, 0x72, 0x56, 0xe3, 0x70,
   0x93, 0xfb, 0x3e, 0x04, 0xe7, 0x2f, 0x15, 0x5a, 0x96, 0xeb, 0x4d, 0x6b,
   0xcf, 0x63, 0xb0, 0x88, 0xea, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x20, 0x35, 0xff, 0xa3, 0x41, 0xfd, 0x2d, 0x0f, 0x80, 0x63, 0x4a, 0xc8,
   0x14, 0x73, 0x2d, 0x53, 0x5b, 0xed, 0x4a, 0xd5, 0xbb, 0xc1, 0x21, 0x5b,
   0xe7, 0xc0, 0x11, 0xb8, 0xf4, 0x93, 0xae, 0x4b, 0xa3, 0x31, 0x38, 0x2b,
   0x7c, 0xac, 0x8f, 0xa5, 0xa3, 0xe0, 0x4e, 0x2d, 0xe0, 0x04, 0x2b, 0xba,
   0x1f, 0x69, 0x03, 0xfd, 0x96, 0x95, 0x17, 0xfb, 0x2c, 0x11, 0x4b, 0xa1,
   0x89, 0xc0, 0xb6, 0x9a, 0x64, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x4a, 0x36, 0x50, 0xaa, 0xac, 0x41, 0xfb, 0x21, 0xac, 0x53, 0x74, 0xd5,
   0x56, 0x2e, 0x6c, 0x83, 0x69, 0x97, 0x32, 0x61, 0x09, 0x15, 0x85, 0xe9,
   0x5f, 0x41, 0xed, 0x6e, 0x35, 0xb8, 0x59, 0x5b]

/-! ## Evaluated checks (compiled code; the kernel checks follow) -/

-- The literals are the Python reference's output (`logs/S3/python-ref.log`), byte for byte.
#guard tape2 = hex ("6004bdd30cf006e92ec966da6a257f20f6f42ba1caddb6ecfb162e2f698a6aef" ++
  "96eb4d6bcf63b088" ++ "0900000000000000" ++
  "f44b940e2f262b4736b953be32cff768ac402e7734b2ed85e2902b8e2f25ebc8" ++
  "1017e4de4aa2b9843e2afcbdfd7a8f8f5ba9f7c5cb5c4b7038e6a30cca2f476f" ++ "6400000000000000" ++
  "4a3650aaac41fb21ac5374d5562e6c8369973261091585e95f41ed6e35b8595b")
#guard vkc2.2 = hex "09b90c7db05d859d133d2712992ba0617501cc91470afce1ed8c99a99553d6f8"
#guard cheatTape = hex ("ceac3a7cae956cf1432ec44c0aeb65461316a98b7256e37093fb3e04e72f155a" ++
  "96eb4d6bcf63b088" ++ "ea03000000000000" ++
  "2035ffa341fd2d0f80634ac814732d535bed4ad5bbc1215be7c011b8f493ae4b" ++
  "a331382b7cac8fa5a3e04e2de0042bba1f6903fd969517fb2c114ba189c0b69a" ++ "6400000000000000" ++
  "4a3650aaac41fb21ac5374d5562e6c8369973261091585e95f41ed6e35b8595b")
-- The honest compiled prover outputs `tape2` at arity 2; the cheat is `cheat`.
#guard prove cfg2 cmpToy L0 x0 [] = some tape2
#guard cheat = cheatTape
#guard (tape2.length, cheatTape.length) = (152, 152)
-- At arity 4 the honest tape (248 bytes: 3 siblings per level, the index tree padded with two
-- zero digests) is accepted, and equals the Python reference's.
#guard (prove cfg4 cmpToy L0 x0 []).map (NARG cfg4 cmpToy (index cfg4 cmpToy L0) x0) = some true
#guard (prove cfg4 cmpToy L0 x0 []).map toHex = some ("f9620879795033a7756ce7c76b8b71ba3a318bae" ++
  "44a0d912b7d5c90befcc5d9bf6521014ff88ae200a00000000000000f4d461fe077265e6ad1f59de4b3cfdf7b5" ++
  "cd68dac6fb07a4ccc50d26b9e03a0736e2e920278b3c0c59fd9fa134c4a410954f51c3a366348bec4fd546a6be" ++
  "98e95b1c35effb70feff3a94086128c479694d71b124fa76d7286d52c126d2b6b2fb65000000000000007467493a" ++
  "66d2f96a698027ab869dedce371e0d36d0ae2643371baf3f693876da" ++
  String.ofList (List.replicate 128 '0'))
-- Merkle roots of the 4-leaf oracle `p ↦ p + 7` (quoted in the S3 RESULT; Python agrees).
#eval (toHex (commit cfg2 ⟨⟨2, 0⟩, fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩⟩),
  toHex (commit cfg4 ⟨⟨2, 0⟩, fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩⟩))
#eval tape2.length

/-! ## Kernel checks -/

/-- `vkc2` is the indexer's output. -/
theorem index_eq : index cfg2 cmpToy L0 = vkc2 := Prod.ext rfl (by decide +kernel)

/-- Known answer for the key digest `D` (S3-M1): `vkc2.digest cfg2` is
`hashlib.blake2s(le64(0x1234) ‖ root)` = `0f4c678b…229556d3` (Python, `logs/S3/python-ref.log`). -/
theorem digest_kat : vkc2.digest cfg2 =
    [0x0f, 0x4c, 0x67, 0x8b, 0xba, 0x7a, 0xe5, 0x30, 0x87, 0xaa, 0xde, 0xa2,
      0xae, 0x14, 0xe9, 0x44, 0xfc, 0xd2, 0xba, 0x44, 0x94, 0x5b, 0x68, 0xc6,
      0x01, 0xb9, 0xa1, 0xf6, 0x22, 0x95, 0x56, 0xd3] := by
  decide +kernel

end RecursionFast.Controls.Compile

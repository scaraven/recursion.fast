/-
# Control data: recursion (`Contract/Recursion.lean`) on the control protocol `cmpToy`

Statements, node witnesses and honest tapes of `cmpToy` at arity 2 (`Controls/CompileToy.lean`),
as literals (the kernel decodes a `String` slowly). Each literal is pinned (`#guard`, compiled) to
the independent Python reference `probes/s5/recursion_ref.py` (`hashlib.blake2s`, output in
`logs/S5/python-ref.log`) and to the honest compiled prover `prove`. The kernel checks are in
`Controls/Recursion.lean` and `Controls/RecursionNode.lean`, two files that build in parallel;
they evaluate each `NARG` run once (`tape2` under `x0` is `Controls/Compile.lean`'s `runs.1`)
and derive `aggOK` from the library's lemmas (`Library/Recursion.lean`).

* Key: `vkc2`, `cmpToy` indexed on `L0`. `cmpToy` ignores the layout, so in most controls the
  recursion key and the leaf key are the same key; the tags are told apart by the statements
  (`d3`, S5-A11). The controls with distinct keys use `vkK` (below).
* Statements: `x0`, `x1` (`Controls/CompileToy.lean`; `x1` is `x0` with bit 0 of `x 31` flipped);
  `xN`, the two-leaf node of `x0`, `x1`; `xR`, the node of `xN` and `x0` (level 2: a node child and
  a leaf child); `xD0`, `xD1`, `xN` with bit 0 of `d0` (element 0) or of `d1` (element 4) flipped.
  `xT`, the statement tree of depth 2 over `x0, x1, x0, x1`.
* Node witnesses: `nwN` (the two-leaf node), `nwR` (level 2), `nwD0`, `nwD1` (a node child whose
  `d0` or `d1` differs from the parent's, with an honest tape that `NARG` accepts, so the key
  check alone rejects it), `nwMis` (`nwR` with the node child tagged leaf, S5-m1).
* A second key `vkK` (`cmpToyK`: key element `0x1235`, same index) and its honest tape `tapeK`,
  for nodes whose recursion and leaf keys differ (`nwK`, `nwKC`, S5-m7); a key `vkC33` with a
  33-byte root (`nw33`).
-/
import RecursionFast.Contract.Certificate
import RecursionFast.Library.Recursion
import RecursionFast.Controls.Compile
import RecursionFast.Controls.Negative

namespace RecursionFast.Controls.Recursion
open RecursionFast RecursionFast.Controls.Compile

/-- The statement whose elements are the words `ws` (missing words are `0`). -/
def stmtOfWords (ws : List Word) : Stmt := fun i => ⟨ws.getD i 0⟩

/-- `x` with bit 0 of element `i` flipped. -/
def bump (x : Stmt) (i : Fin 32) : Stmt := fun j => if j = i then ⟨(x j).bits ^^^ 1⟩ else x j

/-- The honest tape of `x1` (`prove cfg2 cmpToy L0 x1 []`; Python `tape x1`). -/
def tapeX1 : Tape :=
  [0x60, 0x04, 0xbd, 0xd3, 0x0c, 0xf0, 0x06, 0xe9, 0x2e, 0xc9, 0x66, 0xda,
   0x6a, 0x25, 0x7f, 0x20, 0xf6, 0xf4, 0x2b, 0xa1, 0xca, 0xdd, 0xb6, 0xec,
   0xfb, 0x16, 0x2e, 0x2f, 0x69, 0x8a, 0x6a, 0xef, 0x0d, 0x48, 0x8a, 0x48,
   0xcf, 0x4f, 0x35, 0xa7, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x5b, 0x1c, 0x35, 0xef, 0xfb, 0x70, 0xfe, 0xff, 0x3a, 0x94, 0x08, 0x61,
   0x28, 0xc4, 0x79, 0x69, 0x4d, 0x71, 0xb1, 0x24, 0xfa, 0x76, 0xd7, 0x28,
   0x6d, 0x52, 0xc1, 0x26, 0xd2, 0xb6, 0xb2, 0xfb, 0x10, 0x17, 0xe4, 0xde,
   0x4a, 0xa2, 0xb9, 0x84, 0x3e, 0x2a, 0xfc, 0xbd, 0xfd, 0x7a, 0x8f, 0x8f,
   0x5b, 0xa9, 0xf7, 0xc5, 0xcb, 0x5c, 0x4b, 0x70, 0x38, 0xe6, 0xa3, 0x0c,
   0xca, 0x2f, 0x47, 0x6f, 0x65, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x74, 0x67, 0x49, 0x3a, 0x66, 0xd2, 0xf9, 0x6a, 0x69, 0x80, 0x27, 0xab,
   0x86, 0x9d, 0xed, 0xce, 0x37, 0x1e, 0x0d, 0x36, 0xd0, 0xae, 0x26, 0x43,
   0x37, 0x1b, 0xaf, 0x3f, 0x69, 0x38, 0x76, 0xda]

/-- The honest tape of `xN` (`prove cfg2 cmpToy L0 xN []`; Python `tape xN`). -/
def tapeXN : Tape :=
  [0x60, 0x04, 0xbd, 0xd3, 0x0c, 0xf0, 0x06, 0xe9, 0x2e, 0xc9, 0x66, 0xda,
   0x6a, 0x25, 0x7f, 0x20, 0xf6, 0xf4, 0x2b, 0xa1, 0xca, 0xdd, 0xb6, 0xec,
   0xfb, 0x16, 0x2e, 0x2f, 0x69, 0x8a, 0x6a, 0xef, 0xfb, 0xc9, 0x58, 0x85,
   0xef, 0x8b, 0xed, 0x20, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x36, 0xe2, 0xe9, 0x20, 0x27, 0x8b, 0x3c, 0x0c, 0x59, 0xfd, 0x9f, 0xa1,
   0x34, 0xc4, 0xa4, 0x10, 0x95, 0x4f, 0x51, 0xc3, 0xa3, 0x66, 0x34, 0x8b,
   0xec, 0x4f, 0xd5, 0x46, 0xa6, 0xbe, 0x98, 0xe9, 0x9a, 0x67, 0xa1, 0x1f,
   0x66, 0x4e, 0x66, 0x67, 0xfb, 0x36, 0x96, 0x36, 0x76, 0x9e, 0x53, 0xfa,
   0x9e, 0x90, 0x0a, 0x3d, 0x9f, 0xbd, 0xcd, 0x7b, 0x11, 0x30, 0x54, 0x38,
   0xc5, 0x37, 0x93, 0x70, 0x64, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x4a, 0x36, 0x50, 0xaa, 0xac, 0x41, 0xfb, 0x21, 0xac, 0x53, 0x74, 0xd5,
   0x56, 0x2e, 0x6c, 0x83, 0x69, 0x97, 0x32, 0x61, 0x09, 0x15, 0x85, 0xe9,
   0x5f, 0x41, 0xed, 0x6e, 0x35, 0xb8, 0x59, 0x5b]

/-- The honest tape of `xD0` (Python `tape xD0`). -/
def tapeD0 : Tape :=
  [0x60, 0x04, 0xbd, 0xd3, 0x0c, 0xf0, 0x06, 0xe9, 0x2e, 0xc9, 0x66, 0xda,
   0x6a, 0x25, 0x7f, 0x20, 0xf6, 0xf4, 0x2b, 0xa1, 0xca, 0xdd, 0xb6, 0xec,
   0xfb, 0x16, 0x2e, 0x2f, 0x69, 0x8a, 0x6a, 0xef, 0x5f, 0x73, 0x03, 0x27,
   0x64, 0x6b, 0x46, 0xe2, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x36, 0xe2, 0xe9, 0x20, 0x27, 0x8b, 0x3c, 0x0c, 0x59, 0xfd, 0x9f, 0xa1,
   0x34, 0xc4, 0xa4, 0x10, 0x95, 0x4f, 0x51, 0xc3, 0xa3, 0x66, 0x34, 0x8b,
   0xec, 0x4f, 0xd5, 0x46, 0xa6, 0xbe, 0x98, 0xe9, 0x9a, 0x67, 0xa1, 0x1f,
   0x66, 0x4e, 0x66, 0x67, 0xfb, 0x36, 0x96, 0x36, 0x76, 0x9e, 0x53, 0xfa,
   0x9e, 0x90, 0x0a, 0x3d, 0x9f, 0xbd, 0xcd, 0x7b, 0x11, 0x30, 0x54, 0x38,
   0xc5, 0x37, 0x93, 0x70, 0x64, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x4a, 0x36, 0x50, 0xaa, 0xac, 0x41, 0xfb, 0x21, 0xac, 0x53, 0x74, 0xd5,
   0x56, 0x2e, 0x6c, 0x83, 0x69, 0x97, 0x32, 0x61, 0x09, 0x15, 0x85, 0xe9,
   0x5f, 0x41, 0xed, 0x6e, 0x35, 0xb8, 0x59, 0x5b]

/-- The honest tape of `xD1` (Python `tape xD1`). -/
def tapeD1 : Tape :=
  [0x60, 0x04, 0xbd, 0xd3, 0x0c, 0xf0, 0x06, 0xe9, 0x2e, 0xc9, 0x66, 0xda,
   0x6a, 0x25, 0x7f, 0x20, 0xf6, 0xf4, 0x2b, 0xa1, 0xca, 0xdd, 0xb6, 0xec,
   0xfb, 0x16, 0x2e, 0x2f, 0x69, 0x8a, 0x6a, 0xef, 0x31, 0xaa, 0x69, 0xe4,
   0x8c, 0x74, 0xf8, 0x12, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x5b, 0x1c, 0x35, 0xef, 0xfb, 0x70, 0xfe, 0xff, 0x3a, 0x94, 0x08, 0x61,
   0x28, 0xc4, 0x79, 0x69, 0x4d, 0x71, 0xb1, 0x24, 0xfa, 0x76, 0xd7, 0x28,
   0x6d, 0x52, 0xc1, 0x26, 0xd2, 0xb6, 0xb2, 0xfb, 0x10, 0x17, 0xe4, 0xde,
   0x4a, 0xa2, 0xb9, 0x84, 0x3e, 0x2a, 0xfc, 0xbd, 0xfd, 0x7a, 0x8f, 0x8f,
   0x5b, 0xa9, 0xf7, 0xc5, 0xcb, 0x5c, 0x4b, 0x70, 0x38, 0xe6, 0xa3, 0x0c,
   0xca, 0x2f, 0x47, 0x6f, 0x65, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x74, 0x67, 0x49, 0x3a, 0x66, 0xd2, 0xf9, 0x6a, 0x69, 0x80, 0x27, 0xab,
   0x86, 0x9d, 0xed, 0xce, 0x37, 0x1e, 0x0d, 0x36, 0xd0, 0xae, 0x26, 0x43,
   0x37, 0x1b, 0xaf, 0x3f, 0x69, 0x38, 0x76, 0xda]

/-- The two-leaf node statement `nodeStmt cfg2 vkc2 vkc2 .leaf .leaf x0 x1` (Python `xN`). -/
def xN : Stmt := stmtOfWords
  [0x30e57aba8b674c0f, 0x44e914aea2deaa87, 0xc6685b9444bad2fc, 0xd3569522f6a1b901,
   0x30e57aba8b674c0f, 0x44e914aea2deaa87, 0xc6685b9444bad2fc, 0xd3569522f6a1b901,
   0x951893297ee6c582, 0x7ef6b4092e377de5, 0x7a38863e0759cc79, 0x4ea6ac0ebc11a2f5,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000]

/-- The level-2 statement `nodeStmt cfg2 vkc2 vkc2 .node .leaf xN x0` (Python `xR`;
`d3 = (1, 0, 0, 0)`). -/
def xR : Stmt := stmtOfWords
  [0x30e57aba8b674c0f, 0x44e914aea2deaa87, 0xc6685b9444bad2fc, 0xd3569522f6a1b901,
   0x30e57aba8b674c0f, 0x44e914aea2deaa87, 0xc6685b9444bad2fc, 0xd3569522f6a1b901,
   0x27a305f90bfeca81, 0x28ff2160edc40601, 0xef8036dacb1f33f6, 0x917219e2a42b3911,
   0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000]

/-- The statement tree of depth 2 over `x0, x1, x0, x1`: `nodeStmt cfg2 vkc2 vkc2 .node .node xN
xN` (Python `xT`). -/
def xT : Stmt := stmtOfWords
  [0x30e57aba8b674c0f, 0x44e914aea2deaa87, 0xc6685b9444bad2fc, 0xd3569522f6a1b901,
   0x30e57aba8b674c0f, 0x44e914aea2deaa87, 0xc6685b9444bad2fc, 0xd3569522f6a1b901,
   0x5ce274c0fa10b1fc, 0x8403b5aa0b092ade, 0xa6c6453e15ff1c13, 0x8afda1dd0197ce41,
   0x0000000000000001, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
   0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000]

/-- `xN` with bit 0 of `d0` flipped. -/
def xD0 : Stmt := bump xN 0
/-- `xN` with bit 0 of `d1` flipped. -/
def xD1 : Stmt := bump xN 4

/-- The two-leaf node: children `x0`, `x1` with their honest tapes. -/
def nwN : NodeWitness 1 := ⟨vkc2, vkc2, .leaf, .leaf, x0, x1, tape2, tapeX1⟩
/-- The level-2 node: the node child `xN` and the leaf child `x0`. -/
def nwR : NodeWitness 1 := ⟨vkc2, vkc2, .node, .leaf, xN, x0, tapeXN, tape2⟩
/-- A node child whose `d0` is not the parent's (its tape is accepted). -/
def nwD0 : NodeWitness 1 := ⟨vkc2, vkc2, .node, .leaf, xD0, x0, tapeD0, tape2⟩
/-- A node child whose `d1` is not the parent's (its tape is accepted). -/
def nwD1 : NodeWitness 1 := ⟨vkc2, vkc2, .node, .leaf, xD1, x0, tapeD1, tape2⟩

/-- A node statement presented as a leaf child (S5-m1): the level-2 node with its tags wrong. -/
def nwMis : NodeWitness 1 := ⟨vkc2, vkc2, .leaf, .leaf, xN, x0, tapeXN, tape2⟩

/-! ## A second key (S5-m7): the recursion key and the leaf key differ -/

/-- The honest prover of `cmpToyK`: `cmpToy`'s, answering with key element `0x1235`. -/
def cmpNextK (s : Layout K × Stmt) (_ : List (Table K)) (m : MessageIdx cmpShape)
    (tr : Transcript cmpShape m.1.castSucc) : (cmpShape m.1).Ty :=
  match m, tr with
  | ⟨0, _⟩, _ => (fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩ : OVal ⟨2, 0⟩)
  | ⟨1, h⟩, _ => absurd h (by decide)
  | ⟨2, _⟩, tr =>
    (fun _ => ((tr (1 : Fin 2)).1 ⟨0, by decide⟩).c0 + ⟨0x1235⟩ + s.2 0 : OVal ⟨0, 0⟩)

/-- `cmpToy` with key element `0x1235` and its honest prover: another key, the same index. -/
def cmpToyK : Protocol 20 :=
  { cmpToy with VK := fun _ _ => ⟨0x1235⟩, prover := ⟨cmpNextK, fun _ _ _ => ((), ())⟩ }

/-- The second key: `index cfg2 cmpToyK L0` (`#guard`), element `0x1235`, `vkc2`'s root. -/
def vkK : VKc 1 := (fun _ => ⟨0x1235⟩, vkc2.2)

/-- The honest tape of `x0` under `vkK` (`prove cfg2 cmpToyK L0 x0 []`; Python `tape K x0`). -/
def tapeK : Tape :=
  [0x60, 0x04, 0xbd, 0xd3, 0x0c, 0xf0, 0x06, 0xe9, 0x2e, 0xc9, 0x66, 0xda,
   0x6a, 0x25, 0x7f, 0x20, 0xf6, 0xf4, 0x2b, 0xa1, 0xca, 0xdd, 0xb6, 0xec,
   0xfb, 0x16, 0x2e, 0x2f, 0x69, 0x8a, 0x6a, 0xef, 0x3e, 0x8b, 0x37, 0xec,
   0x4f, 0x55, 0xeb, 0xd0, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0xf4, 0xd4, 0x61, 0xfe, 0x07, 0x72, 0x65, 0xe6, 0xad, 0x1f, 0x59, 0xde,
   0x4b, 0x3c, 0xfd, 0xf7, 0xb5, 0xcd, 0x68, 0xda, 0xc6, 0xfb, 0x07, 0xa4,
   0xcc, 0xc5, 0x0d, 0x26, 0xb9, 0xe0, 0x3a, 0x07, 0x9a, 0x67, 0xa1, 0x1f,
   0x66, 0x4e, 0x66, 0x67, 0xfb, 0x36, 0x96, 0x36, 0x76, 0x9e, 0x53, 0xfa,
   0x9e, 0x90, 0x0a, 0x3d, 0x9f, 0xbd, 0xcd, 0x7b, 0x11, 0x30, 0x54, 0x38,
   0xc5, 0x37, 0x93, 0x70, 0x65, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x74, 0x67, 0x49, 0x3a, 0x66, 0xd2, 0xf9, 0x6a, 0x69, 0x80, 0x27, 0xab,
   0x86, 0x9d, 0xed, 0xce, 0x37, 0x1e, 0x0d, 0x36, 0xd0, 0xae, 0x26, 0x43,
   0x37, 0x1b, 0xaf, 0x3f, 0x69, 0x38, 0x76, 0xda]

/-- Distinct keys, leaf children proved under the leaf key `vkK`: accepted. -/
def nwK : NodeWitness 1 := ⟨vkc2, vkK, .leaf, .leaf, x0, x0, tapeK, tapeK⟩
/-- Distinct keys, leaf children proved under the recursion key `vkc2` only: rejected. -/
def nwKC : NodeWitness 1 := ⟨vkc2, vkK, .leaf, .leaf, x0, x0, tape2, tape2⟩

/-- The key `vkc2` with a 33-byte root. -/
def vkC33 : VKc 1 := (vkc2.1, vkc2.2 ++ [0])
/-- The two-leaf node with the recursion key `vkC33` (its children are fine). -/
def nw33 : NodeWitness 1 := ⟨vkC33, vkc2, .leaf, .leaf, x0, x1, tape2, tapeX1⟩

/-! ## A layout that ignores `π₂` (the unsatisfiable one is `Controls/Layout.lean`'s `unsat`) -/

/-- `Cbad`: one chip, the public one, of 51 columns (the statement, then 19 cells for the second
child's proof) and no constraint at all. -/
def Cbad : Layout K := ⟨[⟨51, freeGadget _, [], none⟩], fun _ => .eq, 0⟩

/-- `Cbad`'s decoder: the two-leaf node `nwN`, except that `π₂` is read from cells `32 … 50` of
row 0 (8 bytes each). It stands for a circuit that checks everything but the second child's
proof, whose cells it leaves unconstrained. -/
def decodeBad (w : List (Table K)) : NodeWitness 1 :=
  ⟨vkc2, vkc2, .leaf, .leaf, x0, x1, tape2,
    (List.ofFn fun i : Fin 19 => (w.headD ⟨0, fun _ _ => 0⟩).cell 0 (32 + i)).flatMap K.bytes⟩

/-- A one-row witness of `Cbad`: the statement `x'`, then the cells `cs`. -/
def wOf (x' : Stmt) (cs : List K) : List (Table K) :=
  [⟨1, fun _ c => if h : c < 32 then x' ⟨c, h⟩ else cs.getD (c - 32) 0⟩]

/-- `π₂` in the cells is the honest `tapeX1`. -/
def wGood : List (Table K) := wOf xN (kList tapeX1)
/-- `π₂` in the cells is 152 zero bytes. -/
def wBad : List (Table K) := wOf xN []

/-! ## Known answers needing no hash evaluation -/

/-- The key's index root has 32 bytes. -/
theorem vkc2_root : vkc2.2.length = 32 := rfl

/-- Known answer for `digestToSlot`: the key digest `D vkc2` (`digest_kat`; Python
`hashlib.blake2s(le64(0x1234) ‖ root)`) as four little-endian limbs (Python `struct '<4Q'`). -/
theorem digestToSlot_kat : digestToSlot (vkc2.digest cfg2) = fun j =>
    ⟨[0x30e57aba8b674c0f, 0x44e914aea2deaa87, 0xc6685b9444bad2fc, 0xd3569522f6a1b901].getD j 0⟩ :=
    by
  rw [digest_kat]; decide +kernel

/-! ## Evaluated cross-checks (compiled code; the kernel checks are in the two control files) -/

-- The tapes are the Python reference's (`logs/S5/python-ref.log`) and the honest prover's.
#guard tapeX1 = hex ("6004bdd30cf006e92ec966da6a257f20f6f42ba1caddb6ecfb162e2f698a6aef" ++
  "0d488a48cf4f35a70a000000000000005b1c35effb70feff3a94086128c47969" ++
  "4d71b124fa76d7286d52c126d2b6b2fb1017e4de4aa2b9843e2afcbdfd7a8f8f" ++
  "5ba9f7c5cb5c4b7038e6a30cca2f476f65000000000000007467493a66d2f96a" ++
  "698027ab869dedce371e0d36d0ae2643371baf3f693876da")
#guard tapeXN = hex ("6004bdd30cf006e92ec966da6a257f20f6f42ba1caddb6ecfb162e2f698a6aef" ++
  "fbc95885ef8bed20070000000000000036e2e920278b3c0c59fd9fa134c4a410" ++
  "954f51c3a366348bec4fd546a6be98e99a67a11f664e6667fb369636769e53fa" ++
  "9e900a3d9fbdcd7b11305438c537937064000000000000004a3650aaac41fb21" ++
  "ac5374d5562e6c8369973261091585e95f41ed6e35b8595b")
#guard tapeD0 = hex ("6004bdd30cf006e92ec966da6a257f20f6f42ba1caddb6ecfb162e2f698a6aef" ++
  "5f730327646b46e2070000000000000036e2e920278b3c0c59fd9fa134c4a410" ++
  "954f51c3a366348bec4fd546a6be98e99a67a11f664e6667fb369636769e53fa" ++
  "9e900a3d9fbdcd7b11305438c537937064000000000000004a3650aaac41fb21" ++
  "ac5374d5562e6c8369973261091585e95f41ed6e35b8595b")
#guard tapeD1 = hex ("6004bdd30cf006e92ec966da6a257f20f6f42ba1caddb6ecfb162e2f698a6aef" ++
  "31aa69e48c74f8120a000000000000005b1c35effb70feff3a94086128c47969" ++
  "4d71b124fa76d7286d52c126d2b6b2fb1017e4de4aa2b9843e2afcbdfd7a8f8f" ++
  "5ba9f7c5cb5c4b7038e6a30cca2f476f65000000000000007467493a66d2f96a" ++
  "698027ab869dedce371e0d36d0ae2643371baf3f693876da")
#guard prove cfg2 cmpToy L0 x1 [] = some tapeX1
#guard prove cfg2 cmpToy L0 xN [] = some tapeXN
#guard prove cfg2 cmpToy L0 xD0 [] = some tapeD0
#guard prove cfg2 cmpToy L0 xD1 [] = some tapeD1
-- The aggregate statements are the Python reference's `xN`, `xR`.
#guard nodeStmt cfg2 vkc2 vkc2 .leaf .leaf x0 x1 = xN
#guard nodeStmt cfg2 vkc2 vkc2 .node .leaf xN x0 = xR
#guard treeRoot cfg2 vkc2 vkc2 2 [x0, x1, x0, x1] = some xT
-- The second key and its tape.
#guard (index cfg2 cmpToyK L0).2 == vkK.2 && cmpToyK.VK L0 ⟨0, by decide⟩ == vkK.1 0
#guard tapeK = hex ("6004bdd30cf006e92ec966da6a257f20f6f42ba1caddb6ecfb162e2f698a6aef" ++
  "3e8b37ec4f55ebd00800000000000000f4d461fe077265e6ad1f59de4b3cfdf7" ++
  "b5cd68dac6fb07a4ccc50d26b9e03a079a67a11f664e6667fb369636769e53fa" ++
  "9e900a3d9fbdcd7b11305438c537937065000000000000007467493a66d2f96a" ++
  "698027ab869dedce371e0d36d0ae2643371baf3f693876da")
#guard prove cfg2 cmpToyK L0 x0 [] = some tapeK
#guard NARG cfg2 cmpToy vkK x0 tapeK && !(NARG cfg2 cmpToy vkK x0 tape2) &&
  !(NARG cfg2 cmpToy vkc2 x0 tapeK)
-- `nwD0`, `nwD1`: the child's own proof is accepted, so only the key check can reject them.
#guard NARG cfg2 cmpToy vkc2 xD0 tapeD0 && NARG cfg2 cmpToy vkc2 xD1 tapeD1
#guard (xD0.slot 1 == xN.slot 1, xD1.slot 0 == xN.slot 0) == (true, true)
-- All the positives and negatives of the kernel files, evaluated.
#guard aggOK cfg2 cmpToy xN nwN && aggOK cfg2 cmpToy xR nwR
#guard !(aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkc2 .node .leaf xD0 x0) nwD0) &&
  !(aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkc2 .node .leaf xD1 x0) nwD1)
#guard !(aggOK cfg2 cmpToy xR nwMis)
#guard aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkK .leaf .leaf x0 x0) nwK &&
  !(aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkK .leaf .leaf x0 x0) nwKC)
#guard !(aggOK cfg2 cmpToy (nodeStmt cfg2 vkC33 vkc2 .leaf .leaf x0 x1) nw33)
#guard aggOK cfg2 cmpToy xN (decodeBad wGood) && !(aggOK cfg2 cmpToy xN (decodeBad wBad))

end RecursionFast.Controls.Recursion

/-
# Contract: the extractor's machine, a step-counting word language                (TRUSTED)

The user's decision of 2026-10-20 (handoff §2.5, issue #7; ledger V3-S2R-A1) replaces the RISC-V
image and the vendored Rv64 model. The extractor is a **program of this machine**: a statement
tree over 64-bit words, given as data. Its meaning is the interpreter `XStmt.exec` below, which
consumes one unit of fuel for every statement it executes, so a proved fuel bound is a proved step
bound (`Extractor.lean`).

**Why the shape is what it is (the review `V3-S2R-handoff-review.md`).**
* **Deep, not shallow (H-M1).** The syntax has no function-typed field. A program cannot run Lean
  code of its own: the only computation a program causes is the interpreter's, one statement per
  step. (A monad whose bind takes a Lean continuation would let that continuation compute for
  free.)
* **Three-address code (H-M2).** An operation reads two memory cells and writes one, a branch or a
  loop tests one cell, and no statement contains a sub-expression. Each step is a bounded amount
  of word-RAM work: one `XOp` (one instruction on the reference machine; `clmul`/`clmulh` are
  `pclmulqdq` or Zbc, V3-1), one memory or input access, one output word, or one push or pop of the
  statement stack.
* **Memory is charged (H-m5).** A program declares `mem` zero-initialised words, and `run` charges
  one step per word before the first statement.

**State.** The memory `M` is an array of `mem` words, named by indices. A read outside it is `0`
and a write outside it is lost. The input tape `I` is read-only (a read past its end is `0`). The
output is a list of words, appended to. A stack holds the statements still to run. The run halts
when the stack is empty, and returns the output.

`clmul` (the carry-less product, v2's Zbc semantics) is unchanged from the RISC-V machine. `Word`
was the vendored model's notation for `BitVec 64` and is defined here.
-/

namespace RecursionFast

/-- A 64-bit machine word. -/
abbrev Word := BitVec 64

/-- Carry-less product of two words (polynomials of degree `< 64` over GF(2)) as a 128-bit word
(schoolbook shift-and-xor). -/
def clmul (a b : Word) : BitVec 128 :=
  Fin.foldl 64
    (fun acc i => if a.getLsbD i then acc ^^^ (b.zeroExtend 128 <<< (i : Nat)) else acc) 0

/-- The word operations of the machine; each is one instruction of the reference machine. -/
inductive XOp where
  | add | sub | mul | mulhu | divu | remu | and | or | xor | shl | shr | ltu | eq | clmul | clmulh

/-- What an operation computes: arithmetic modulo `2^64`, `mulhu` the high word of the product,
`x / 0 = 0` and `x % 0 = x`, shifts by the low 6 bits of `b`, `ltu`/`eq` as `1` or `0`, and the
low and high words of the carry-less product. -/
def XOp.eval : XOp → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .mulhu, a, b => ((a.zeroExtend 128 * b.zeroExtend 128) >>> 64).setWidth 64
  | .divu, a, b => a / b
  | .remu, a, b => a % b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< (b.toNat % 64)
  | .shr, a, b => a >>> (b.toNat % 64)
  | .ltu, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0
  | .clmul, a, b => (RecursionFast.clmul a b).setWidth 64
  | .clmulh, a, b => (RecursionFast.clmul a b >>> 64).setWidth 64

/-- A statement of the machine (three-address code; `M[i]` is memory cell `i`). -/
inductive XStmt where
  /-- `M[d] := M[a] ∘ M[b]`. -/
  | op (o : XOp) (d a b : Nat)
  /-- `M[d] := w`. -/
  | const (d : Nat) (w : Word)
  /-- `M[d] := M[M[a]]`. -/
  | load (d a : Nat)
  /-- `M[M[a]] := M[s]`. -/
  | store (a s : Nat)
  /-- `M[d] :=` input word `M[a]`. -/
  | input (d a : Nat)
  /-- Append `M[s]` to the output. -/
  | out (s : Nat)
  /-- `p`, then `q`. -/
  | seq (p q : XStmt)
  /-- `p` if `M[c] ≠ 0`, else `q`. -/
  | ite (c : Nat) (p q : XStmt)
  /-- `p` while `M[c] ≠ 0`. -/
  | loop (c : Nat) (p : XStmt)

/-- The number of statements in `p`. -/
def XStmt.size : XStmt → Nat
  | .seq p q | .ite _ p q => p.size + q.size + 1
  | .loop _ p => p.size + 1
  | _ => 1

/-- An extractor program: `mem` zero-initialised memory words and the statement to run. -/
structure XProg where
  /-- The number of memory words. -/
  mem : Nat
  /-- The statement. -/
  body : XStmt

/-- Run the statement stack `ks` (top first) on input `I`, memory `M` and output `o` for at most
`n` statements: the output once the stack is empty, `none` if the fuel runs out first. -/
def XStmt.exec (I : Array Word) : Nat → Array Word → Array Word → List XStmt → Option (List Word)
  | _, _, o, [] => some o.toList
  | 0, _, _, _ :: _ => none
  | n + 1, M, o, s :: ks =>
    match s with
    | .op f d a b => exec I n (M.setIfInBounds d (f.eval (M.getD a 0) (M.getD b 0))) o ks
    | .const d w => exec I n (M.setIfInBounds d w) o ks
    | .load d a => exec I n (M.setIfInBounds d (M.getD (M.getD a 0).toNat 0)) o ks
    | .store a v => exec I n (M.setIfInBounds (M.getD a 0).toNat (M.getD v 0)) o ks
    | .input d a => exec I n (M.setIfInBounds d (I.getD (M.getD a 0).toNat 0)) o ks
    | .out v => exec I n M (o.push (M.getD v 0)) ks
    | .seq p q => exec I n M o (p :: q :: ks)
    | .ite c p q => exec I n M o ((if M.getD c 0 = 0 then q else p) :: ks)
    | .loop c p => exec I n M o (if M.getD c 0 = 0 then ks else p :: .loop c p :: ks)

/-- **The machine**: run `p` on the input tape for at most `fuel` steps, one per memory word and
one per statement executed; the output words, or `none` if the fuel runs out. -/
def XProg.run (p : XProg) (input : List Word) (fuel : Nat) : Option (List Word) :=
  if p.mem ≤ fuel then
    XStmt.exec input.toArray (fuel - p.mem) (Array.replicate p.mem 0) #[] [p.body]
  else none

end RecursionFast

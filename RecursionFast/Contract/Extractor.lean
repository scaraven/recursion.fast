/-
# Contract: the extractor program and its step bound                              (TRUSTED)

DESIGN-v3 §4.4, amended by V3-S2R-A1 (the user's decision of 2026-10-20, handoff §2.5, #7).
Knowledge means an extractor that is efficient. A submission names a program `ext` of the
contract's step-counting machine (`Machine.lean`) and proves that it computes its extractor
specification `E` on every input within a declared step budget `fuel t`, `t` the input tape's
length in words, and itself at most `B t = 2^48 + 2^16 · t` (`Certificate.lean`). The fuel is the
interpreter's: one unit per memory word and one per statement executed, so the bound is a theorem,
not a measurement.

**Input tape (normative, V3-S1-A7).** `extractorInput c π L` is a list of 64-bit words:
* the statement `c`: 4 words;
* the proof `π`: one word `|π|` (bytes), then `⌈|π|/8⌉` words of packed bytes;
* one word `|L|` (entries), then for each entry `(q, a)` in log order: one word `|q|` (bytes),
  `⌈|q|/8⌉` words of packed bytes, and the answer `a` in 4 words.
Bytes are **packed** eight per word, little-endian (byte `8j + i` is bits `8i … 8i + 7` of word
`j`), the last word zero-padded; a number is its low 64 bits. Every field starts on a word.
`packBytes`, `wordByte` and `bytesAt` are specifications: their compiled code is quadratic, and
`Library/Words.lean` has linear twins proved equal (#10).

**Output (normative, V3-S1-A7, A22).** The program's output words **denote** a witness through the
contract's total decoder `decodeWit`: word 0 is a tag, `0` a leaf (start in words 1–4, length in
word 5), `1` a node (child digests in words 1–4 and 5–8, then each child proof as on the input
tape: length word, packed bytes). The empty output, any other tag, and a child length above
`proofCap` denote `none`; missing words read as `0` and words past the fields are ignored. The
certificate requires the denoted witness to be `E`'s result, not the words to be one canonical
encoding.

**Domain (V3-S1-A11, V3-S2R-H-m3).** Every statement, every proof of at most `proofCap` bytes and
every log whose tape the machine can address: at most `2^64` words, since the input is read at a
64-bit address. A log entry takes at least five words, so efficient extraction is claimed for logs
of up to about `2^61` entries; `KS` itself covers logs up to `logCap`. The output has at most
`outCap = 2^24` words (a witness of the relation needs at most `11 + 2 · 2^17`), and the program
has at most `progCap = 2^20` statements.

**Budget (V3-S2R-A1, O-21).** `B t` charges `2^16` steps per input word and a fixed `2^48`. The
fixed term covers a quasi-linear Reed–Solomon decoder of the word a node extractor must decode
(about `2^29` symbols, `2^38.7` field operations at about `2^4` statements each, F1 §3.3), with
`2^5` to spare. The linear term covers indexing the log by sorting it (`t · log t` comparisons of
4-word digests). Within the domain `B t ≤ 2^80`, so enumerating `2^128` candidates is excluded; the
relation has no shorter secret.
-/
import RecursionFast.Contract.Machine
import RecursionFast.Contract.Oracle

namespace RecursionFast

/-- A number as a word: its low 64 bits. -/
def toWord (a : ℕ) : Word := BitVec.ofNat 64 a

/-- The number with the little-endian base-256 digits `ds`. -/
def ofLE (ds : List UInt8) : ℕ := ds.foldr (fun d a => d.toNat + 256 * a) 0

/-- Bytes packed into words: word `j` is the little-endian number of bytes `8j … 8j + 7`, the last
word zero-padded. -/
def packBytes (b : List UInt8) : List Word :=
  (List.range ((b.length + 7) / 8)).map fun j => toWord (ofLE ((b.drop (8 * j)).take 8))

/-- A byte string on the tape: its length in bytes, then its bytes packed. -/
def bytesWords (b : List UInt8) : List Word := toWord b.length :: packBytes b

/-- **The extractor's input tape** `⟦c, |π|, π, |L|, L⟧`: the statement (4 words), the proof
(length-prefixed), the number of log entries, then each entry's query (length-prefixed) and
answer (4 words). -/
def extractorInput (c : Digest) (π : Proof) (L : Log) : List Word :=
  packBytes c.toList ++ bytesWords π.data.toList ++ toWord L.length ::
    L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList

/-- Byte `i` of words read as packed bytes; `0` beyond their end. -/
def wordByte (ws : List Word) (i : ℕ) : UInt8 :=
  ((ws.getD (i / 8) 0).toNat / 256 ^ (i % 8)).toUInt8

/-- The digest packed in words `k … k + 3` of `o`. -/
def digestAt (o : List Word) (k : ℕ) : Digest := Vector.ofFn fun i => wordByte (o.drop k) i

/-- The `n` bytes packed from word `k` of `o` on. -/
def bytesAt (o : List Word) (k n : ℕ) : Proof :=
  ⟨((List.range n).map (wordByte (o.drop k))).toArray⟩

/-- **The witness an extractor output denotes**: tag `0` a leaf (start, length), tag `1` a node
(two digests, two length-prefixed proofs of at most `proofCap` bytes), as in the module header;
missing words read as `0`; `none` for the empty output, any other tag and a longer child. -/
def decodeWit : List Word → Option Wit
  | [] => none
  | o@(t :: _) =>
    let w (k : ℕ) := (o.getD k 0).toNat
    let m := (w 9 + 7) / 8
    if t = 0 then some (.leaf (digestAt o 1) (w 5))
    else if t = 1 ∧ w 9 ≤ proofCap ∧ w (10 + m) ≤ proofCap then
      some (.node (digestAt o 1) (digestAt o 5) (bytesAt o 10 (w 9))
        (bytesAt o (11 + m) (w (10 + m))))
    else none

/-- The extractor budget `B t = 2^48 + 2^16 · t` steps, for an input tape of `t` words. -/
def extractorBudget (t : ℕ) : ℕ := 2 ^ 48 + 2 ^ 16 * t

/-- The longest extractor output: `2^24` words. -/
def outCap : ℕ := 2 ^ 24

/-- The largest extractor program: `2^20` statements. -/
def progCap : ℕ := 2 ^ 20

/-- **The program computes the extractor `E` within `fuel`**: on every statement, every proof of
at most `proofCap` bytes and every log whose tape has at most `2^64` words, the program halts
within `fuel t` steps, `t` the tape's length, with at most `outCap` words, and they denote `E`'s
result. -/
def Computes (p : XProg) (E : Digest → Proof → Log → Option Wit) (fuel : ℕ → ℕ) : Prop :=
  ∀ c (π : Proof) (L : Log), π.size ≤ proofCap → (extractorInput c π L).length ≤ 2 ^ 64 →
    ∃ o, p.run (extractorInput c π L) (fuel (extractorInput c π L).length) = some o ∧
      o.length ≤ outCap ∧ decodeWit o = E c π L

end RecursionFast

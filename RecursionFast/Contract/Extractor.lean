/-
# Contract: the extractor image (decision Q1)                                      (TRUSTED)

DESIGN-v3 §4.4. Knowledge means an executable extractor with a budget: a submission names a
RISC-V image (`Machine.lean`) and proves that it computes its extractor specification `E` on
every input within a declared step budget `fuel t`, `t` the input tape's length in words, itself
at most `B t = 2^40 + 2^8 · t` (`Certificate.lean`). The machine and the image are v2's; the tape
and output formats below are new (bytes, not field elements).

**Input tape (normative, V3-S1-A7).** `extractorInput c π L` is a list of 64-bit words:
* the statement `c`: 4 words;
* the proof `π`: one word `|π|` (bytes), then `⌈|π|/8⌉` words of packed bytes;
* one word `|L|` (entries), then for each entry `(q, a)` in log order: one word `|q|` (bytes),
  `⌈|q|/8⌉` words of packed bytes, and the answer `a` in 4 words.
Bytes are **packed** eight per word, little-endian (byte `8j + i` is bits `8i … 8i + 7` of word
`j`), the last word zero-padded; a number is its low 64 bits. Every field starts on a word.

**Output (normative, V3-S1-A7, A22).** The image's output words **denote** a witness through the
contract's total decoder `decodeWit`: word 0 is a tag, `0` a leaf (start in words 1–4, length in
word 5), `1` a node (child digests in words 1–4 and 5–8, then each child proof as on the input
tape: length word, packed bytes). The empty output, any other tag, and a child length above
`proofCap` denote `none`; missing words read as `0` and words past the fields are ignored. The
certificate requires the denoted witness to be `E`'s result, not the words to be one canonical
encoding. This leniency is what lets the witness-sending extractor (DESIGN-v3 §7.3) output its
proof's words in place, in a constant number of steps, whatever the proof: a malformed proof
denotes exactly what its words denote, which is what that extractor's specification returns.

**Domain (V3-S1-A11, A21).** Every statement, every proof of at most `proofCap` bytes and every
log whose input tape the machine can address (`2^60` words; no image could read a longer one).
No bound on the number of log entries. The output has at most `outCap = 2^24` words, a cap on the
image (a witness of the relation needs at most `11 + 2 · 2^17` words); the image has at most
`imageCap` bytes.

**Budget (V3-S1-A21, O-21).** `B t` charges `2^8` steps per input word and a fixed `2^40`: a
straight-line extractor reads the proof, indexes the log (by answer, or by query, both within
`2^8` steps per word) and rebuilds the openings it needs; `2^40` covers a quasi-linear decoder of
a `2^20`-byte proof with a large constant, and excludes enumerating `2^128` candidates. A log of
long entries brings its own budget.
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

/-- The extractor budget `B t = 2^40 + 2^8 · t` steps, for an input tape of `t` words. -/
def extractorBudget (t : ℕ) : ℕ := 2 ^ 40 + 2 ^ 8 * t

/-- The longest extractor output: `2^24` words. -/
def outCap : ℕ := 2 ^ 24

/-- The largest extractor image: `2^20` bytes. -/
def imageCap : ℕ := 2 ^ 20

/-- **The image computes the extractor `E` within `fuel`**: on every statement, every proof of at
most `proofCap` bytes and every log whose tape the machine can address, the machine halts on
`img` within `fuel t` steps, `t` the tape's length, with at most `outCap` words, and they denote
`E`'s result. -/
def ImageComputes (img : Image) (E : Digest → Proof → Log → Option Wit) (fuel : ℕ → ℕ) : Prop :=
  ∀ c (π : Proof) (L : Log), π.size ≤ proofCap → (extractorInput c π L).length ≤ 2 ^ 60 →
    ∃ o, run img (extractorInput c π L) (fuel (extractorInput c π L).length) = some o ∧
      o.length ≤ outCap ∧ decodeWit o = E c π L

end RecursionFast

/-
# Contract: the extractor program and its step bound                              (TRUSTED)

DESIGN-v3 §4.4, amended by V3-S2R-A1 (the user's decision of 2026-10-20, handoff §2.5, #7); v4
changes only the output format, for witnesses with signed children (V4-6). Knowledge means an
extractor that is efficient. A submission names a program `ext` of the contract's step-counting
machine (`Machine.lean`) and proves that it computes its extractor specification `E` on every
input within a declared step budget `fuel t`, `t` the input tape's length in words, and itself at
most `B t = 2^48 + 2^16 · t` (`Certificate.lean`). The fuel is the interpreter's: one unit per
memory word and one per statement executed, so the bound is a theorem, not a measurement. The
extractor takes no public key (V4-6): a node extractor reads its children from the node proof.

**Input tape (normative, V3-S1-A7; unchanged in v4).** `extractorInput c π L` is a list of 64-bit
words: the statement `c` (4 words); the proof `π`: one word `|π|` (bytes), then `⌈|π|/8⌉` words of
packed bytes; then the log (`logWords`): one word `|L|` (entries), then for each entry `(q, a)` in
log order one word `|q|` (bytes), `⌈|q|/8⌉` words of packed bytes, and the answer `a` in 4 words.
Bytes are **packed** eight per word, little-endian (byte `8j + i` is bits `8i … 8i + 7` of word
`j`), the last word zero-padded; a number is its low 64 bits. Every field starts on a word.
`packBytes` is a specification: its compiled code is quadratic, and `Library/Words.lean` has a
linear twin proved equal (#10).

**Output (normative; V3-S1-A7, A22, extended in v4).** The output words **denote** a witness
through the decoder `decodeWit`, which reads fields in order from the front of the output:
* the tag (1 word): `0` a leaf, then its start (4 words) and length (1 word); `1` a node, then
  the two child digests (4 words each) and the two children's signed proofs, each as
  * the proof: a length word, then its packed bytes;
  * the trace, written exactly as a log on the input tape (`logWords`);
  * the signature: the index (1 word), then the `wotsLen = 133` chain values and the
    `sigHeight = 16` path digests (4 words each; a valid signature has exactly these counts).
* Bytes are packed as on the tape, a number is its word, a digest is 32 packed bytes.
The output denotes `none` if its tag is neither `0` nor `1` or if a field runs past its end;
words after the last field are ignored. The certificate requires the denoted witness to be `E`'s
result, not the words to be one canonical encoding.

*Change from v3.* v3 read missing words as `0` and capped the two declared proof lengths, so that
a short output could not declare a `2^63`-byte proof (V3-S1 review m5). With nested
variable-length fields (traces of queries) every declared length would need such a cap; v4 reads
**strictly** instead: a field that runs past the end denotes nothing, so everything decoded is
bounded by the output's length, and the decoder runs in time linear in it (C9; compiled, `take`,
`drop` and `flatMap` are linear).

**Domain (V3-S1-A11, V3-S2R-H-m3, A9).** Every statement, every proof of at most `proofCap`
bytes and every log whose queries have fewer than `2^64` bytes each and whose tape the machine can
address: at most `2^64` words, since the input is read at a 64-bit address. A length word is the
number's low 64 bits, so a query of `2^64` bytes or more would make the tape ambiguous (two logs
with different answers, one tape). A log entry takes at least five words, so efficient extraction
is claimed for logs of up to about `2^61` entries; `KS` itself covers logs up to `logCap`. The
program has at most `progCap = 2^20` statements.

**Output cap (recomputed for v4).** `outCap = 2^24` words. A leaf witness takes 6 words; a node
witness `9 + Σ` over its two children of `(1 + ⌈|π|/8⌉) + (1 + Σ_entries (5 + ⌈|q|/8⌉)) + 597`.
With both proofs at `proofCap` (`2^17` words each), `2^24 − 263,351` words remain for the two
traces: for example `2^16` queries per child (the cap on `qV`) of up to 960 bytes each. A trace is
exactly the verifier's queries (`runSeq`, V4-A3), so this bounds what a node extractor must output
for a verifier whose queries are that short. A node whose children's traces do not fit cannot be
extracted, so its verifier is not certifiable (C-m11), which is the intended outcome.

**Budget (V3-S2R-A1, A8, O-21).** `B t` charges `2^16` steps per input word and a fixed
`2^48`. The fixed term covers a quasi-linear Reed–Solomon decoder of the word a node extractor must
decode (about `2^29` symbols, `2^38.7` field operations at about `2^4` statements each, F1 §3.3),
with `2^5` to spare. The linear term covers indexing the log: copy each entry's answer and tape
position into memory and merge-sort them by answer in a scratch of the same size (`memPerWord = 2`,
`Machine.lean`), `t · log t ≤ 64 · t` comparisons of 4-word digests at about `2^5` statements each,
so about `2^11` steps per word; a lookup is then a binary search. The decoded word's symbols are
read from the log, so the decoder's memory is also proportional to `t`. One scan of the log for
an answer is a kernel-checked control within `16 · t` steps (`Controls/LogScan.lean`). Within the
domain `B t < 2^81`, so enumerating `2^128` candidates is excluded; the relation has no shorter
secret.
-/
import RecursionFast.Contract.Machine
import RecursionFast.Contract.Oracle
import RecursionFast.Contract.Signature

namespace RecursionFast

/-! ## The input tape -/

/-- A number as a word: its low 64 bits. -/
def toWord (a : ℕ) : Word := BitVec.ofNat 64 a

/-- The number with the little-endian base-256 digits `ds`. -/
def ofLE (ds : List UInt8) : ℕ := ds.foldr (fun d a => d.toNat + 256 * a) 0

/-- Bytes packed into words: word `j` is the little-endian number of bytes `8j … 8j + 7`, the last
word zero-padded. -/
def packBytes (b : List UInt8) : List Word :=
  (List.range ((b.length + 7) / 8)).map fun j => toWord (ofLE ((b.drop (8 * j)).take 8))

/-- A byte string in words: its length in bytes, then its bytes packed. -/
def bytesWords (b : List UInt8) : List Word := toWord b.length :: packBytes b

/-- A log (or a trace) in words: the number of entries, then each entry's query (length-prefixed)
and answer (4 words). -/
def logWords (L : Log) : List Word :=
  toWord L.length :: L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList

/-- **The extractor's input tape** `⟦c, |π|, π, |L|, L⟧`: the statement (4 words), the proof
(length-prefixed), then the log. -/
def extractorInput (c : Digest) (π : Proof) (L : Log) : List Word :=
  packBytes c.toList ++ bytesWords π.data.toList ++ logWords L

/-! ## The output -/

/-- A reader of output words: it reads a value from the front and leaves the rest, or fails
(`none`) when a field runs past the end. -/
abbrev Reader := StateT (List Word) Option

/-- A number: one word. -/
def readNat : Reader ℕ := fun o =>
  match o with
  | w :: o => some (w.toNat, o)
  | [] => none

/-- The 8 bytes of a word, little-endian. -/
def wordBytes (w : Word) : List UInt8 :=
  List.ofFn fun i : Fin 8 => (w.toNat / 256 ^ i.val).toUInt8

/-- `n` bytes, packed eight per word in the next `⌈n/8⌉` words. -/
def readBytes (n : ℕ) : Reader (List UInt8) := fun o =>
  let ws := o.take ((n + 7) / 8)
  if ws.length = (n + 7) / 8 then some ((ws.flatMap wordBytes).take n, o.drop ((n + 7) / 8))
  else none

/-- A byte string: its length (one word), then its bytes. -/
def readString : Reader ByteArray := do return ⟨(← readBytes (← readNat)).toArray⟩

/-- A digest: 32 bytes in 4 words. -/
def readDigest : Reader Digest := do
  let b ← readBytes 32
  return Vector.ofFn fun i => b.getD i 0

/-- `n` values, read in turn. -/
def readList {α : Type} (r : Reader α) : ℕ → Reader (List α)
  | 0 => return []
  | n + 1 => return (← r) :: (← readList r n)

/-- A trace or log entry: the query (a byte string), then the answer (a digest). -/
def readEntry : Reader (ByteArray × Digest) := do return (← readString, ← readDigest)

/-- A trace, as `logWords` writes it: the number of entries, then the entries. -/
def readTrace : Reader Trace := do readList readEntry (← readNat)

/-- A signature: the index, then `wotsLen` chain values and `sigHeight` path digests. -/
def readSig : Reader Sig := do
  return ⟨← readNat, ← readList readDigest wotsLen, ← readList readDigest sigHeight⟩

/-- A signed proof: the proof (a byte string), its trace, its signature. -/
def readSigned : Reader Signed := do return ⟨← readString, ← readTrace, ← readSig⟩

/-- A witness: tag `0` and a leaf's start and length, or tag `1` and a node's two child digests
and two signed proofs. -/
def readWit : Reader Wit := do
  match ← readNat with
  | 0 => return .leaf (← readDigest) (← readNat)
  | 1 => return .node (← readDigest) (← readDigest) (← readSigned) (← readSigned)
  | _ => failure

/-- **The witness an extractor output denotes**, read strictly from its front (module header);
`none` for another tag or a field that runs past the end. -/
def decodeWit (o : List Word) : Option Wit := readWit.run' o

/-! ## Budget and the computation claim -/

/-- The extractor budget `B t = 2^48 + 2^16 · t` steps, for an input tape of `t` words. -/
def extractorBudget (t : ℕ) : ℕ := 2 ^ 48 + 2 ^ 16 * t

/-- The longest extractor output: `2^24` words. -/
def outCap : ℕ := 2 ^ 24

/-- The largest extractor program: `2^20` statements. -/
def progCap : ℕ := 2 ^ 20

/-- **The program computes the extractor `E` within `fuel`**: on every statement, every proof of
at most `proofCap` bytes and every log of queries under `2^64` bytes whose tape has at most `2^64`
words, the program halts within `fuel t` steps, `t` the tape's length, with at most `outCap`
words, and they denote `E`'s result. -/
def Computes (p : XProg) (E : Digest → Proof → Log → Option Wit) (fuel : ℕ → ℕ) : Prop :=
  ∀ c (π : Proof) (L : Log), π.size ≤ proofCap → (∀ e ∈ L, e.1.size < 2 ^ 64) →
    (extractorInput c π L).length ≤ 2 ^ 64 →
    ∃ o, p.run (extractorInput c π L) (fuel (extractorInput c π L).length) = some o ∧
      o.length ≤ outCap ∧ decodeWit o = E c π L

end RecursionFast

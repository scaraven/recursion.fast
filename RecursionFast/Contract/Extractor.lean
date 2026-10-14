/-
# Contract: the bounded extractor (decision Q1)                                  (TRUSTED)

DESIGN §4 item 3, O-1, decision Q1 ("the extractor is the program"). A submission names a
RISC-V image (`ExtractorImage`), and its round-by-round extractor is **defined** as running that
image on the contract machine (`Machine.lean`) and decoding its output
(`ExtractorImage.toExtractor`). The budget `B(k) = 2^(2k+16)` steps is the **total** over the
`n + 1` calls of the round-by-round extractor of an `n`-round protocol: the submitter chooses how
it is split over the calls (`ExtractorImage.fuel`, S4-A14; a round-0 decoder may take almost all
of it), and the contract bounds the total, not the split. Calls may pass state through the
witness words, so the whole extraction runs for at most `B(k)` steps; adding rounds buys nothing. A
fault, a trap, fuel exhaustion or an output longer than `witCap k` words yields the empty
witness. `Security.lean`'s `KSF` laws are stated about this function; there is no separate
agreement theorem and no separate step bound. The laws force a witness in `relK` only before
round 0, where `[]` fails; after round 0 the submitter's state function says what an output must
satisfy, `[]` included.

**Serialisation (S4-A1).** It is the contract's, not the submitter's: a submitter-supplied
encoder or decoder would be unbounded Lean computation on the extractor's path (it could append
a brute-forced preimage to the tape for the image to copy), which would void the fuel bound.
* Input tape (`extractorTape`): a directory (`frame`), then the sections `[j]` (the round before
  which the witness is wanted), the layout `L` (`Layout.words`), the statement `x` (32 words),
  one section per transcript round in order (`Round.words`: an oracle's elements; a challenge's
  tape words, v0.3's convention), and the witness `w` after round `j` (empty for `extractOut`).
* Witnesses (`Mid`): before round 0 the witness tables, decoded from the output by `decTables`;
  after round 0, the image's own output words, unchanged. A submitter's `KSF` reads structure
  into these words as it likes; its laws are about the words.
* Size cap (O-1): an output of more than `witCap k = 2^(k+12)` words is discarded. It is an
  interface cap, not a security bound (the fuel already bounds what an output can contain): the
  largest intermediate witness an extraction passes between calls, four maximum-size oracles.

The image is a literal (rendered from the claim, as v0.3's images) of at most `imageCap` bytes,
so the precomputation it can carry is bounded; the harness gate requires it to be computable.
-/
import RecursionFast.Contract.Machine
import RecursionFast.Contract.Security
import RecursionFast.Contract.Layout

namespace RecursionFast

/-- The extractor budget `B(k)` at class `k`: the total number of steps over all the calls of
one extraction. It is `2^16` times the square of the witness-cell cap `2^k` (a sixteenth of the
square of the longest admissible oracle). It excludes enumerating `2^128` candidates. At about
10 steps per `K` multiply-add it admits O(N²) decoding up to about `2^(k+6)` elements and
quasi-linear decoding of every admissible oracle, not cubic Gaussian elimination (`k ≥ 17`). -/
def extractorBudget (k : ℕ) : ℕ := 2 ^ (2 * k + 16)

/-- The longest extractor output that counts, in words, at class `k` (O-1, S4-A1): an
interface cap on what one call passes to the next. -/
def witCap (k : ℕ) : ℕ := 2 ^ (k + 12)

/-- Contract cap on an extractor image: `2^20` bytes (v0.3's image cap). -/
def imageCap : ℕ := 2 ^ 20

/-! ### Input tape -/

/-- A number as a word: its low 64 bits. -/
def toWord (a : ℕ) : Word := BitVec.ofNat 64 a

/-- A table of `c` columns: its height, then its cells in `rows × c`, row by row. -/
def Table.words (c : ℕ) (T : Table K) : List Word :=
  toWord T.rows :: (List.range (T.rows * c)).map fun q => (T.cell (q / c) (q % c)).bits

/-- A chip: its columns; the gadget's `cons, t, q`; each matrix (its length, then each entry as
row, column, value); each term (its length, then its matrices); the coefficients; the number of
ports, then each port (bus, `1` if it sends else `0`, selector, message length, message
columns); the fixed table (`0`, or `1` and the table). -/
def Chip.words (C : Chip K) : List Word :=
  let g := C.gadget
  [C.cols, g.cons, g.t, g.q].map toWord ++
    (List.ofFn g.M).flatMap (fun M => toWord M.length ::
      M.flatMap fun e => [toWord e.1, toWord e.2.1, e.2.2.bits]) ++
    (List.ofFn g.S).flatMap (fun S => toWord S.length :: S.map fun j => toWord j.val) ++
    (List.ofFn g.c).map K.bits ++
    toWord C.ports.length :: C.ports.flatMap (fun p =>
      [p.bus, if p.send then 1 else 0, p.sel, p.msg.length].map toWord ++ p.msg.map toWord) ++
    C.fixed.elim [0] fun T => 1 :: T.words C.cols

/-- A layout: the number of chips, the public chip, the kinds of buses `0 … 255` (`1` for
`sub`; admissible layouts use no other bus), then the chips. -/
def Layout.words (L : Layout K) : List Word :=
  [toWord L.chips.length, toWord L.pub] ++
    (List.range (2 ^ 8)).map (fun b => toWord (if L.bus b = .sub then 1 else 0)) ++
    L.chips.flatMap Chip.words

/-- The words of a round's value: a message oracle's elements in order, or a challenge's tape
words (E elements as 3 limbs, indices zero-extended: `Round.tapeWords`). -/
def Round.words : (r : Round) → r.Ty → List Word
  | .msg _, v => List.ofFn fun i => (v i).bits
  | .chal nE idx, v => Round.tapeWords (.chal nE idx) v

/-- Sections behind a directory: the number of sections, then for each section the index of
its first word in the result and its length, then the sections in order. -/
def frame (secs : List (List Word)) : List Word :=
  let starts := (secs.map List.length).scanl (· + ·) (1 + 2 * secs.length)
  toWord secs.length :: ((starts.zip secs).flatMap fun p => [toWord p.1, toWord p.2.length]) ++
    secs.flatten

/-- **The extractor's input tape** `⟦j, (L, x), rounds, w⟧`: the sections `[j]`, `L`, `x`, one per
transcript round (`rounds`), and `w`, behind their directory. -/
def extractorTape (j : ℕ) (s : Layout K × Stmt) (rounds : List (List Word)) (w : List Word) :
    List Word :=
  frame ([toWord j] :: s.1.words :: List.ofFn (fun i => (s.2 i).bits) :: rounds ++ [w])

/-! ### Witnesses and output -/

/-- The witness before round `j` (`Security.lean`'s `WitMid`), fixed by the contract: the
witness tables before round 0, words after it (S4-A1). -/
def Mid (n : ℕ) (j : Fin (n + 1)) : Type :=
  List (Fin.cases (motive := fun _ => Type) (Table K) (fun _ => Word) j)

/-- Tables of the given column counts, read from words as `Table.words` writes them (a missing
word reads as `0`; words left over are ignored). -/
def decTables : List ℕ → List Word → List (Table K)
  | [], _ => []
  | c :: cs, ws =>
    let h := (ws.headD 0).toNat
    ⟨h, fun r i => if r < h ∧ i < c then ⟨ws.tail.getD (r * c + i) 0⟩ else 0⟩ ::
      decTables cs (ws.tail.drop (h * c))

/-- An output as the witness before round `j`: tables of `L`'s chips before round 0, the words
themselves after it. -/
def decMid {n : ℕ} (L : Layout K) (j : Fin (n + 1)) (o : List Word) : Mid n j :=
  Fin.cases (motive := fun j => List Word → Mid n j) (decTables (L.chips.map Chip.cols))
    (fun _ o => o) j o

/-- An extractor image for an `n`-round protocol at class `k`: a machine image within the image
cap (computable, harness gate), and the fuel of each of the `n + 1` calls, indexed by the round
before which the call's witness lives. The submitter chooses how the total budget `B(k)` is
split over the calls (a round-0 decoder may take almost all of it); the total, not the split, is
what the contract bounds. -/
structure ExtractorImage (k n : ℕ) where
  img : Image
  img_le : img.byteSize ≤ imageCap
  fuel : Fin (n + 1) → ℕ
  fuel_le : (List.ofFn fuel).sum ≤ extractorBudget k

namespace ExtractorImage
variable {k n : ℕ} (E : ExtractorImage k n)

/-- One call at class `k` in an `n`-round protocol: run the image on `t` with fuel `E.fuel j`
and decode the output as the witness before round `j` of layout `L`; the empty witness if the
run fails (fault, trap, fuel exhaustion) or the output exceeds `witCap k` words. -/
def call (L : Layout K) (j : Fin (n + 1)) (t : List Word) : Mid n j :=
  match run E.img t (E.fuel j) with
  | some o => if o.length ≤ witCap k then decMid L j o else []
  | none => []

/-- **The extractor of an image** on the `n` round shapes `sh`: `extractMid m` runs it on
`⟦m, s, tr, w⟧` (the transcript through round `m`, the witness after it) with fuel
`E.fuel m.castSucc`, `extractOut` on `⟦n, s, tr, []⟧` (the full transcript) with fuel
`E.fuel (Fin.last n)`. -/
def toExtractor (sh : Fin n → Round) :
    Extractor sh (Layout K × Stmt) (List (Table K)) Unit (Mid n) where
  eqIn := rfl
  extractMid m s tr w :=
    E.call s.1 m.castSucc (extractorTape m s (List.ofFn fun i => Round.words _ (tr i)) w)
  extractOut s tr _ :=
    E.call s.1 (Fin.last n) (extractorTape n s (List.ofFn fun i => (sh i).words (tr i)) [])

end ExtractorImage

end RecursionFast

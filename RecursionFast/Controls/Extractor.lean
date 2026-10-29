/-
# Controls: the extractor program and output format (`Contract/Extractor.lean`)    (§4.4; V4-6)

Programs of the contract's step-counting machine (V3-S2R-A1). Fuel is a function of the input
tape's length (V3-S1-A21), and the budget is `B t = 2^48 + 2^16 · t`.

Positive:
* `ws_computes`: the witness-sending program (`Library/WitnessSending.lean`, 21 statements) computes
  the witness-sending extractor within `8 · t` steps on every input; `ws_run_exact`: on the empty
  proof it halts in exactly 26 steps (5 memory words, 21 statements).
* `halt_computes`: the one-statement program computes the extractor that returns no witness, in
  1 step.
* **The domain is closed under extraction** (V4-A11): `decodeWit_children_size`: both children of
  a node witness that `o` output words denote have proofs of at most `8 · |o|` bytes;
  `child_in_domain`: so a child extracted within `outCap` words is within `Computes`'s domain, and
  from a deployed proof every proof of the extraction tree is.
* Format known answers (for the runner's Python twins; the expected words are those of the
  module header's format): `extractorInput_kat` (v3's: a 3-byte proof and a log of one 9-byte
  query: padding, length words, answer), `wordBytes_layout` and `wordBytes_kat` (a word's bytes,
  little-endian), `decodeWit_leaf_kat`, and for v4's node with two signed
  children `decodeWit_node_kat`, `witWords_node_kat` (`nodeKatWords`: two proofs, a one-entry and
  an empty trace, two signatures), `decodeWit_trailing` (words after the fields are ignored).

Negative:
* `ws_fuel_short`: the witness-sending program does not compute its extractor in 25 steps.
* `halt_not_ws`: the one-statement program does not compute the witness-sending extractor (wrong
  output: on the proof of a leaf witness it outputs nothing).
* `spin_computes_nothing`: a program that never halts computes no extractor at any fuel.
* `toolong_not_computes`: a program that outputs `2^24 + 1` words computes no extractor (the output
  cap).
* `ws_output_beyond_domain` (V4-A11): the domain's proof bound `8 · outCap` is tight for the
  witness-sending program: on every proof longer than it (and below `2^60` bytes) the program
  outputs more than `outCap` words, so without the bound the witness-sending entry, whose
  verifier accepts proofs of every size below the word, would compute no extractor.
* `enum_no_computes`: **a program that enumerates `2^64 − 1` candidates computes no extractor within
  the budget**, whatever its specification and declared fuel (on a 6-word tape `B` is about
  `2^48`, and the count needs `2^65` steps, `Controls/Machine.lean`, `count_short`).
* Malformed outputs denote nothing (strict reading, v4): `decodeWit_bad_tag`, `decodeWit_empty`,
  `decodeWit_short_leaf` (a missing word is no longer read as `0`), `decodeWit_long_proof` (V3-S1
  review m5: a 10-word output declaring a `2^63`-byte proof), **`decodeWit_long_trace`** (a trace
  declaring `2^63` entries, V4-A7 (c)), `decodeWit_short_sig` (a signature one digest short).
-/
import RecursionFast.Library.WitnessSending
import RecursionFast.Controls.Machine

namespace RecursionFast.Controls.Extractor
open RecursionFast RecursionFast.WitnessSending XStmt
open RecursionFast.Controls.Machine (count count_short spin spin_run dec exec_dec)

/-! ## The witness-sending program -/

theorem ws_computes : Computes ext E fuel := computes

/-- The input of the zero statement, the empty proof and the empty log (6 words). -/
def tape0 : List Word := extractorInput (Vector.replicate 32 0) ByteArray.empty []

theorem tape0_length : tape0.length = 6 := by decide +kernel

theorem ws_run_exact : ext.run tape0 26 = some [] := by decide +kernel

theorem ws_run_short : ext.run tape0 25 = none := by decide +kernel

/-- **Beyond the domain's proof bound** the witness-sending program's output is over the cap. -/
theorem ws_output_beyond_domain (c : Digest) (π : Proof) (L : Log) (h : 8 * outCap < π.size)
    (h' : π.size < 2 ^ 60) : ∃ o, ext.run (extractorInput c π L) (fuel (extractorInput c π L).length)
      = some o ∧ outCap < o.length :=
  ⟨_, ext_run c π L h', by rw [packBytes_length, ← size_eq_length]; unfold outCap at *; omega⟩

/-- **Fuel exhaustion**: 25 steps are not enough. -/
theorem ws_fuel_short : ¬ Computes ext E fun _ => 25 := by
  intro h
  obtain ⟨o, ho, -⟩ := h (Vector.replicate 32 0) .empty [] (by decide) (by simp) (by decide)
  cases ws_run_short.symm.trans ho

/-! ## The one-statement program -/

/-- One statement, no memory, no output. -/
def haltProg : XProg := ⟨0, 0, .const 0 0⟩

theorem halt_run (t : List Word) (f : ℕ) : haltProg.run t (f + 1) = some [] := by
  simp [haltProg, XProg.run, XProg.memFor, exec]

/-- **The one-statement program computes the extractor that returns nothing.** -/
theorem halt_computes : Computes haltProg (fun _ _ _ => none) fun _ => 1 :=
  fun _ _ _ _ _ _ => ⟨[], halt_run _ 0, by decide, rfl⟩

/-- **Wrong output**: it does not compute the witness-sending extractor. -/
theorem halt_not_ws : ¬ Computes haltProg E fun _ => 1 := by
  intro h
  have hs := size_encode_leaf (Vector.replicate 32 0) 0
  obtain ⟨o, ho, -, hd⟩ := h (Vector.replicate 32 0) (encode (.leaf (Vector.replicate 32 0) 0)) []
    (by rw [hs]; decide) (by simp)
    (by simp [extractorInput_eq, packBytes_length, hs, logWords])
  cases (halt_run _ 0).symm.trans ho
  exact nomatch hd.trans (decode_encode (.leaf _ 0) (by decide : (0 : ℕ) < 2 ^ 64))

/-! ## No halt; too long an output; enumeration -/

/-- **A program that never halts computes no extractor**, at any fuel. -/
theorem spin_computes_nothing (E : Digest → Proof → Log → Option Wit) (f : ℕ → ℕ) :
    ¬ Computes spin E f := by
  intro h
  obtain ⟨o, ho, -⟩ := h (Vector.replicate 32 0) .empty [] (by decide) (by simp) (by decide)
  cases (spin_run _ _).symm.trans ho

/-- The loop body that outputs `M[0]`, then counts it down. -/
def outDec : XStmt := .seq (.out 0) dec

/-- Output `2^24 + 1` words. -/
def toolongProg : XProg :=
  ⟨2, 0, .seq (.const 0 (toWord (2 ^ 24 + 1))) (.seq (.const 1 1) (.loop 0 outDec))⟩

theorem exec_outDec {I M o : Array Word} {n : ℕ} {ks : List XStmt} :
    exec I (n + 1) M o (outDec :: ks) = exec I n M o (.out 0 :: dec :: ks) := rfl

theorem outDec_loop (I : Array Word) (f : ℕ) :
    ∀ j (o : Array Word), j < 2 ^ 64 → ∃ r, exec I (f + 4 * j + 1) #[toWord j, 1] o
      [.loop 0 outDec] = some r ∧ r.length = o.size + j := by
  intro j
  induction j with
  | zero => intro o _; rw [exec_loop_eq (by decide)]; simp
  | succ j ih =>
    intro o hj
    have hne : (#[toWord (j + 1), 1] : Array Word).getD 0 0 ≠ 0 := by
      simpa using (toWord_eq_zero hj).not.mpr (by omega)
    rw [show f + 4 * (j + 1) + 1 = (f + 4 * j + 1 + 1 + 1 + 1) + 1 by ring, exec_loop_ne hne,
      exec_outDec, exec_out, exec_dec, Machine.dec_mem]
    obtain ⟨r, hr, hl⟩ := ih (o.push _) (by omega)
    exact ⟨r, hr, by simp [hl]; omega⟩

theorem toolong_mem (I : Array Word) (n : ℕ) :
    exec I (n + 4) (Array.replicate 2 0) #[] [toolongProg.body] =
      exec I n #[toWord (2 ^ 24 + 1), 1] #[] [.loop 0 outDec] := by
  rw [show Array.replicate 2 (0 : Word) = #[0, 0] from rfl]
  simp [toolongProg, exec]

theorem toolong_run (t : List Word) : ∃ o,
    toolongProg.run t (4 * (2 ^ 24 + 1) + 7) = some o ∧ o.length = 2 ^ 24 + 1 := by
  unfold XProg.run
  simp only [show toolongProg.memFor t.length = 2 by simp [toolongProg, XProg.memFor],
    show 2 ≤ 4 * (2 ^ 24 + 1) + 7 by omega, ↓reduceIte]
  rw [show 4 * (2 ^ 24 + 1) + 7 - 2 = (0 + 4 * (2 ^ 24 + 1) + 1) + 4 by omega, toolong_mem]
  obtain ⟨r, hr, hl⟩ := outDec_loop t.toArray 0 (2 ^ 24 + 1) #[] (by decide)
  exact ⟨r, hr, by simpa using hl⟩

/-- **The output cap**: a program that outputs `2^24 + 1` words computes no extractor. -/
theorem toolong_not_computes (E : Digest → Proof → Log → Option Wit) :
    ¬ Computes toolongProg E fun _ => 4 * (2 ^ 24 + 1) + 7 := by
  intro h
  obtain ⟨o, ho, hl, -⟩ := h (Vector.replicate 32 0) .empty [] (by decide) (by simp) (by decide)
  obtain ⟨o', ho', hl'⟩ := toolong_run tape0
  cases ho.symm.trans ho'
  exact absurd (hl' ▸ hl) (by decide)

/-- **Enumerating `2^64 − 1` candidates is not within the budget**, for every specification and
every declared fuel within `B`. -/
theorem enum_no_computes (E : Digest → Proof → Log → Option Wit) (f : ℕ → ℕ)
    (hf : ∀ t, f t ≤ extractorBudget t) : ¬ Computes (count (2 ^ 64 - 1)) E f := by
  intro h
  obtain ⟨o, ho, -⟩ := h (Vector.replicate 32 0) .empty [] (by decide) (by simp) (by decide)
  have h6 := hf tape0.length
  change (count _).run tape0 (f tape0.length) = some o at ho
  rw [tape0_length] at h6 ho
  rw [count_short _ (by decide) _ (le_trans h6 (by unfold extractorBudget; decide))] at ho
  cases ho

/-! ## Format known answers -/

deriving instance DecidableEq for Sig, Signed, Wit

/-- The input tape of the statement `01…01`, the proof `aa bb cc` and the log with one entry, the
query `01 02 … 09` and the answer `02…02`. -/
theorem extractorInput_kat :
    extractorInput (Vector.replicate 32 1) ⟨#[0xaa, 0xbb, 0xcc]⟩
        [(⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩, Vector.replicate 32 2)] =
      [0x0101010101010101, 0x0101010101010101, 0x0101010101010101, 0x0101010101010101,
       3, 0xccbbaa, 1, 9, 0x0807060504030201, 9,
       0x0202020202020202, 0x0202020202020202, 0x0202020202020202, 0x0202020202020202] := by
  decide +kernel

/-- **A word's bytes are the 8-byte little-endian encoding** (`wordBytes w = enc64 w.toNat`, GA's
trusted-code change): byte `i` is `w / 256^i mod 256`. -/
theorem wordBytes_layout (w : Word) :
    wordBytes w = List.ofFn fun i : Fin 8 => (w.toNat / 256 ^ i.val).toUInt8 := rfl

/-- The bytes of `0x0807060504030201` are `01 02 … 08`, low byte first. -/
theorem wordBytes_kat : wordBytes 0x0807060504030201 = [1, 2, 3, 4, 5, 6, 7, 8] := by decide

/-- A leaf: tag `0`, the start `01…01` (4 words), the length `16`. -/
theorem decodeWit_leaf_kat :
    decodeWit [0, 0x0101010101010101, 0x0101010101010101, 0x0101010101010101,
        0x0101010101010101, 16] = some (.leaf (Vector.replicate 32 1) 16) := by
  decide +kernel

/-- The words of a digest whose bytes are all `b` (`b` repeated eight times per word). -/
def dw (b : Word) : List Word := List.replicate 4 (b * 0x0101010101010101)

/-- The digest whose bytes are all `b`. -/
abbrev dg (b : UInt8) : Digest := Vector.replicate 32 b

/-- The node of the format known answer: children `02…02`, `03…03`; the first signed proof
`aa bb cc`, a one-entry trace (query `01 … 09`, answer `04…04`), a signature with index 5,
chain values `06…06` and path `07…07`; the second `dd`, the empty trace, index 0, chain values
`08…08`, path `09…09`. -/
def nodeKat : Wit :=
  .node (dg 2) (dg 3)
    ⟨⟨#[0xaa, 0xbb, 0xcc]⟩, [(⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩, dg 4)],
      ⟨5, List.replicate 133 (dg 6), List.replicate 16 (dg 7)⟩⟩
    ⟨⟨#[0xdd]⟩, [], ⟨0, List.replicate 133 (dg 8), List.replicate 16 (dg 9)⟩⟩

/-- **The node format, word by word** (for the runner's Python twin): tag `1`; the two child
digests; per child the proof (length word, packed bytes), the trace (a count word, then per
entry the query's length word, its packed bytes and the answer's 4 words), the signature (the
index, then 133 and 16 digests of 4 words). -/
def nodeKatWords : List Word :=
  [1] ++ dw 2 ++ dw 3 ++
    ([3, 0xccbbaa] ++ [1, 9, 0x0807060504030201, 9] ++ dw 4 ++
      [5] ++ (List.replicate 133 (dw 6)).flatten ++ (List.replicate 16 (dw 7)).flatten) ++
    ([1, 0xdd] ++ [0] ++
      [0] ++ (List.replicate 133 (dw 8)).flatten ++ (List.replicate 16 (dw 9)).flatten)

theorem nodeKatWords_length : nodeKatWords.length = 9 + 607 + 600 := by decide +kernel

/-- The encoder writes exactly these words. -/
theorem witWords_node_kat : witWords nodeKat = nodeKatWords := by decide +kernel

/-- The node fits the format: its numbers are words, its signatures have 133 and 16 digests. -/
theorem nodeKat_fits : nodeKat.Fits :=
  ⟨⟨by decide, by decide, by decide, by decide, rfl, rfl⟩,
    ⟨by decide, by decide, by decide, by decide, rfl, rfl⟩⟩

/-- The decoder reads the node back. The kernel evaluates the encoder on `nodeKat`
(`witWords_node_kat`) and the decoder's field boundaries on these words (`decodeWit_short_sig`);
the bytes of the 302 decoded digests follow from the round trip `decodeWit_witWords` (evaluating
them and comparing them as vectors took the kernel about 90 s). -/
theorem decodeWit_node_kat : decodeWit nodeKatWords = some nodeKat :=
  witWords_node_kat ▸ decodeWit_witWords nodeKat nodeKat_fits

/-! ### Malformed outputs denote nothing -/

/-- Another tag. -/
theorem decodeWit_bad_tag : decodeWit [2, 0, 0, 0, 0, 0] = none := by decide +kernel

/-- The empty output. -/
theorem decodeWit_empty : decodeWit [] = none := rfl

/-- **Strict reading**: a leaf without its length word denotes nothing (v3 read it as `0`). -/
theorem decodeWit_short_leaf : decodeWit [0, 1, 1, 1, 1] = none := by decide +kernel

/-- **A declared length beyond the output** (V3-S1 review m5): ten words cannot denote a
`2^63`-byte proof. -/
theorem decodeWit_long_proof :
    decodeWit ([1] ++ dw 2 ++ dw 3 ++ [2 ^ 63]) = none := by decide +kernel

/-- **A malformed trace length** (V4-A7 (c)): the first child's trace declares `2^63` entries
and the output ends long before. -/
theorem decodeWit_long_trace :
    decodeWit ([1] ++ dw 2 ++ dw 3 ++ [3, 0xccbbaa] ++ [2 ^ 63] ++ [9, 0x0807060504030201, 9] ++
      dw 4) = none := by decide +kernel

/-- **A short signature**: the second child's path lacks its last digest (15 siblings cannot be
denoted; a valid signature has 16). -/
theorem decodeWit_short_sig : decodeWit (nodeKatWords.dropLast) = none := by decide +kernel

/-- Words after the last field are ignored. -/
theorem decodeWit_trailing : decodeWit (nodeKatWords ++ [7, 7]) = some nodeKat :=
  witWords_node_kat ▸ congrArg (Prod.fst <$> ·) (readWit_witWords nodeKat nodeKat_fits [7, 7])

/-! ## The domain is closed under extraction (V4-A11) -/

/-- A reader that consumes only from the front leaves a suffix no longer than its input. -/
private theorem readBytes_len {n : ℕ} {o o' : List Word} {b : List UInt8}
    (h : (readBytes n).run o = some (b, o')) : b.length ≤ 8 * o.length ∧ o'.length ≤ o.length := by
  simp only [readBytes, StateT.run] at h
  split at h
  · cases h
    exact ⟨(List.length_take_le' _ _).trans ((wordsBytes_length _).trans_le
      (Nat.mul_le_mul_left 8 (List.length_take_le' _ _))), by simp⟩
  · cases h

private theorem readNat_len {o o' : List Word} {x : ℕ} (h : readNat.run o = some (x, o')) :
    o'.length ≤ o.length := by
  match o, h with
  | _ :: _, rfl => exact Nat.le_succ _

private theorem readString_len {o o' : List Word} {b : ByteArray} (h : readString.run o = some (b, o')) :
    b.size ≤ 8 * o.length ∧ o'.length ≤ o.length := by
  simp only [readString, StateT.run_bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨n, o₁⟩, h₁, ⟨bs, o₂⟩, h₂, ⟨⟩⟩ := h
  have l1 := readNat_len h₁
  exact ⟨(readBytes_len h₂).1.trans (Nat.mul_le_mul_left 8 l1), (readBytes_len h₂).2.trans l1⟩

private theorem readDigest_len {o o' : List Word} {d : Digest} (h : readDigest.run o = some (d, o')) :
    o'.length ≤ o.length := by
  simp only [readDigest, StateT.run_bind, Option.bind_eq_bind, Option.bind_eq_some_iff,
    StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨bs, o₁⟩, h₁, -, rfl⟩ := h
  exact (readBytes_len h₁).2

/-- A reader that never lengthens what is left. -/
private def Shrinks {α : Type} (r : Reader α) : Prop := ∀ o o' x, r.run o = some (x, o') → o'.length ≤ o.length

private theorem shrinks_bind {α β : Type} {r : Reader α} {f : α → Reader β} (hr : Shrinks r)
    (hf : ∀ a, Shrinks (f a)) : Shrinks (r >>= f) := by
  intro o o' x h
  simp only [StateT.run_bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, o₁⟩, h₁, h₂⟩ := h
  exact (hf a _ _ _ h₂).trans (hr _ _ _ h₁)

private theorem shrinks_pure {α : Type} (a : α) : Shrinks (pure a : Reader α) := by
  rintro _ _ _ ⟨⟩
  exact le_rfl

private theorem shrinks_readList {α : Type} {r : Reader α} (hr : Shrinks r) : ∀ n, Shrinks (readList r n)
  | 0 => shrinks_pure _
  | n + 1 => shrinks_bind hr fun _ => shrinks_bind (shrinks_readList hr n) fun _ => shrinks_pure _

private theorem shrinks_readSigned : Shrinks readSigned := by
  have hs : Shrinks readString := fun _ _ _ h => (readString_len h).2
  have hd : Shrinks readDigest := fun _ _ _ h => readDigest_len h
  have hn : Shrinks readNat := fun _ _ _ h => readNat_len h
  have he : Shrinks readEntry := shrinks_bind hs fun _ => shrinks_bind hd fun _ => shrinks_pure _
  exact shrinks_bind hs fun _ => shrinks_bind (shrinks_bind hn fun n => shrinks_readList he n) fun _ =>
    shrinks_bind (shrinks_bind hn fun _ => shrinks_bind (shrinks_readList hd _) fun _ =>
      shrinks_bind (shrinks_readList hd _) fun _ => shrinks_pure _) fun _ => shrinks_pure _

/-- The proof of a signed proof read from `o` has at most `8 · o.length` bytes. -/
private theorem readSigned_pi {o o' : List Word} {s : Signed} (h : readSigned.run o = some (s, o')) :
    s.π.size ≤ 8 * o.length := by
  simp only [readSigned, StateT.run_bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨π, o₆⟩, h₆, ⟨tr, o₇⟩, -, ⟨σ, o₈⟩, -, ⟨⟩⟩ := h
  exact (readString_len h₆).1

/-- **The domain is closed under extraction** (V4-A11): both children of a node witness that an
output of `o` words denotes have proofs of at most `8 · o.length` bytes, so a child extracted
within `outCap` words is within `Computes`'s domain of `8 · outCap` bytes (`child_in_domain`). -/
theorem decodeWit_children_size {o : List Word} {c₁ c₂ : Digest} {p₁ p₂ : Signed}
    (h : decodeWit o = some (.node c₁ c₂ p₁ p₂)) :
    p₁.π.size ≤ 8 * o.length ∧ p₂.π.size ≤ 8 * o.length := by
  obtain ⟨⟨_, o'⟩, hr, rfl⟩ : ∃ a, readWit.run o = some a ∧ a.1 = .node c₁ c₂ p₁ p₂ :=
    Option.map_eq_some_iff.mp h
  simp only [readWit, StateT.run_bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
  obtain ⟨⟨_ | _ | _, o₁⟩, hk, hr⟩ := hr
  · simp [Option.bind_eq_some_iff] at hr
  · simp only [StateT.run_bind, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨d₁, o₂⟩, h₂, ⟨d₂, o₃⟩, h₃, ⟨s₁, o₄⟩, h₄, ⟨s₂, o₅⟩, h₅, ⟨⟩⟩ := hr
    have l₃ := ((readDigest_len h₃).trans (readDigest_len h₂)).trans (readNat_len hk)
    exact ⟨(readSigned_pi h₄).trans (Nat.mul_le_mul_left 8 l₃),
      (readSigned_pi h₅).trans (Nat.mul_le_mul_left 8 ((shrinks_readSigned _ _ _ h₄).trans l₃))⟩
  · cases hr

/-- An extracted child within the output cap is within the extractor's domain. -/
theorem child_in_domain {o : List Word} {c₁ c₂ : Digest} {p₁ p₂ : Signed}
    (h : decodeWit o = some (.node c₁ c₂ p₁ p₂)) (hl : o.length ≤ outCap) :
    p₁.π.size ≤ 8 * outCap ∧ p₂.π.size ≤ 8 * outCap :=
  have h8 := Nat.mul_le_mul_left 8 hl
  (decodeWit_children_size h).imp (·.trans h8) (·.trans h8)

end RecursionFast.Controls.Extractor

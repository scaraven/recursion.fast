/- S9 compile fix pass (S9F-M4): an indexing benchmark protocol. `cmpToy`'s rounds and verifier at
class 24, with a holographic-sized index oracle: `2^m` elements in leaves of 16, holding the
layout's serialisation (`Library/Codec.lean`, `eLayout`) followed by zeros. NOT SECURE. -/
import RecursionFast.Controls.CompileToy
import RecursionFast.Library.Codec

namespace S3IdxBench
open RecursionFast RecursionFast.Controls.Compile

/-- An index oracle as a precomputed function, boxed: Lean's compiler eta-expands a definition
`Layout K → OVal o` that starts with a `let`, so a precomputation inside `IDX L` would be redone
for every element read (measured: 190 ms per element here). A structure field is not expanded. -/
structure IdxFn (m : ℕ) where
  /-- The oracle. -/
  g : OVal ⟨m, 4⟩

/-- The layout's serialisation, then zeros, computed once. -/
def idxFn (m : ℕ) (L : Layout K) : IdxFn m :=
  let a := (Codec.eLayout L).toArray
  ⟨fun p => a.getD p.val 0⟩

/-- `cmpToy` at class 24 with the index oracle `F` (the layout's, precomputed; `4 ≤ m ≤ 32`). -/
def bench (m : ℕ) (h4 : 4 ≤ m) (h32 : m ≤ 32) (F : IdxFn m) : Protocol 24 where
  k_range := by decide
  n := 3
  n_le := by decide
  shape := cmpShape
  vkLen := 1
  vkLen_le := by decide
  VK := cmpVK
  idxShape := ⟨m, 4⟩
  IDX := fun _ => F.g
  shape_ok := ⟨fun j => match j with
    | 0 => ⟨by decide, by decide⟩
    | 1 => fun b hb => by simp at hb; omega
    | 2 => ⟨by decide, by decide⟩, h4, by omega⟩
  prover := { next := cmpNext, output := fun _ _ _ => ((), ()) }
  verify := cmpVerify
  extractor := firstMsgImage 24 3
  ε := fun _ => 0

end S3IdxBench

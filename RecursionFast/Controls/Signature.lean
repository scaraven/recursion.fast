/-
# Controls: the trace digest and the signature check (`Contract/Signature.lean`)   (V4-3)

Layout controls evaluate no hash (`decide`, `decide +kernel` on byte lists, or `rfl` on symbolic
inputs); the hash known answers
are decided by the kernel (`decide +kernel`, five compressions in all), each against the
`python3 -I` command in its docstring (`hashlib.blake2s`, `digest_size=32`).

**`traceDigest`.** Positive: `traceBytes_kat` (the entry layout `enc64 |q| ‖ q ‖ a`, no hash),
`traceDigest_layout` (`tagTrace` first), `traceDigest_kat` (a one-entry trace against `hashlib`;
the service and the runner reproduce it), `traceDigest_empty_kat` (the empty trace, which every
witness-sending child carries). Negative: `traceDigest_changed_answer` (one answer byte changed,
another digest: a signature on one trace is not, without a collision, a signature on the
other), and for every pair of traces `traceBytes_inj` (`Library/Trace.lean`).

**WOTS digits.** `wotsDigits_ff` (all `0xFF`: 128 digits `3`, checksum `0`), `wotsDigits_zero`
(all `0x00`: checksum `384 = 0b01_10_00_00_00`, digits `0, 0, 0, 2, 1`, low first),
`wotsDigits_order` (byte `0x1B` gives digits `3, 2, 1, 0`: low bits first), and the general
facts `wotsDigits_length`, `wotsDigits_le` (`Library/Signer.lean`).

**Chain, leaf, node, root.** `wotsStep_layout` (`tagWots ‖ enc64 j ‖ i ‖ s ‖ x`, 43 bytes),
`wotsStep_kat` (against `hashlib`), `wotsLeaf_length` (133 ends make 4,265 bytes),
`sigNode_kat` (against `hashlib`), `sigRoot_bits` (index `2 = 0b10`: left at level 0, right at
level 1), `wotsChain_two` (two steps from position 1 are the steps of positions 1 and 2).

**`SigOk`.** Positive: `sigOk_sign` for every secret function and key index below `2^16`, and
`sigOk_sign_ref` for the reference derivation (`Library/Signer.lean`, symbolic). Negative, for
every key, message and signature: `sigOk_idx_out_of_range` (index `2^16`), `sigOk_ots_length`
(not 133 chain values), `sigOk_path_length` (not 16 siblings), `sigOk_key_unique` (a signature
verifies under at most one key, so a child signed under another key is rejected,
`Controls/Relation.lean`).
-/
import RecursionFast.Library.Signer
import RecursionFast.Library.Fast
import RecursionFast.Controls.Hex

namespace RecursionFast.Controls.Signature
open RecursionFast
open RecursionFast.Controls.Blake2s (hex)

/-! ## The trace digest -/

/-- A one-entry trace: the query `01 02 03`, the answer `02…02`. -/
def tr₁ : Trace := [(⟨#[1, 2, 3]⟩, Vector.replicate 32 2)]

/-- The same with the answer's last byte changed to `03`. -/
def tr₁' : Trace := [(⟨#[1, 2, 3]⟩, (Vector.replicate 32 2).set 31 3)]

theorem traceBytes_kat : traceBytes tr₁ =
    [3, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3] ++ List.replicate 32 2 := by decide

theorem traceDigest_layout (tr : Trace) :
    traceDigest tr = blake2sDigest (tagTrace :: traceBytes tr) := rfl

/-- `python3 -I -c "import hashlib; print(hashlib.blake2s(b'T'+(3).to_bytes(8,'little')
+bytes([1,2,3])+bytes([2]*32)).hexdigest())"` -/
theorem traceDigest_kat : (traceDigest tr₁).toList =
    hex "8a9bab6cd3b72537116ac1deb19be38c20598e1ecdd4ff9a3da4bb6153f9acc2" := by
  rw [← traceDigestF_eq]
  decide +kernel

/-- `python3 -I -c "import hashlib; print(hashlib.blake2s(b'T').hexdigest())"` -/
theorem traceDigest_empty_kat : (traceDigest []).toList =
    hex "5b09a6d58b2575e460bb840bd94533d1be58c8e4fabefdad16cad55e76b18920" := by
  rw [← traceDigestF_eq]
  decide +kernel

/-- **A changed answer changes the digest** (`hashlib`: `0fcc0ca2…0e69` for `tr₁'`). -/
theorem traceDigest_changed_answer : traceDigest tr₁' ≠ traceDigest tr₁ := by
  rw [← traceDigestF_eq, ← traceDigestF_eq]
  decide +kernel

example {tr tr' : Trace} (h : ∀ e ∈ tr, e.1.size < 2 ^ 64) (h' : ∀ e ∈ tr', e.1.size < 2 ^ 64)
    (hb : traceBytes tr = traceBytes tr') : tr = tr' := traceBytes_inj h h' hb

/-! ## WOTS digits -/

theorem wotsDigits_ff : wotsDigits (Vector.replicate 32 0xFF) =
    List.replicate 128 3 ++ [0, 0, 0, 0, 0] := by decide +kernel

theorem wotsDigits_zero : wotsDigits (Vector.replicate 32 0) =
    List.replicate 128 0 ++ [0, 0, 0, 2, 1] := by decide +kernel

theorem wotsDigits_order : (wotsDigits ((Vector.replicate 32 0).set 0 0x1B)).take 4 =
    [3, 2, 1, 0] := by decide +kernel

example (m : Digest) : (wotsDigits m).length = wotsLen := Signer.wotsDigits_length m

example (m : Digest) : ∀ d ∈ wotsDigits m, d ≤ 3 := Signer.wotsDigits_le m

/-! ## Chain, leaf, node, root -/

theorem wotsStep_layout (j i s : ℕ) (x : Digest) :
    wotsStep j i s x = blake2sDigest (tagWots :: enc64 j ++ [i.toUInt8, s.toUInt8] ++ x.toList) ∧
      (tagWots :: enc64 j ++ [i.toUInt8, s.toUInt8] ++ x.toList).length = 43 := by
  simp [wotsStep, enc64]

/-- The digest `00 01 … 1f`. -/
def x₀ : Digest := Vector.ofFn fun i => i.val.toUInt8

/-- `python3 -I -c "import hashlib; print(hashlib.blake2s(b'W'+(5).to_bytes(8,'little')
+bytes([7,1])+bytes(range(32))).hexdigest())"` -/
theorem wotsStep_kat : (wotsStep 5 7 1 x₀).toList =
    hex "d4c46d495c47284942f4723f7d28fc0f700c23dc6983b58bae5006bf6b4f39ea" := by
  rw [← wotsStepF_eq]
  decide +kernel

/-- Two steps from position 1 are the steps of positions 1 and 2. -/
theorem wotsChain_two (j i : ℕ) (x : Digest) :
    wotsChain j i 1 2 x = wotsStep j i 2 (wotsStep j i 1 x) := rfl

theorem wotsLeaf_length (j : ℕ) (ends : List Digest) (h : ends.length = wotsLen) :
    (tagWotsLeaf :: enc64 j ++ ends.flatMap Vector.toList).length = 4265 := by
  simp [enc64, List.length_flatMap, h, wotsLen]

/-- `python3 -I -c "import hashlib; print(hashlib.blake2s(b'M'+bytes([1]*32)+bytes([2]*32))
.hexdigest())"` -/
theorem sigNode_kat : (sigNode (Vector.replicate 32 1) (Vector.replicate 32 2)).toList =
    hex "1d65faf711ab261cb6b223748dc8a6c48cf605d75c3476b6fc4cce4345e46111" := by
  rw [← sigNodeF_eq]
  decide +kernel

/-- **Bit order**: at index `2 = 0b10` the leaf is the left child at level 0 and the right child
at level 1. -/
theorem sigRoot_bits (x a b : Digest) : sigRoot 2 x [a, b] = sigNode b (sigNode x a) := rfl

/-- At index `1` the leaf is the right child. -/
theorem sigRoot_one (x a : Digest) : sigRoot 1 x [a] = sigNode a x := rfl

/-! ## `SigOk` -/

theorem sigOk_sign (sk : ℕ → ℕ → Digest) (j : ℕ) (hj : j < 2 ^ sigHeight) (m : Digest) :
    SigOk (Signer.pk sk) m (Signer.sign sk j m) = true := Signer.sigOk_sign sk j hj m

/-- The positive control with the reference derivation (V4-A4), for every seed. -/
theorem sigOk_sign_ref (seed : List UInt8) (j : ℕ) (hj : j < 2 ^ sigHeight) (m : Digest) :
    SigOk (Signer.pk (Signer.chainStart seed)) m (Signer.sign (Signer.chainStart seed) j m) =
      true := Signer.sigOk_sign _ j hj m

theorem sigOk_idx_out_of_range (vk m : Digest) (σ : Sig) (h : 2 ^ sigHeight ≤ σ.idx) :
    SigOk vk m σ = false := by
  simp [SigOk, show ¬ σ.idx < 2 ^ sigHeight by omega]

theorem sigOk_ots_length (vk m : Digest) (σ : Sig) (h : σ.ots.length ≠ wotsLen) :
    SigOk vk m σ = false := by
  simp [SigOk, h]

theorem sigOk_path_length (vk m : Digest) (σ : Sig) (h : σ.path.length ≠ sigHeight) :
    SigOk vk m σ = false := by
  simp [SigOk, h]

/-- **A signature verifies under at most one key.** -/
theorem sigOk_key_unique {vk vk' m : Digest} {σ : Sig} (h : SigOk vk m σ = true)
    (h' : SigOk vk' m σ = true) : vk = vk' := by
  simp only [SigOk, Bool.and_eq_true, decide_eq_true_eq] at h h'
  exact h.2.symm.trans h'.2

/-- Under another key, a valid signature is rejected. -/
theorem sigOk_other_key {vk vk' m : Digest} {σ : Sig} (h' : SigOk vk' m σ = true)
    (hne : vk ≠ vk') : SigOk vk m σ = false :=
  Bool.eq_false_iff.mpr fun h => hne (sigOk_key_unique h h')

end RecursionFast.Controls.Signature

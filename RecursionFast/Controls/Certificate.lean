/-
# Controls: the certificate (`Contract/Certificate.lean`), positive and negative  (DESIGN-v3 §3.2)

Positive:
* `ws_certificate`: the witness-sending submission (`Library/WitnessSending.lean`) has a
  `Certificate`: every clause (knowledge soundness, completeness, the image computing the
  extractor, the caps) is proved.
* `ws_certificateR`: and against a claim rendered the way a challenge renders it (the image as a
  literal, error `0`, no verifier query, fuel 8).
* `blake2sOracle_kat`: the instantiated oracle on the query `01 02 03` against `hashlib`
  (`BLAKE2s-256(tagRO ‖ q)`; the runner, the native prover and the liveness wrapper reproduce it).

Negative:
* `flipped_image`: the claim with one bit of one instruction flipped is not certified (the image
  binding).
* `fuel_7_claim`: a claim of fuel 7 is not certified (the declared fuel is a bound the
  submission's fuel must meet); `fuel_over_budget_claim`: a declared fuel above the budget is not
  certified either (the harness runs the image with the declared fuel).
* `rejectAll_no_certificate`: a submission whose verifier rejects everything has no certificate
  (completeness), whatever its other fields.
* `acceptAll_no_certificate`: a submission whose verifier accepts everything and whose extractor
  returns nothing has no certificate (knowledge soundness with the named extractor).
* `error_one_no_certificate`, `fuel_over_budget_no_certificate`, `big_image_no_certificate`: a
  submission declaring error `1`, a fuel of `2^41` steps, or an image of `2^18 + 1` instructions
  has no certificate (the three caps).
The certificate does **not** exclude a verifier that recognises the deployment oracle: see
`Controls/Backdoor.lean` (O-25).
-/
import RecursionFast.Controls.Security
import RecursionFast.Controls.Blake2s

open scoped NNReal

namespace RecursionFast.Controls.Certificate
open RecursionFast RecursionFast.WitnessSending
open RecursionFast.Controls.Blake2s (hex)

theorem ws_certificate : Certificate submission := certificate

/-- `python3 -I -c "import hashlib; print(hashlib.blake2s(b'R'+bytes([1,2,3])).hexdigest())"` -/
theorem blake2sOracle_kat : (blake2sOracle ⟨#[1, 2, 3]⟩).toList =
    hex "5d32eaa721251d8e473bc410cf953591949de810e935f6e06caa3f8d5ae9cf84" := by decide +kernel

/-- The claim of the witness-sending submission, as a challenge renders it. -/
def declared : Declared where
  img := ⟨[0x00100313, 0x03f31313, 0x02033583, 0x00758593, 0x0035d593, 0x02830513, 0x00000293,
    0x00000073], []⟩
  ε := 0
  qV := 0
  fuel _ := 8

theorem ws_certificateR : CertificateR declared submission :=
  ⟨certificate, rfl, le_rfl, le_rfl,
    fun _ => ⟨le_rfl, Nat.le_add_right_of_le (by decide : 8 ≤ 2 ^ 40)⟩⟩

/-- The claim with bit 0 of the third instruction flipped (`ld a1, 32(t1)` becomes an illegal
word). -/
def flipped : Declared :=
  { declared with
    img := ⟨[0x00100313, 0x03f31313, 0x02033582, 0x00758593, 0x0035d593, 0x02830513, 0x00000293,
      0x00000073], []⟩ }

theorem flipped_image : ¬ CertificateR flipped submission := fun h => by
  simpa [submission, img, flipped] using h.img

theorem fuel_7_claim : ¬ CertificateR { declared with fuel := fun _ => 7 } submission :=
  fun h => absurd (h.bounds.2.2 0).1 (by simp [submission, fuel])

theorem fuel_over_budget_claim :
    ¬ CertificateR { declared with fuel := fun _ => 2 ^ 41 } submission :=
  fun h => absurd (h.bounds.2.2 0).2 (by simp [extractorBudget])

theorem rejectAll_no_certificate (S : Submission) (hV : S.V = Security.rejectAll) :
    ¬ Certificate S := fun h =>
  Security.rejectAll_not_complete S.Vb S.P (hV ▸ h.complete)

theorem acceptAll_no_certificate (S : Submission) (hV : S.V = acceptAll)
    (hE : S.E = fun _ _ _ => none) : ¬ Certificate S := fun h =>
  (Security.acceptAll_no_kstate_none S.Vb S.ε).false (hV ▸ hE ▸ h.secure.1.some)

theorem error_one_no_certificate (S : Submission) (hε : S.ε = 1) : ¬ Certificate S := fun h =>
  (hε ▸ h.cap.1).not_gt errorCap_lt_one

theorem fuel_over_budget_no_certificate (S : Submission) (hf : S.fuel = fun _ => 2 ^ 41) :
    ¬ Certificate S := fun h => absurd (hf ▸ h.cap.2.2.1 0) (by simp [extractorBudget])

/-- The byte size of an image of `n` instructions and no data (symbolic: no list is built). -/
theorem byteSize_replicate (n : ℕ) (w : BitVec 32) :
    Image.byteSize ⟨List.replicate n w, []⟩ = 4 * n := by simp [Image.byteSize]

/-- An image of `2^18 + 1` instructions (`2^20 + 4` bytes). -/
def bigImg : Image := ⟨List.replicate (2 ^ 18 + 1) 0x00000073, []⟩

theorem big_image_no_certificate (S : Submission) (hi : S.img = bigImg) : ¬ Certificate S :=
  fun h => by
    have := h.cap.2.2.2
    rw [hi, bigImg, byteSize_replicate, imageCap] at this
    omega

end RecursionFast.Controls.Certificate

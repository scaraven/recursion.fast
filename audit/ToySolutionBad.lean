-- NEGATIVE comparator test (not a default target): one word of the rendered image is changed.
/-
  TOY SOLUTION (comparator demonstration, CI), from the challenge stub, board L (the leaf board, DESIGN §6.2), rendered by
  `python3 -I scripts/render-challenge.py L.lean.in claim.json OUT.lean` (strict schema, A4-F5;
  v2 placeholders, Stage 6b). Everything except `submission` is organiser data (A4-F2): the
  declared claim (`Declared`: the class, the hash and the Merkle arity of the configuration, and
  the extractor image, rendered from the submitted raw `.code`/`.data` files, so that the image is
  a literal and no word of it is an expensive Lean term; S4-A2, S7-A1). The comparator checks
  that the solution proves exactly `certified`, with `submission` as the only entry of
  `definition_names`; the gate then requires compiled code for the badge-path fields of
  `submission` (`--computable RecursionFast.Challenge.submission`, S5-A9). Wall times and proof
  sizes are measured by the benchmark run, not stated here (DESIGN §6).
-/
import RecursionFast.Contract
import RecursionFast.Controls.Toy

namespace RecursionFast.Challenge
open RecursionFast

def image_code_0 : ℕ := 0x63000002930065053300351513040335830383350303f3131300100313
/-- Chunks of the submitted file (8 words), 256 words each but the last. -/
def image_code_chunks : List (List ℕ) := [unpack 32 8 image_code_0]
/-- Rendered from the submitted file. -/
def image_code : List (BitVec 32) := image_code_chunks.flatten.map (BitVec.ofNat 32)
/-- Chunks of the submitted file (0 words), 256 words each but the last. -/
def image_data_chunks : List (List ℕ) := []
/-- Rendered from the submitted file. -/
def image_data : List (Word) := image_data_chunks.flatten.map (BitVec.ofNat 64)
/-- The submitted extractor image (rendered challenge data, S4-A2). -/
def image : Image := { code := image_code, data := image_data }

/-- The declared claim (rendered). -/
def declared : Declared := ⟨20, .blake2s, 2, image⟩

/-- The submission (provided by the solution): a protocol at the declared class, its compilation
configuration and the proof that the protocol is secure. -/
def submission : Submission declared.k := ⟨Controls.toy20, ⟨.blake2s, 2, by decide⟩, Controls.toy20_secure⟩

/-- **The certificate**: the configuration is the declared one, and the extractor image is the
rendered one. -/
theorem certified : Certificate declared submission :=
  ⟨⟨rfl, rfl⟩, sorry⟩

end RecursionFast.Challenge

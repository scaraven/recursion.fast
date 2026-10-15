/-
# Baseline submission: the leaf-board submission and its certificate              (UNTRUSTED)

DESIGN §3.3, §7.3, S5-A3. `submission k` packages `P_triv k`, the configuration `cfg` and
`triv_secure` as a leaf-board `Submission k`, at every class `20 ≤ k ≤ 28`. The certified class is
`k = 24`, the recursion tree's `k_min` (S6-A1: `L_chain(2^10)` fits class 24, and every
`L_chain(n)` needs `k ≥ 24` for its fixed `add8` table); board L needs the class of its largest
leaf (26 for `L_chain(2^12)`, S7-M2). The record is `declared = ⟨24, blake2s, 2, firstMsgImg⟩`.

What the certificate proves and what it does not:
* **Proved** (kernel): the protocol is secure at class 24 (`Submission.secure`), and the
  submission's configuration and extractor image are the declared ones (`certificate`; the image
  field is S7-A1). Against the rendered claim both equations are `rfl`.
* **Declared, not certified:** nothing else. The leaf-board record has no key digests (only a
  recursion-board `DeclaredR` has `digestC`/`digestL`, which the harness recomputes, S5-A3), and
  this entry has no recursion entry (no fixed point, DESIGN §7.3).
* **Measured:** nothing. The compiled verifier accepts no tape (`triv_narg`), so the entry is
  listed, unranked: it cannot run the badge path (O-10).
-/
import RecursionFastCandidate.Compiled

namespace RecursionFastCandidate
open RecursionFast

/-- The compilation configuration: BLAKE2s (the menu's only hash) at Merkle arity 2. Every
oracle of `P_triv` has one leaf, so its tree has depth 0 at every arity (`triv_depth`): the arity
changes neither the tape nor the verifier's work, and 2 is the design's default. -/
def cfg : Cfg := ⟨.blake2s, 2, by decide⟩

/-- **The leaf-board submission** at class `k`: `P_triv k`, `cfg`, and its security proof. -/
def submission (k : ℕ) (hk : 20 ≤ k ∧ k ≤ 28) : Submission k :=
  ⟨P_triv k hk, cfg, triv_secure k hk⟩

/-- The certified class, 24, is in range. -/
theorem h24 : 20 ≤ 24 ∧ 24 ≤ 28 := by decide

/-- The declared record: class 24, BLAKE2s, arity 2, the image `firstMsgImg` (`claim.json`, whose
image files `extractor/extractor.{bin,data}` render to it). -/
def declared : Declared := ⟨24, .blake2s, 2, firstMsgImg⟩

/-- **The certificate** of the declared record. -/
theorem certificate : Certificate declared (submission 24 h24) := ⟨⟨rfl, rfl⟩, rfl⟩

/-- The same certificate at every class in range (the entry is not tied to class 24). -/
theorem certificate_at (k : ℕ) (hk : 20 ≤ k ∧ k ≤ 28) :
    Certificate ⟨k, .blake2s, 2, firstMsgImg⟩ (submission k hk) := ⟨⟨rfl, rfl⟩, rfl⟩

/-- The extractor image of the submission is the library's first-message image. -/
theorem submission_img (k : ℕ) (hk : 20 ≤ k ∧ k ≤ 28) :
    (submission k hk).P.extractor.img = firstMsgImg := rfl

end RecursionFastCandidate

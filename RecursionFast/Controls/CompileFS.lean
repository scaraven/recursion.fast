/-
# Controls: the compiled argument (`Contract/Compile.lean`), Fiat–Shamir binding

On the control protocol `cmpToy` at arity 2 (`Controls/CompileToy.lean`) and on `pfs` (below), in
one kernel evaluation (`fsRuns`), plus a known-answer test of the challenge decoding.

* `root_flip`: bit 0 of the root of oracle 1 (the root is absorbed: new challenges, and the
  verifier's first check, the plain answer, which depends on `e`, rejects).
* `stmt_flip`: bit 0 of `x 31`, which the verifier never reads: only Fiat–Shamir binds it.
* `fs_binding`: a prover that commits to another oracle (`p ↦ p + 1000`) with valid openings
  under its own root, but answers the challenges of the honest root (`cheat`).
* `pfs_honest`, `pfs_cheat` (S3-M2): a plain message **before** a challenge, the pattern plain
  oracles (S3-A1) exist for (a sumcheck polynomial, then its challenge). `pfs` sends `a`, receives
  `e`, sends `m`, and accepts iff `m = e.c0 + a`. The cheat picks `a = 6` after the challenge of a
  sponge that does not absorb plain messages; it is rejected because `pass` absorbs them.
* `decode_kat` (S3-M2): `chal 1 [8, 64]` decodes the bytes `0, 1, …, 47` with the `E` limbs from
  bytes `0–7`, `8–15`, `16–23`, index 0 the low 8 bits of the word at byte 24 (`0x18`) and index 1
  the word at byte 32. A decoder reading index `j` at byte `8j` gives `0x00`, `0x0f0e…08`.

`pfs` and the two `pfs` tapes are from the S3 review (`probes/s3/RevKill.lean`); the tapes are
pinned to the independent encoder `probes/s3/indep_encoder.py` (`pfs_tapes`) and the honest one
to `prove` (`#guard`).
-/
import RecursionFast.Controls.CompileToy

namespace RecursionFast.Controls.Compile
open RecursionFast

/-! ## `pfs`: a plain message before a challenge -/

/-- Rounds: a plain element, a challenge of one `E` element, a plain element. -/
def pfsShape : Fin 3 → Round
  | 0 => .msg ⟨0, 0⟩
  | 1 => .chal 1 []
  | 2 => .msg ⟨0, 0⟩

/-- Accept iff the answer `m` (oracle 2) is `e.c0 + a`, `a` the first plain message (oracle 1). -/
def pfsVerify (_ : Fin 1 → K) (_ : Stmt) (ρ : Challenges pfsShape) : QProg Bool :=
  .query 1 0 fun a => .query 2 0 fun m => .done (m == a.map fun z => ((ρ ⟨1, rfl⟩).1 0).c0 + z)

/-- The honest prover: `a = 5`, then `m = e.c0 + 5`. -/
def pfsNext (_ : Layout K × Stmt) (_ : List (Table K)) (m : MessageIdx pfsShape)
    (tr : Transcript pfsShape m.1.castSucc) : (pfsShape m.1).Ty :=
  match m, tr with
  | ⟨0, _⟩, _ => (fun _ => ⟨5⟩ : OVal ⟨0, 0⟩)
  | ⟨1, h⟩, _ => absurd h (by decide)
  | ⟨2, _⟩, tr => (fun _ => ((tr (1 : Fin 2)).1 0).c0 + ⟨5⟩ : OVal ⟨0, 0⟩)

/-- **The plain-before-challenge control protocol** (class 20, not secure; `cmpToy`'s key and
index). -/
def pfs : Protocol 20 where
  k_range := by decide
  n := 3
  n_le := by decide
  shape := pfsShape
  vkLen := 1
  vkLen_le := by decide
  VK := cmpVK
  idxShape := ⟨1, 0⟩
  IDX := cmpIDX
  shape_ok := ⟨fun j => match j with
    | 0 => ⟨by decide, by decide⟩
    | 1 => fun b hb => by simp at hb
    | 2 => ⟨by decide, by decide⟩, by decide, by decide⟩
  prover := { next := pfsNext, output := fun _ _ _ => ((), ()) }
  verify := pfsVerify
  WitMid := fun _ => List (Table K)
  extractor := { eqIn := rfl, extractMid := fun _ _ _ w => w, extractOut := fun _ _ _ => [] }
  ε := fun _ => 0

/-- The honest `pfs` tape: `a = 5`, `m = e.c0 + 5`. -/
def pfsTape : Tape :=
  [0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x59, 0x30, 0x73, 0x26, 0xbd, 0x90, 0x63, 0x03]

/-- The cheat against a sponge that skips plain messages: `a = 6`, `m = e'.c0 + 6`. -/
def pfsCheat : Tape :=
  [0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe5, 0xd8, 0x1e, 0x33, 0x20, 0xe7, 0x4d, 0x74]

-- Python `pfs_tapes` (`logs/S3-review/indep-encoder.log`) and the honest prover.
#guard pfsTape = hex "050000000000000059307326bd906303"
#guard pfsCheat = hex "0600000000000000e5d81e3320e74d74"
#guard prove cfg2 pfs L0 x0 [] = some pfsTape
#guard (index cfg2 pfs L0).2 = vkc2.2

/-! ## Kernel checks -/

/-- The Fiat–Shamir tamperings and `pfs`, in one kernel evaluation. -/
theorem fsRuns :
    NARG cfg2 cmpToy vkc2 x0 (flip tape2 0) = false ∧
    NARG cfg2 cmpToy vkc2 x1 tape2 = false ∧
    NARG cfg2 cmpToy vkc2 x0 cheatTape = false ∧
    NARG cfg2 pfs vkc2 x0 pfsTape = true ∧
    NARG cfg2 pfs vkc2 x0 pfsCheat = false := by
  decide +kernel

theorem root_flip : NARG cfg2 cmpToy vkc2 x0 (flip tape2 0) = false := fsRuns.1
theorem stmt_flip : NARG cfg2 cmpToy vkc2 x1 tape2 = false := fsRuns.2.1
theorem fs_binding : NARG cfg2 cmpToy vkc2 x0 cheatTape = false := fsRuns.2.2.1
theorem pfs_honest : NARG cfg2 pfs vkc2 x0 pfsTape = true := fsRuns.2.2.2.1
theorem pfs_cheat : NARG cfg2 pfs vkc2 x0 pfsCheat = false := fsRuns.2.2.2.2

/-- Bytes `0, 1, …, 47`. -/
def ramp : List UInt8 := (List.range 48).map Nat.toUInt8

/-- **Challenge decoding, known answer** (S3-M2): `E` limbs from bytes `0–7`, `8–15`, `16–23`;
index 0 the low 8 bits of the word at byte 24; index 1 the word at byte 32. -/
theorem decode_kat :
    ((Round.chal 1 [8, 64]).decode ramp).1 0 =
      ⟨⟨0x0706050403020100⟩, ⟨0x0f0e0d0c0b0a0908⟩, ⟨0x1716151413121110⟩⟩ ∧
    (((Round.chal 1 [8, 64]).decode ramp).2 ⟨0, by decide⟩).toNat = 0x18 ∧
    (((Round.chal 1 [8, 64]).decode ramp).2 ⟨1, by decide⟩).toNat = 0x2726252423222120 := by
  decide +kernel

end RecursionFast.Controls.Compile

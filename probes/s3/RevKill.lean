/- S3 review probe (kernel evaluation, one `decide +kernel`): the controls that kill the two
surviving mutants of `probes/s3/RevMutants.lean`. Tapes are pinned bytes, cross-checked against the
independent encoder `probes/s3/indep_encoder.py` (`pfs_tapes`), not computed by `prove`.

* `idx_path_flip`: bit 0 of byte 120 (a digest of the INDEX path; the index leaf `100` is intact):
  rejected only by the authentication of oracle 0 against the key's root. Kills `NARGidx`.
* `pfs_honest` / `pfs_cheat`: a plain message `a` before a challenge (the sumcheck pattern of
  S3-A1). The cheat picks `a = 6` after the challenge of a sponge that does not absorb `a`; the
  contract's `NARG` rejects it. Kills `NARGplain` (consistent with a mutated `prove`, too).
-/
import RecursionFast.Controls.CompileToy
open RecursionFast RecursionFast.Controls.Compile

namespace RecursionFast.S3Review

def pfsShape : Fin 3 → Round
  | 0 => .msg ⟨0, 0⟩
  | 1 => .chal 1 []
  | 2 => .msg ⟨0, 0⟩

/-- Accept iff the answer `m` (oracle 2) is `e.c0 + a`, `a` the first plain message (oracle 1). -/
def pfsVerify (_ : Fin 1 → K) (_ : Stmt) (ρ : Challenges pfsShape) : QProg Bool :=
  .query 1 0 fun a => .query 2 0 fun m => .done (m == a.map fun z => ((ρ ⟨1, rfl⟩).1 0).c0 + z)

def pfsNext (_ : Layout K × Stmt) (_ : List (Table K)) (m : MessageIdx pfsShape)
    (tr : Transcript pfsShape m.1.castSucc) : (pfsShape m.1).Ty :=
  match m, tr with
  | ⟨0, _⟩, _ => (fun _ => ⟨5⟩ : OVal ⟨0, 0⟩)
  | ⟨1, h⟩, _ => absurd h (by decide)
  | ⟨2, _⟩, tr => (fun _ => ((tr (1 : Fin 2)).1 0).c0 + ⟨5⟩ : OVal ⟨0, 0⟩)

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
  extractor := firstMsgImage 20 3
  ε := fun _ => 0

/-- The honest `pfs` tape (Python `pfs_tapes`): `a = 5`, `m = e.c0 + 5`. -/
def pfsTape : Tape := hex "050000000000000059307326bd906303"

/-- The cheat against a sponge that skips plain messages (Python `pfs_tapes`). -/
def pfsCheat : Tape := hex "0600000000000000e5d81e3320e74d74"

theorem kill :
    NARG cfg2 cmpToy vkc2 x0 (flip tape2 120) = false ∧
    NARG cfg2 pfs vkc2 x0 pfsTape = true ∧
    NARG cfg2 pfs vkc2 x0 pfsCheat = false := by
  decide +kernel

end RecursionFast.S3Review

#print axioms RecursionFast.S3Review.kill

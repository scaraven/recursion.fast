/-
# Controls: the compiled argument (`Contract/Compile.lean`), honest run and Merkle side

On the control protocol `cmpToy` at arity 2 (`Controls/CompileToy.lean`). All runs are one kernel
evaluation (`runs`, `decide +kernel`), so the kernel's cache computes the hashes they share once.
Each tampering flips bit 0 of one byte of the honest tape.

* `honest_accepted` (positive): the honest tape, under the indexer's key.
* `leaf_flip`: a leaf of oracle 1 (its path no longer climbs to the root on the tape).
* `path_flip`: a digest of that path.
* `plain_flip`: the plain element (absorbed, and read by the verifier).
* `idx_leaf_flip`: a leaf of the index oracle (checked against the key's root).
* `idx_path_flip` (S3-m2): a digest of the index path, the index leaf `100` intact: rejected only
  by the authentication of oracle 0 against the key's root.
* `oob_rejected` (S3-m2): a verifier that reads leaf 4 of a 4-leaf oracle, on a tape holding leaf
  0's valid opening (`4 mod 2^2` has leaf 0's base-2 digits): rejected only by the range check.
* `leftover`: one extra byte; `truncated`: one byte short.
* `oversize`: a tape beyond `tapeCap` (by the general `narg_oversize`, no evaluation).
* `toy_local` (S3-m6, positive): `narg_local`'s conclusion is not vacuous. The honest oracle list
  is `Consistent` with the views and the opened leaves of the honest tape, so `narg_local` turns
  the accepted tape into an accepting run of the query program on real oracles.
-/
import RecursionFast.Controls.CompileToy

namespace RecursionFast.Controls.Compile
open RecursionFast

/-- `oob`: `cmpToy`'s rounds and key, but the verifier reads leaf `4` of the 4-leaf oracle 1 (out
of range, so the IOP rejects) and accepts iff it is `[7]`. -/
def oob : Protocol 20 :=
  { cmpToy with verify := fun _ _ _ => .query 1 4 fun a => .done (a == [⟨7⟩]) }

/-- Oracle 1's root, a plain word `0`, and leaf 0's valid opening (`#guard`ed below). -/
def oobTape : Tape :=
  [0x60, 0x04, 0xbd, 0xd3, 0x0c, 0xf0, 0x06, 0xe9, 0x2e, 0xc9, 0x66, 0xda,
   0x6a, 0x25, 0x7f, 0x20, 0xf6, 0xf4, 0x2b, 0xa1, 0xca, 0xdd, 0xb6, 0xec,
   0xfb, 0x16, 0x2e, 0x2f, 0x69, 0x8a, 0x6a, 0xef, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x36, 0xe2, 0xe9, 0x20, 0x27, 0x8b, 0x3c, 0x0c, 0x59, 0xfd, 0x9f, 0xa1,
   0x34, 0xc4, 0xa4, 0x10, 0x95, 0x4f, 0x51, 0xc3, 0xa3, 0x66, 0x34, 0x8b,
   0xec, 0x4f, 0xd5, 0x46, 0xa6, 0xbe, 0x98, 0xe9, 0x9a, 0x67, 0xa1, 0x1f,
   0x66, 0x4e, 0x66, 0x67, 0xfb, 0x36, 0x96, 0x36, 0x76, 0x9e, 0x53, 0xfa,
   0x9e, 0x90, 0x0a, 0x3d, 0x9f, 0xbd, 0xcd, 0x7b, 0x11, 0x30, 0x54, 0x38,
   0xc5, 0x37, 0x93, 0x70]

#guard oobTape = commit cfg2 ⟨⟨2, 0⟩, fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩⟩ ++ K.bytes 0 ++
  K.bytes ⟨7⟩ ++ (pathOf cfg2 ⟨⟨2, 0⟩, fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩⟩ 0).flatten.flatten

/-- The bytes the honest pass records: the root, the squeezed challenge, the plain element. -/
def esT : Array (List UInt8) :=
  #[[0x60, 0x04, 0xbd, 0xd3, 0x0c, 0xf0, 0x06, 0xe9, 0x2e, 0xc9, 0x66, 0xda,
    0x6a, 0x25, 0x7f, 0x20, 0xf6, 0xf4, 0x2b, 0xa1, 0xca, 0xdd, 0xb6, 0xec,
    0xfb, 0x16, 0x2e, 0x2f, 0x69, 0x8a, 0x6a, 0xef],
    [0xa2, 0xf9, 0x4d, 0x6b, 0xcf, 0x63, 0xb0, 0x88, 0x0a, 0xd8, 0x43, 0x27,
    0x78, 0xe0, 0x1d, 0x85, 0x75, 0x9e, 0x36, 0x7c, 0x8c, 0x65, 0xbf, 0x49,
    0xc6, 0x3a, 0x89, 0xee, 0x67, 0x0e, 0xdc, 0xbf],
    [0x96, 0xeb, 0x4d, 0x6b, 0xcf, 0x63, 0xb0, 0x88]]

/-- The honest run, the Merkle-side tamperings, and the honest pass and openings, in one kernel
evaluation. -/
theorem runs :
    NARG cfg2 cmpToy vkc2 x0 tape2 = true ∧
    NARG cfg2 cmpToy vkc2 x0 (flip tape2 40) = false ∧
    NARG cfg2 cmpToy vkc2 x0 (flip tape2 48) = false ∧
    NARG cfg2 cmpToy vkc2 x0 (flip tape2 32) = false ∧
    NARG cfg2 cmpToy vkc2 x0 (flip tape2 112) = false ∧
    NARG cfg2 cmpToy vkc2 x0 (flip tape2 120) = false ∧
    NARG cfg2 oob vkc2 x0 oobTape = false ∧
    NARG cfg2 cmpToy vkc2 x0 (tape2 ++ [0]) = false ∧
    NARG cfg2 cmpToy vkc2 x0 tape2.dropLast = false ∧
    pass cfg2 (List.ofFn cmpToy.shape) (seed cfg2 vkc2 x0) tape2 #[] = some (esT, tape2.drop 40) ∧
    opened cfg2 (views cmpToy vkc2.2 esT)
      (cmpToy.verify vkc2.1 x0 (chals cmpToy.shape (esT.map fun b => (kList b).toArray)))
      (tape2.drop 40) = [(1, 2, [⟨9⟩]), (0, 0, [⟨100⟩])] := by
  decide +kernel

theorem honest_accepted : NARG cfg2 cmpToy (index cfg2 cmpToy L0) x0 tape2 = true :=
  index_eq ▸ runs.1
theorem leaf_flip : NARG cfg2 cmpToy vkc2 x0 (flip tape2 40) = false := runs.2.1
theorem path_flip : NARG cfg2 cmpToy vkc2 x0 (flip tape2 48) = false := runs.2.2.1
theorem plain_flip : NARG cfg2 cmpToy vkc2 x0 (flip tape2 32) = false := runs.2.2.2.1
theorem idx_leaf_flip : NARG cfg2 cmpToy vkc2 x0 (flip tape2 112) = false := runs.2.2.2.2.1
theorem idx_path_flip : NARG cfg2 cmpToy vkc2 x0 (flip tape2 120) = false := runs.2.2.2.2.2.1
theorem oob_rejected : NARG cfg2 oob vkc2 x0 oobTape = false := runs.2.2.2.2.2.2.1
theorem leftover : NARG cfg2 cmpToy vkc2 x0 (tape2 ++ [0]) = false := runs.2.2.2.2.2.2.2.1
theorem truncated : NARG cfg2 cmpToy vkc2 x0 tape2.dropLast = false := runs.2.2.2.2.2.2.2.2.1

theorem oversize : NARG cfg2 cmpToy vkc2 x0 (tape2 ++ List.replicate tapeCap 0) = false :=
  narg_oversize cfg2 cmpToy vkc2 x0 _ (by
    rw [List.length_append, List.length_replicate]
    exact Nat.lt_add_of_pos_left (by decide +kernel))

/-! ## Non-vacuity of `narg_local` -/

/-- The honest oracles: the index, `p ↦ p + 7`, the plain answer. -/
def osH : List Oracle :=
  [⟨⟨1, 0⟩, cmpIDX L0⟩, ⟨⟨2, 0⟩, fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩⟩,
   ⟨⟨0, 0⟩, fun _ => ⟨0x88b063cf6b4deb96⟩⟩]

theorem views_T : views cmpToy vkc2.2 esT =
    #[.root ⟨1, 0⟩ vkc2.2, .root ⟨2, 0⟩ (esT.getD 0 []), .plain ⟨0, 0⟩ [⟨0x88b063cf6b4deb96⟩]] := by
  have : kList [0x96, 0xeb, 0x4d, 0x6b, 0xcf, 0x63, 0xb0, 0x88] = [⟨0x88b063cf6b4deb96⟩] := by
    decide +kernel
  simp [views, cmpToy, cmpShape, List.ofFn_succ, roundViews, OShape.plain, esT, this]

/-- The honest oracles are consistent with the honest tape's views and opened leaves. -/
theorem toy_consistent : Consistent (views cmpToy vkc2.2 esT) osH
    (opened cfg2 (views cmpToy vkc2.2 esT)
      (cmpToy.verify vkc2.1 x0 (chals cmpToy.shape (esT.map fun b => (kList b).toArray)))
      (tape2.drop 40)) := by
  rw [runs.2.2.2.2.2.2.2.2.2.2, views_T]
  refine ⟨fun j => ?_, fun j o ws o' hv ho l hl => ?_, fun op hop => ?_⟩
  · rcases j with _ | _ | _ | j <;> simp [osH, View.shape]
  · rcases j with _ | _ | _ | j <;> simp [osH] at hv ho
    obtain ⟨rfl, rfl⟩ := hv; subst ho
    simp [OShape.leaves] at hl; subst hl; decide
  · simp at hop; rcases hop with rfl | rfl <;> decide

/-- **`narg_local` on the honest tape**: the accepted tape's verdict transfers to the honest
oracles (the conclusion of `narg_local` is about a real, consistent oracle list). -/
theorem toy_local :
    (cmpToy.verify vkc2.1 x0 (chals cmpToy.shape (esT.map fun b => (kList b).toArray))).eval osH =
      some true := by
  obtain ⟨-, -, es, rest, hp, hall⟩ := narg_local cfg2 cmpToy vkc2 x0 tape2 runs.1
  have hp' : pass cfg2 (List.ofFn cmpToy.shape) (seed cfg2 vkc2 x0) tape2 #[] = some (es, rest) :=
    hp
  rw [runs.2.2.2.2.2.2.2.2.2.1, Option.some.injEq, Prod.mk.injEq] at hp'
  obtain ⟨rfl, rfl⟩ := hp'
  exact hall osH toy_consistent

end RecursionFast.Controls.Compile

/-
S5 review probe (coverage): every S5 control uses one key `vkc2` as both `vkC` and `vkL`, so a
mutant `child` that verifies a leaf child under `vkC` (keys swapped) survives all of them. A node
whose leaf key differs (`vkK`, the indexer's key of `cmpToyK`, VK element `0x1235`) kills it.
Compiled evaluation (`#guard`); the kernel version would cost two `NARG` runs.
-/
import RecursionFast.Controls.RecursionData

namespace RecursionFast.Probes.S5Review
open RecursionFast RecursionFast.Controls.Compile RecursionFast.Controls.Recursion

/-- The mutant: a leaf child is verified under the recursion key. -/
def childSwap (cfg : Cfg) {k : ℕ} (P : Protocol k) (vkC _vkL : VKc P.vkLen) (x' : Stmt) :
    Tag → Stmt → Tape → Bool
  | .node, x, π =>
    decide (x.slot 0 = x'.slot 0) && decide (x.slot 1 = x'.slot 1) && NARG cfg P vkC x π
  | .leaf, x, π => NARG cfg P vkC x π

def aggOKSwap (cfg : Cfg) {k : ℕ} (P : Protocol k) (x' : Stmt) (nw : NodeWitness P.vkLen) : Bool :=
  decide (x' = nodeStmt cfg nw.vkC nw.vkL nw.x₁ nw.x₂) &&
    nw.vkC.2.length == 32 && nw.vkL.2.length == 32 &&
    childSwap cfg P nw.vkC nw.vkL x' nw.t₁ nw.x₁ nw.π₁ &&
    childSwap cfg P nw.vkC nw.vkL x' nw.t₂ nw.x₂ nw.π₂

/-- The honest prover for VK element `0x1235`. -/
def cmpNextK (s : Layout K × Stmt) (_ : List (Table K)) (m : MessageIdx cmpShape)
    (tr : Transcript cmpShape m.1.castSucc) : (cmpShape m.1).Ty :=
  match m, tr with
  | ⟨0, _⟩, _ => (fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩ : OVal ⟨2, 0⟩)
  | ⟨1, h⟩, _ => absurd h (by decide)
  | ⟨2, _⟩, tr => (fun _ => ((tr (1 : Fin 2)).1 ⟨0, by decide⟩).c0 + ⟨0x1235⟩ + s.2 0 : OVal ⟨0, 0⟩)

/-- A second key for `cmpToy`'s verifier: VK element `0x1235`, with its honest prover. -/
def cmpToyK2 : Protocol 20 :=
  { cmpToy with VK := fun _ _ => ⟨0x1235⟩, prover := { next := cmpNextK, output := fun _ _ _ => ((), ()) } }
def vkK : VKc 1 := index cfg2 cmpToyK2 L0
def tapeK : Tape := (prove cfg2 cmpToyK2 L0 x0 []).getD []

-- The mutant agrees with `aggOK` on every node of the S5 controls (positives and negatives).
#guard aggOKSwap cfg2 cmpToy xN nwN && aggOKSwap cfg2 cmpToy xR nwR
#guard !(aggOKSwap cfg2 cmpToy (nodeStmt cfg2 vkc2 vkc2 xD0 x0) nwD0) &&
  !(aggOKSwap cfg2 cmpToy (nodeStmt cfg2 vkc2 vkc2 xD1 x0) nwD1)
#guard aggOKSwap cfg2 cmpToy xN (decodeBad wGood) && !(aggOKSwap cfg2 cmpToy xN (decodeBad wBad))
-- A node with distinct keys separates them: `aggOK` accepts it, the mutant rejects it.
#guard vkK ≠ vkc2 && NARG cfg2 cmpToy vkK x0 tapeK && !(NARG cfg2 cmpToy vkc2 x0 tapeK)
#guard aggOK cfg2 cmpToy (nodeStmt cfg2 vkc2 vkK x0 x0) ⟨vkc2, vkK, .leaf, .leaf, x0, x0, tapeK, tapeK⟩
#guard !(aggOKSwap cfg2 cmpToy (nodeStmt cfg2 vkc2 vkK x0 x0) ⟨vkc2, vkK, .leaf, .leaf, x0, x0, tapeK, tapeK⟩)

/-- The mutant without S5-A1's root-length conjuncts. -/
def aggOKNoRoot (cfg : Cfg) {k : ℕ} (P : Protocol k) (x' : Stmt) (nw : NodeWitness P.vkLen) :
    Bool :=
  decide (x' = nodeStmt cfg nw.vkC nw.vkL nw.x₁ nw.x₂) &&
    child cfg P nw.vkC nw.vkL x' nw.t₁ nw.x₁ nw.π₁ && child cfg P nw.vkC nw.vkL x' nw.t₂ nw.x₂ nw.π₂

-- It agrees with `aggOK` on every node of the S5 controls …
#guard aggOKNoRoot cfg2 cmpToy xN nwN && aggOKNoRoot cfg2 cmpToy xR nwR
#guard !(aggOKNoRoot cfg2 cmpToy (nodeStmt cfg2 vkc2 vkc2 xD0 x0) nwD0) &&
  !(aggOKNoRoot cfg2 cmpToy (nodeStmt cfg2 vkc2 vkc2 xD1 x0) nwD1)
#guard aggOKNoRoot cfg2 cmpToy xN (decodeBad wGood) &&
  !(aggOKNoRoot cfg2 cmpToy xN (decodeBad wBad))
-- … and a two-leaf node whose recursion key has a 33-byte root separates them.
def vkC33 : VKc 1 := (vkc2.1, vkc2.2 ++ [0])
#guard !(aggOK cfg2 cmpToy (nodeStmt cfg2 vkC33 vkc2 x0 x1) ⟨vkC33, vkc2, .leaf, .leaf, x0, x1, tape2, tapeX1⟩) &&
  aggOKNoRoot cfg2 cmpToy (nodeStmt cfg2 vkC33 vkc2 x0 x1) ⟨vkC33, vkc2, .leaf, .leaf, x0, x1, tape2, tapeX1⟩
#eval s!"tapeK {tapeK.length} bytes, {toHex tapeK}"

end RecursionFast.Probes.S5Review

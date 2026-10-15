/- S3 review probe (compiled evaluation): mutation analysis of the Stage 3 control suite.
Updated in the S3 fix pass: the mutants mirror the fixed `NARG` (32-byte key root, challenges
decoded once from `K`-element arrays); the last `#eval` is the mutant → killing-control table.

Two mutants of the trusted verifier, each a one-line change:
* `NARGidx`: openings of oracle 0 (the index) are not authenticated (no `verifyPath`).
* `NARGplain`: plain prover messages are not absorbed by the sponge.
Each gives the SAME verdict as `NARG` on every control tape of `Controls/Compile*.lean`, so no
control kills it. Then the killing tapes: `flip tape2 120` (a digest of the index path) kills
`NARGidx`; the protocol `pfs` (plain message, challenge, plain answer) kills `NARGplain`.
-/
import RecursionFast.Controls.CompileToy
open RecursionFast RecursionFast.Controls.Compile

namespace RecursionFast.S3Review

/-- Mutant `runQ`: oracle 0's openings are parsed but not authenticated. -/
def runQidx (cfg : Cfg) (vs : Array View) : QProg Bool → Tape → Option Bool
  | .done b, [] => some b
  | .done _, _ :: _ => none
  | .query j l cont, t => match vs[j]? with
    | some (.plain o ws) => if l < o.leaves then runQidx cfg vs (cont ws) t else none
    | some (.root o r) =>
      if l < o.leaves then
        match readOpening cfg o t with
        | some (leaf, path, t) =>
          if j == 0 || verifyPath cfg r l leaf path then runQidx cfg vs (cont leaf) t else none
        | none => none
      else none
    | none => none

def NARGidx (cfg : Cfg) {k : ℕ} (P : Protocol k) (vkc : VKc P.vkLen) (x : Stmt) (t : Tape) : Bool :=
  decide (t.length ≤ tapeCap) && vkc.2.length == 32 &&
    match pass cfg (List.ofFn P.shape) (seed cfg vkc x) t #[] with
    | some (es, t) => runQidx cfg (views P vkc.2 es)
        (P.verify vkc.1 x (chals P.shape (es.map fun b => (kList b).toArray))) t == some true
    | none => false

/-- Mutant `pass`: a plain message is read but not absorbed. -/
def passPlain (cfg : Cfg) : List Round → Digest → Tape → Array (List UInt8) →
    Option (Array (List UInt8) × Tape)
  | [], _, t, es => some (es, t)
  | .msg o :: rs, s, t, es => match takeN (msgLen o) t [] with
    | some (b, t) => passPlain cfg rs (if o.plain then s else absorb cfg s b) t (es.push b)
    | none => none
  | .chal nE idx :: rs, s, t, es => match squeeze cfg s (Round.chal nE idx).chalLen with
    | (b, s) => passPlain cfg rs s t (es.push b)

def NARGplain (cfg : Cfg) {k : ℕ} (P : Protocol k) (vkc : VKc P.vkLen) (x : Stmt) (t : Tape) : Bool :=
  decide (t.length ≤ tapeCap) && vkc.2.length == 32 &&
    match passPlain cfg (List.ofFn P.shape) (seed cfg vkc x) t #[] with
    | some (es, t) => runQ cfg (views P vkc.2 es)
        (P.verify vkc.1 x (chals P.shape (es.map fun b => (kList b).toArray))) t == some true
    | none => false

/-- The control tapes of `Controls/Compile.lean` and `Controls/CompileFS.lean` (statement, tape). -/
def controls : List (String × Stmt × Tape) :=
  [("honest", x0, tape2), ("leaf_flip", x0, flip tape2 40), ("path_flip", x0, flip tape2 48),
   ("plain_flip", x0, flip tape2 32), ("idx_leaf_flip", x0, flip tape2 112),
   ("leftover", x0, tape2 ++ [0]), ("truncated", x0, tape2.dropLast),
   ("root_flip", x0, flip tape2 0), ("stmt_flip", x1, tape2), ("fs_binding", x0, cheatTape)]

-- Verdicts (NARG, NARGidx, NARGplain) on every control: identical columns = mutant survives.
#eval controls.map fun (n, x, t) =>
  (n, NARG cfg2 cmpToy vkc2 x t, NARGidx cfg2 cmpToy vkc2 x t, NARGplain cfg2 cmpToy vkc2 x t)

-- Killing tape for `NARGidx`: a flipped digest of the INDEX path (byte 120); leaf 100 intact.
#eval (NARG cfg2 cmpToy vkc2 x0 (flip tape2 120), NARGidx cfg2 cmpToy vkc2 x0 (flip tape2 120))

/-! ## `pfs`: a plain message before a challenge (the sumcheck pattern S3-A1 is for) -/

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

/-- The honest `pfs` tape: `a = 5`, then `m = e.c0 + 5`. -/
def pfsTape : Tape := (prove cfg2 pfs L0 x0 []).getD []

/-- The challenge `e.c0` as the mutant derives it (independent of `a`). -/
def eMut : K :=
  match passPlain cfg2 (List.ofFn pfsShape) (seed cfg2 (index cfg2 pfs L0) x0) (List.replicate 16 0) #[] with
  | some (es, _) => ((chals pfsShape (es.map fun b => (kList b).toArray) ⟨1, rfl⟩).1 0).c0
  | none => 0

/-- Against the mutant, `a` can be chosen after the challenge: `a = 6`, `m = e.c0 + 6`. -/
def pfsCheat : Tape := (K.bytes ⟨6⟩) ++ (eMut + ⟨6⟩).bytes

#eval (toHex pfsTape, toHex pfsCheat)
-- (NARG, NARGplain) on the honest pfs tape and on the cheat.
#eval ((NARG cfg2 pfs (index cfg2 pfs L0) x0 pfsTape, NARGplain cfg2 pfs (index cfg2 pfs L0) x0 pfsTape),
       (NARG cfg2 pfs (index cfg2 pfs L0) x0 pfsCheat, NARGplain cfg2 pfs (index cfg2 pfs L0) x0 pfsCheat))

/-! ## Two more survivors: the leaf-range check and the index-challenge offset -/

/-- Mutant `runQ`: no `l < leaves` check before an opening. -/
def runQrange (cfg : Cfg) (vs : Array View) : QProg Bool → Tape → Option Bool
  | .done b, [] => some b
  | .done _, _ :: _ => none
  | .query j l cont, t => match vs[j]? with
    | some (.plain o ws) => if l < o.leaves then runQrange cfg vs (cont ws) t else none
    | some (.root o r) =>
        match readOpening cfg o t with
        | some (leaf, path, t) =>
          if verifyPath cfg r l leaf path then runQrange cfg vs (cont leaf) t else none
        | none => none
    | none => none

def NARGrange (cfg : Cfg) {k : ℕ} (P : Protocol k) (vkc : VKc P.vkLen) (x : Stmt) (t : Tape) : Bool :=
  decide (t.length ≤ tapeCap) && vkc.2.length == 32 &&
    match pass cfg (List.ofFn P.shape) (seed cfg vkc x) t #[] with
    | some (es, t) => runQrange cfg (views P vkc.2 es)
        (P.verify vkc.1 x (chals P.shape (es.map fun b => (kList b).toArray))) t == some true
    | none => false

/-- Mutant challenge decoding: index `j` read at element `j` (byte `8 j`, overlapping the `E`
elements) instead of element `3·nE + j`. -/
def decodeKOff : (r : Round) → Array K → r.Ty
  | .msg _, _ => fun _ => 0
  | .chal _ idx, ks => (fun j => ⟨ks.getD (3 * j) 0, ks.getD (3 * j + 1) 0, ks.getD (3 * j + 2) 0⟩,
      fun j => (ks.getD j 0).bits.setWidth (idx.get j))

def chalsOff {n : ℕ} (sh : Fin n → Round) (ks : Array (Array K)) : Challenges sh :=
  fun c => decodeKOff (sh c.1) (ks.getD c.1 #[])

def NARGoff (cfg : Cfg) {k : ℕ} (P : Protocol k) (vkc : VKc P.vkLen) (x : Stmt) (t : Tape) : Bool :=
  decide (t.length ≤ tapeCap) && vkc.2.length == 32 &&
    match pass cfg (List.ofFn P.shape) (seed cfg vkc x) t #[] with
    | some (es, t) => runQ cfg (views P vkc.2 es)
        (P.verify vkc.1 x (chalsOff P.shape (es.map fun b => (kList b).toArray))) t == some true
    | none => false

-- Both survive every control of the suite (identical verdicts to `NARG`).
#eval controls.map fun (n, x, t) =>
  (n, NARG cfg2 cmpToy vkc2 x t, NARGrange cfg2 cmpToy vkc2 x t, NARGoff cfg2 cmpToy vkc2 x t)

/-- `oob`: `cmpToy`'s rounds, but the verifier reads leaf `4` of the 4-leaf oracle 1 (out of
range: the IOP rejects) and accepts iff it is `[7]`. -/
def oob : Protocol 20 := { cmpToy with verify := fun _ _ _ => .query 1 4 fun a => .done (a == [⟨7⟩]) }

/-- The oracle `p ↦ p + 7` and a tape with its root, any plain word, and leaf 0's opening. -/
def oobOracle : Oracle := ⟨⟨2, 0⟩, fun p => ⟨BitVec.ofNat 64 (p.val + 7)⟩⟩
def oobTape : Tape := commit cfg2 oobOracle ++ (K.bytes 0) ++
  (oobOracle.leaf 0).flatMap K.bytes ++ (pathOf cfg2 oobOracle 0).flatten.flatten

-- (NARG, NARGrange): the out-of-range query is accepted by the mutant with leaf 0's opening.
#eval (NARG cfg2 oob vkc2 x0 oobTape, NARGrange cfg2 oob vkc2 x0 oobTape)

/-! ## Fix pass: the mutant → killing-control table

Every control of `Controls/Compile*.lean` after the fix pass, as (name, protocol verdict under
`NARG`, under each mutant). A control kills a mutant when the two verdicts differ. `decode_kat`
is a theorem about `Round.decode`; its mutant counterpart is the same equation for `decodeKOff`. -/

/-- The verdicts of one verifier on every control tape of the fix pass. -/
def verdicts (V : ∀ {k : ℕ} (P : Protocol k), VKc P.vkLen → Stmt → Tape → Bool) : List (String × Bool) :=
  (controls.map fun (n, x, t) => (n, V cmpToy vkc2 x t)) ++
  [("idx_path_flip", V cmpToy vkc2 x0 (flip tape2 120)), ("oob", V oob vkc2 x0 oobTape),
   ("pfs_honest", V pfs vkc2 x0 (prove cfg2 pfs L0 x0 [] |>.getD [])),
   ("pfs_cheat", V pfs vkc2 x0 pfsCheat)]

/-- The controls on which a mutant's verdict differs from `NARG`'s. -/
def kills (V : ∀ {k : ℕ} (P : Protocol k), VKc P.vkLen → Stmt → Tape → Bool) : List String :=
  ((verdicts (NARG cfg2)).zip (verdicts V)).filterMap fun ((n, a), (_, b)) =>
    if a != b then some n else none

/-- `decode_kat`'s index-0 equation, under the true and the mutated decoder. -/
def ramp : List UInt8 := (List.range 48).map Nat.toUInt8
#eval ((((Round.chal 1 [8, 64]).decode ramp).2 ⟨0, by decide⟩).toNat,
  ((decodeKOff (.chal 1 [8, 64]) (kList ramp).toArray).2 ⟨0, by decide⟩).toNat)

#eval [("NARGidx", kills (NARGidx cfg2)), ("NARGplain", kills (NARGplain cfg2)),
  ("NARGrange", kills (NARGrange cfg2)), ("NARGoff", kills (NARGoff cfg2))]

end RecursionFast.S3Review

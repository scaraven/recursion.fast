/-
# Contract: recursion, the verifier as a circuit                                 (TRUSTED)

DESIGN §5. Board R ranks one 2→1 recursion step. A **node** of the recursion tree proves, with the
submitted protocol `P` compiled by `cfg`, that two **children** were accepted: each child is a
statement and a proof (a tape), tagged **leaf** (a proof of the benchmark layout `L_chain`, under
the leaf key) or **node** (a proof of the recursion layout `C_V`, under the recursion key).

**Statements as digests (§5.1).** A statement (32 elements of `K`) is 8 slots `d0 … d7` of 4
elements; a 32-byte digest fills a slot, limb `j` being bytes `8j … 8j + 7` read little-endian
(`K.ofBytes`, the inverse of `K.bytes`; Rust `u64::from_le_bytes`). The **key digest** `D` is the
trusted `VKc.digest cfg` (`Compile.lean`, S3-A8): the hash of the key's elements and its index
root. A node's statement is the **aggregate statement** `nodeStmt`: `d0 = D vkC`, `d1 = D vkL`,
`d2 = H (x₁ ‖ x₂)` (the children's statement bytes, `stmtBytes`), `d3 = (tagK t₁, tagK t₂, 0, 0)`
(the children's tags, S5-A11) and `d4 … d7 = 0`, so a node statement carries no free bits: it is a
function of the keys and the tagged children. `H = cfg.hash.run` is the hash of `D` and of the
sponge, so a recursion circuit needs one hash gadget (S5-A8). A node *child's* statement is pinned
by its parent's `d2` (collision resistance) and by its own proof (the `C_V` relation), not by
`aggOK`.

**The VK cycle** (§5.2). `C_V`'s key depends on `C_V`, which verifies proofs under that key. The
cycle is broken by the digest: the keys are witness cells of the node (`NodeWitness`), checked
against the public `d0`, `d1`; nothing in `C_V` depends on the value of its own key. A node child
must carry the parent's `d0`, `d1`, so the keys are the same at every level. The organiser's root
check (`rootOK`) recomputes the **statement tree** (`treeRoot`) over the leaf statements with the
indexer's keys for `C_V` and `L_chain`: it pins the keys, the children (by `d2`) and the tags by
position (S5-A12). The **fixed point** is that `C_V` is admissible and satisfiable at the class `k`
of `P` itself (`RecursionEntry`).

**Bounded node witnesses (S5-A1).** `aggOK` also requires both keys' index roots to be 32 bytes,
as `NARG` does for the key it uses. Otherwise a node whose children are both leaves would accept
any `vkC` whose digest is `d0`, including arbitrarily long preimages, and `complete` would ask
`C_V` to hold them.
-/
import RecursionFast.Contract.Compile

namespace RecursionFast

/-! ## Statements as digests -/

/-- A digest as a statement slot: limb `j` is bytes `8j … 8j + 7`, read little-endian. -/
def digestToSlot (d : Digest) (j : Fin 4) : K := K.ofBytes (d.drop (8 * j.val))

/-- Slot `d_i` of a statement: elements `4i … 4i + 3`. -/
def Stmt.slot (x : Stmt) (i : Fin 8) (j : Fin 4) : K := x ⟨4 * i.val + j.val, by omega⟩

/-- The statement whose slot `d_i` is `s i`. -/
def Stmt.ofSlots (s : Fin 8 → Fin 4 → K) : Stmt :=
  fun i => s ⟨i.val / 4, by omega⟩ ⟨i.val % 4, by omega⟩

/-! ## Nodes -/

/-- The kind of a child: a proof of the leaf layout, or of the recursion layout (a node). -/
inductive Tag where
  /-- A leaf proof, verified under the leaf key `vkL`. -/
  | leaf
  /-- A node proof, verified under the recursion key `vkC`. -/
  | node
  deriving DecidableEq

/-- A tag as an element of the statement: `leaf ↦ 0`, `node ↦ 1`. -/
def tagK : Tag → K
  | .leaf => 0
  | .node => 1

/-- The tag slot `d3` of a node statement: the children's tags, then two zeros. -/
def tagSlot (t₁ t₂ : Tag) (j : Fin 4) : K :=
  match j.val with
  | 0 => tagK t₁
  | 1 => tagK t₂
  | _ => 0

/-- What a node holds besides its statement: the two keys (witness cells, which breaks the VK
cycle) and, for each child, its tag, statement and proof. -/
structure NodeWitness (vkLen : ℕ) where
  /-- The recursion key (`C_V` indexed). -/
  vkC : VKc vkLen
  /-- The leaf key (`L_chain` indexed). -/
  vkL : VKc vkLen
  /-- The first child's tag. -/
  t₁ : Tag
  /-- The second child's tag. -/
  t₂ : Tag
  /-- The first child's statement. -/
  x₁ : Stmt
  /-- The second child's statement. -/
  x₂ : Stmt
  /-- The first child's proof. -/
  π₁ : Tape
  /-- The second child's proof. -/
  π₂ : Tape

/-- **The aggregate statement** of a node with keys `vkC`, `vkL` and children `x₁`, `x₂` tagged
`t₁`, `t₂`: `d0 = D vkC`, `d1 = D vkL`, `d2 = H (x₁ ‖ x₂)` with `H = cfg.hash.run`,
`d3 = tagSlot t₁ t₂`, `d4 … d7 = 0`. -/
def nodeStmt (cfg : Cfg) {vkLen : ℕ} (vkC vkL : VKc vkLen) (t₁ t₂ : Tag) (x₁ x₂ : Stmt) : Stmt :=
  Stmt.ofSlots fun i => match i.val with
    | 0 => digestToSlot (vkC.digest cfg)
    | 1 => digestToSlot (vkL.digest cfg)
    | 2 => digestToSlot (cfg.hash.run (stmtBytes x₁ ++ stmtBytes x₂))
    | 3 => tagSlot t₁ t₂
    | _ => fun _ => 0

/-- A **child** of a node with statement `x'` is accepted: a node child carries the parent's
`d0`, `d1` and verifies under `vkC`; a leaf child verifies under `vkL`. (The rest of a node
child's statement is pinned by the parent's `d2` and by the child's own proof, not here.) -/
def child (cfg : Cfg) {k : ℕ} (P : Protocol k) (vkC vkL : VKc P.vkLen) (x' : Stmt) :
    Tag → Stmt → Tape → Bool
  | .node, x, π =>
    decide (x.slot 0 = x'.slot 0) && decide (x.slot 1 = x'.slot 1) && NARG cfg P vkC x π
  | .leaf, x, π => NARG cfg P vkL x π

/-- **What a node proves** (DESIGN §5.2): `x'` is the aggregate statement of the node's keys and
tagged children, both keys have a 32-byte index root (S5-A1), and both children are accepted. -/
def aggOK (cfg : Cfg) {k : ℕ} (P : Protocol k) (x' : Stmt) (nw : NodeWitness P.vkLen) : Bool :=
  decide (x' = nodeStmt cfg nw.vkC nw.vkL nw.t₁ nw.t₂ nw.x₁ nw.x₂) &&
    nw.vkC.2.length == 32 && nw.vkL.2.length == 32 &&
    child cfg P nw.vkC nw.vkL x' nw.t₁ nw.x₁ nw.π₁ && child cfg P nw.vkC nw.vkL x' nw.t₂ nw.x₂ nw.π₂

/-! ## The statement tree and the root check -/

/-- One level of the statement tree: adjacent statements, all tagged `t`, aggregated in pairs in
order; `none` on an odd count. -/
def pairUp (cfg : Cfg) {vkLen : ℕ} (vkC vkL : VKc vkLen) (t : Tag) :
    List Stmt → Option (List Stmt)
  | x₁ :: x₂ :: r => (pairUp cfg vkC vkL t r).map (nodeStmt cfg vkC vkL t t x₁ x₂ :: ·)
  | [] => some []
  | [_] => none

/-- **The statement tree** (DESIGN §6.3 step 5): the root of the complete binary tree of depth `d`
over the leaf statements `xs`, in order, with keys `vkC`, `vkL`; level 1 aggregates leaves, every
level above aggregates nodes. `none` unless `xs` has `2^d` statements. -/
def treeRoot (cfg : Cfg) {vkLen : ℕ} (vkC vkL : VKc vkLen) (d : ℕ) (xs : List Stmt) :
    Option Stmt :=
  go .leaf d xs
where
  /-- `d` more levels over statements tagged `t`. -/
  go : Tag → ℕ → List Stmt → Option Stmt
    | _, 0, [x] => some x
    | t, d + 1, xs => (pairUp cfg vkC vkL t xs).bind (go .node d)
    | _, 0, _ => none

/-- **The organiser's root check** (DESIGN §5.1, §6.3 step 5): `x` is the root of the statement
tree of depth `d` over the leaf statements `xs`, keyed by the indexer for the recursion layout
`C` and the leaf layout `L`. It pins `d0`, `d1` (the keys), `d2` (the children, by collision
resistance, level by level) and `d3` (the tags, by position). -/
def rootOK (cfg : Cfg) {k : ℕ} (P : Protocol k) (C L : Layout K) (d : ℕ) (xs : List Stmt)
    (x : Stmt) : Bool :=
  decide (treeRoot cfg (index cfg P C) (index cfg P L) d xs = some x)

/-- **A recursion entry** (board R, DESIGN §5.3): a layout `C` (the verifier as a circuit),
admissible at `P`'s own class `k`, and a computable `decode` reading a node witness out of its
tables (the gate checks computability). `sound`: every satisfying witness decodes to a node that
`aggOK` accepts. `complete`: every node `aggOK` accepts is decoded from a satisfying witness; as
`C.rel k` bounds the cells by `2^k`, this is what makes `C` fit class `k` (the fixed point,
S1-A6), and it excludes a `C` whose `rel` is unsatisfiable (`sound` alone would be vacuous).
`complete` ranges over every accepted node, whatever its keys: `verify` must bound its own work
and its tape on every key (e.g. reject keys outside the format of `VK`). `live` keeps both from
being vacuous (S5-A10). See also: the controls have no positive entry; arithmetising `NARG` is
the submitter's work (DESIGN §7.3). -/
structure RecursionEntry {k : ℕ} (P : Protocol k) (cfg : Cfg) where
  /-- The recursion layout `C_V`. -/
  C : Layout K
  /-- `C_V` is admissible at the protocol's class. -/
  fits : C.Admissible k
  /-- The node witness held by a witness of `C_V` (computable). -/
  decode : List (Table K) → NodeWitness P.vkLen
  /-- Every satisfying witness holds an accepted node. -/
  sound : ∀ x' w, C.rel k x' w → aggOK cfg P x' (decode w) = true
  /-- Every accepted node is decoded from a satisfying witness, so every accepted statement has a
  witness of at most `2^k` cells (`decode` may also read cells outside `rows × cols`). -/
  complete : ∀ x' nw, aggOK cfg P x' nw = true → ∃ w, C.rel k x' w ∧ decode w = nw
  /-- The compiled argument accepts a node keyed by the indexer: `C`'s key and the key of some
  layout `L` (keys of no layout are excluded, as `Secure` says nothing about them). A submitter
  proves it with `aggOK_sat_of_secure` plus a bound on its own proof size. A protocol that
  special-cases the key of a trivially satisfiable layout can still meet it without accepting any
  proof of a hard layout; that the benchmark's nodes are provable is shown by the benchmark run
  (§6.3). -/
  live : ∃ L x' nw, nw.vkC = index cfg P C ∧ nw.vkL = index cfg P L ∧ aggOK cfg P x' nw = true

end RecursionFast

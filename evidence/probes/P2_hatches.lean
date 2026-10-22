import Mathlib
/-! O25 review probe P2: Lean-4 parametricity escape hatches against a `D`-polymorphic `V`.
Each block is expected to FAIL (error) or to be harmless; the log records which. -/

namespace O25P2
abbrev Digest := Vector UInt8 32

-- H1: branch on `D = Digest` with `Classical.dec`; expected: rejected as noncomputable.
def h1 (D : Type) : Bool := @decide (D = Digest) (Classical.dec _)

-- H2: same, but marked `noncomputable`; it elaborates, yet cannot be compiled into `Vb`.
noncomputable def h2 (D : Type) : Bool := @decide (D = Digest) (Classical.dec _)

-- H3: a typeclass search for bytes of an abstract `D`; expected: no instance.
def h3 (D : Type) [DecidableEq D] (d : D) : String := toString d

-- H4: `Hashable` on abstract D; expected: no instance.
def h4 (D : Type) [DecidableEq D] (d : D) : UInt64 := hash d

-- H5: `cast` to Digest without a type equality; expected: type error.
def h5 (D : Type) (d : D) : Digest := cast rfl d

-- H6: `Classical.choice` yields an abstract element only; computable use is rejected.
def h6 (D : Type) (h : Nonempty D) : D := Classical.choice h

-- H7: `Inhabited` is not in the binder list; `default : D` fails.
def h7 (D : Type) [DecidableEq D] : D := default

-- H8 (harmless, compiles): `CommRing F` gives `Nat.cast`, i.e. a native-to-F map.
def h8 (F : Type) [CommRing F] (n : ℕ) : F := (n : F)

end O25P2

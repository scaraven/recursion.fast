import Clean.Air.FlatEnsemble
import Mathlib.LinearAlgebra.Matrix.Defs

#check @Air.Flat.Ensemble
#check @Matrix
-- a use of both worlds in one file
example : (Matrix.of (fun (i j : Fin 2) => (i : ℕ) + j)) 1 1 = 2 := by decide

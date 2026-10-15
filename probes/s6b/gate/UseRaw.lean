import ForgeRaw
/-! An importer of `ForgeRaw` calling `dec` (the badge main's role): its emitted code shows what
the forged compiler data does (CI greps it). -/
open RecursionFast

/-- Calls `S7Raw.dec`. -/
def useDec (vk : Fin 1 → K) (x : Stmt) (idx msg : List K) : Bool := S7Raw.dec vk x idx msg

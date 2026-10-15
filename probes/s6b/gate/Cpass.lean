/-
Stage 6b CI regression: a copy of `probes/s7/CpassRegister.lean` with a theorem for the gate to
walk (`cert`). The S7 review probe (S7-M1, second route): a non-module submission file registers a compiler pass
installer. `@[cpass]` entries are evaluated by every importer (`passManagerExt.addImportedFn`), so
they run when the badge executable's main module is compiled, and they rewrite its code. Gate rule
3 lists `implemented_by`, `extern`, `export`, `init`, `csimp`, not `cpass`. This installer is a
no-op; the probe only shows that the attribute is accepted outside the module system.
-/
import Lean
open Lean Compiler.LCNF
/-- A no-op compiler pass installer, registered by a "submission" module. -/
@[cpass] def noopInstaller : PassInstaller := { phase := .base, install := fun ps => pure ps }

/-- A certificate for the gate to walk. -/
theorem cert : True := trivial

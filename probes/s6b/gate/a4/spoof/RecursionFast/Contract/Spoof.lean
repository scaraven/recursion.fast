import RecursionFast.Contract
/-! v0.3 gate test: a solution module that *names itself* like a trusted contract module
(`RecursionFast.Contract.Spoof`) and hides compiled code behind `implemented_by`. A name-prefix
trust rule skips it; the gate trusts contract modules only if they are reachable by imports from
the root `RecursionFast.Contract`. (A spoofed `Mathlib.*` name does not even resolve: Lean maps a
module prefix to one search-path root.) -/
open RecursionFast
def provedImage : Image := ⟨[0x00000293, 0x00100513, 0x00000073], []⟩
def shownImage : Image := ⟨[0x00000013, 0x00000293, 0x00100513, 0x00000073], []⟩
@[implemented_by shownImage] def spoofImage : Image := provedImage

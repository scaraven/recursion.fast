import RecursionFast.Controls.Extractor
/-! S4 review probe: edge cases of the trimmed machine's memory map and `HALT` (S4-A3, S4-A4),
kernel-checked on small images (`probes/s4/asm/edge_*.S`, `-march=rv64im_zbc_zicsr_zicntr`),
and the round-0 decoder on a short output. None is a defect; they pin what an image can and
cannot reach. -/

namespace RecursionFast.Probe.Edge
open RecursionFast

/-- An output region that wraps past `2^64` reads the last tape word (zero beyond the input), then
data word 0: an output is always contract input, image data, written memory or zero. -/
theorem halt_wraps : run ⟨[0xff800513, 0x00200593, 0x00000293, 0x00000073], [42]⟩ [7] 100 =
    some [0, 42] := by decide +kernel

/-- Harvard: a load at `CODE_BASE` reads data memory (here zero), not the instruction there. -/
theorem code_invisible : run ⟨[0x00100313, 0x00c31313, 0x00033383, 0x00703023, 0x00000513,
    0x00100593, 0x00000293, 0x00000073], []⟩ [] 100 = some [0] := by decide +kernel

/-- A byte store at `2^63 - 1`, the last data byte, is allowed. -/
theorem sb_below_tape : run ⟨[0x00100313, 0x03f31313, 0x07f00393, 0xfe730fa3, 0xff830513,
    0x00100593, 0x00000293, 0x00000073], []⟩ [] 100 = some [0x7f00000000000000] := by
  decide +kernel

/-- A byte store at `2^63` faults. -/
theorem sb_tape : run ⟨[0x00100313, 0x03f31313, 0x07f00393, 0x00730023, 0x00000513, 0x00000293,
    0x00000073], []⟩ [] 100 = none := by decide +kernel

/-- A store at `0 - 8`, which wraps to `2^64 - 8`, is in the tape and faults. -/
theorem sd_wrapped : run ⟨[0x00100393, 0xfe703c23, 0x00000293, 0x00000073], []⟩ [] 100 = none := by
  decide +kernel

/-- `FENCE` is a no-op; `EBREAK` and a CSR read (`rdcycle`) are not decoded, so they trap. -/
theorem fence_ebreak_csr :
    run ⟨[0x0ff0000f, 0x00000293, 0x00000073], []⟩ [] 100 = some [] ∧
    run ⟨[0x00100073], []⟩ [] 100 = none ∧ run ⟨[0xc0002573], []⟩ [] 100 = none := by
  decide +kernel

/-- Before round 0 a short output decodes to tables whose missing cells are zero: `[5]` gives a
first table of height 5 and a second of height 0. The decoder adds no information (zeros), and
`relK` bounds the cells (`rows · cols ≤ 2^k`), so this expansion is harmless. -/
theorem decTables_short : (decTables [32, 1] [5]).map Table.rows = [5, 0] := rfl

/-- Every call starts afresh: the run is a function of the image, the tape and the fuel only. -/
theorem run_fresh (img : Image) (t : List Word) (f : ℕ) :
    run img t f = execute img f (initState img t) := rfl

end RecursionFast.Probe.Edge

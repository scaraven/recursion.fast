# Extractor size-bound control (Controls/Extractor.lean): output 2^33 words from address 0
# (more than witCap 20 = 2^32). `long32` (the same with `slli a1, a1, 32`) outputs exactly 2^32.
  addi a1, x0, 1
  slli a1, a1, 33      # a1 = 2^33 (a0 = 0 already)
  addi t0, x0, 0       # HALT
  ecall

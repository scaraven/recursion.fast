# Extractor size-bound control (Controls/Extractor.lean): output exactly 2^32 = witCap 20 words.
  addi a1, x0, 1
  slli a1, a1, 32      # a1 = 2^32 (a0 = 0 already)
  addi t0, x0, 0       # HALT
  ecall

# Extractor control and toy extractor (Controls/Extractor.lean): output tape section 3 (the first
# transcript round) in place, without copying.
  addi t1, x0, 1
  slli t1, t1, 63      # t1 = TAPE_BASE
  ld   a0, 56(t1)      # a0 = start of section 3 (tape word 7)
  ld   a1, 64(t1)      # a1 = length of section 3 (tape word 8)
  slli a0, a0, 3
  add  a0, a0, t1      # a0 = its address
  addi t0, x0, 0       # HALT
  ecall

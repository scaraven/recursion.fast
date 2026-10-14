# Machine control (Controls/Extractor.lean): a W-op and Zbc, output from data memory.
  addi   t1, x0, -1      # t1 = 2^64 - 1
  addw   t3, t1, t1      # (-1) + (-1) on 32 bits, sign-extended: 0xffff_ffff_ffff_fffe
  clmulh t4, t1, t1      # high word of the carry-less square: 0x5555_5555_5555_5555
  sd     t3, 0(x0)
  sd     t4, 8(x0)
  addi   a1, x0, 2       # output 2 words from address 0
  addi   t0, x0, 0
  ecall

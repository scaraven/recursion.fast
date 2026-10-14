# Extractor negative control (Controls/Extractor.lean): brute force. Find the least c with
# clmul(c, 0x1b) = x_0 (the first statement word) by trying c = 0, 1, 2, ...; 4 steps per
# candidate that fails.
  addi t1, x0, 1
  slli t1, t1, 63      # t1 = TAPE_BASE
  ld   t2, 40(t1)      # start of section 2 (the statement x, tape word 5)
  slli t2, t2, 3
  add  t2, t2, t1
  ld   t3, 0(t2)       # t3 = x_0
  addi t4, x0, 0       # c = 0
  addi t5, x0, 0x1b
loop:
  clmul t6, t4, t5
  beq  t6, t3, found
  addi t4, t4, 1
  jal  x0, loop
found:
  sd   t4, 0(x0)       # output c from address 0
  addi a0, x0, 0
  addi a1, x0, 1
  addi t0, x0, 0       # HALT
  ecall

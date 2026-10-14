# S4 review probe (ChainBudget.lean): brute force resumed across extractor calls. The search
# state travels in the witness section w (the last tape section), as [flag, c]:
#   w = []      : start at c = 0;
#   w = [0, c]  : candidates below c failed, resume at c;
#   w = [1, c]  : c was found, pass it on.
# Each call tries at most T = 4 candidates c, c+1, ..., c+3 against x_0 (statement word 0) with
# the test clmul(c, 0x1b) = x_0, and outputs [1, c] (found) or [0, c+4] (give up), from address 0.
  addi t1, x0, 1
  slli t1, t1, 63        # t1 = TAPE_BASE
  ld   t2, 40(t1)        # start of section 2 (the statement x, tape word 5)
  slli t2, t2, 3
  add  t2, t2, t1
  ld   t3, 0(t2)         # t3 = x_0
  ld   t2, 0(t1)         # t2 = number of sections N
  slli a2, t2, 4
  add  a2, a2, t1        # a2 = address of tape word 2N (length of the last section, w)
  ld   a3, 0(a2)         # a3 = |w|
  addi t4, x0, 0         # c = 0
  beq  a3, x0, start     # w = []: start at 0
  ld   a7, -8(a2)        # a7 = start of w (tape word 2N-1)
  slli a7, a7, 3
  add  a7, a7, t1        # a7 = address of w[0]
  ld   a6, 0(a7)         # a6 = flag
  ld   t4, 8(a7)         # c = w[1]
  bne  a6, x0, found     # already found: pass it on
start:
  addi t5, x0, 0x1b
  addi a4, t4, 4         # a4 = c + T
loop:
  beq  t4, a4, giveup
  clmul t6, t4, t5
  beq  t6, t3, found
  addi t4, t4, 1
  jal  x0, loop
found:
  addi a5, x0, 1
  jal  x0, out
giveup:
  addi a5, x0, 0
out:
  sd   a5, 0(x0)
  sd   t4, 8(x0)
  addi a0, x0, 0
  addi a1, x0, 2
  addi t0, x0, 0         # HALT
  ecall

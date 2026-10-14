# S4 review probe (MachineEdge.lean): a load at CODE_BASE reads data memory, not the code.
  addi t1, x0, 1
  slli t1, t1, 12      # t1 = 0x1000 = CODE_BASE
  ld   t2, 0(t1)
  sd   t2, 0(x0)
  addi a0, x0, 0
  addi a1, x0, 1
  addi t0, x0, 0       # HALT
  ecall

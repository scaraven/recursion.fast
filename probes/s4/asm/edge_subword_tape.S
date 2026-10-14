# S4 review probe (MachineEdge.lean): a byte store at 2^63 faults.
  addi t1, x0, 1
  slli t1, t1, 63
  addi t2, x0, 0x7f
  sb   t2, 0(t1)
  addi a0, x0, 0
  addi t0, x0, 0
  ecall

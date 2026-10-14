# S4 review probe (MachineEdge.lean): a store at 0 - 8 = 2^64 - 8 (wrapped) is in the tape: fault.
  addi t2, x0, 1
  sd   t2, -8(x0)
  addi t0, x0, 0
  ecall

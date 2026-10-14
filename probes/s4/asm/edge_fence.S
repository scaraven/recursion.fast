# S4 review probe (MachineEdge.lean): FENCE is a no-op.
  fence
  addi t0, x0, 0       # HALT
  ecall

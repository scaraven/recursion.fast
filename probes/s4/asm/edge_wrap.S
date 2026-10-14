# S4 review probe (MachineEdge.lean): an output region that wraps past 2^64 reads the last tape
# word (zero beyond the input) and then data word 0; nothing else is reachable.
  addi a0, x0, -8      # a0 = 2^64 - 8
  addi a1, x0, 2
  addi t0, x0, 0       # HALT
  ecall

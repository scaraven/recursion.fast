# S4 review probe (MachineEdge.lean): a byte store at 2^63 - 1 (the last data byte) is allowed and
# lands in the doubleword at 2^63 - 8; a byte store at 2^63 faults (edge_subword_tape).
  addi t1, x0, 1
  slli t1, t1, 63      # t1 = TAPE_BASE
  addi t2, x0, 0x7f
  sb   t2, -1(t1)
  addi a0, t1, -8
  addi a1, x0, 1
  addi t0, x0, 0       # HALT
  ecall

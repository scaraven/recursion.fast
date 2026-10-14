# Machine negative control (Controls/Extractor.lean): a store into the tape faults.
  addi t1, x0, 1
  slli t1, t1, 63      # t1 = TAPE_BASE
  sd   x0, 0(t1)
  addi t0, x0, 0
  ecall

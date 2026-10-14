# Extractor control (Controls/Extractor.lean): copy the last tape section (the witness `w`)
# into data memory at 0x100 and output it from there.
  addi t1, x0, 1
  slli t1, t1, 63      # t1 = TAPE_BASE
  ld   t2, 0(t1)       # t2 = number of sections N
  slli t3, t2, 4       # t3 = 16 N
  add  t3, t3, t1      # t3 = address of tape word 2N (length of section N-1)
  ld   a1, 0(t3)       # a1 = |w|
  ld   t4, -8(t3)      # t4 = start of w (tape word 2N-1)
  slli t4, t4, 3
  add  t4, t4, t1      # t4 = address of w[0]
  addi a0, x0, 0x100   # a0 = destination
  addi t5, a0, 0       # t5 = write pointer
  addi t6, a1, 0       # t6 = words left
loop:
  beq  t6, x0, done
  ld   s1, 0(t4)
  sd   s1, 0(t5)
  addi t4, t4, 8
  addi t5, t5, 8
  addi t6, t6, -1
  jal  x0, loop
done:
  addi t0, x0, 0       # HALT
  ecall

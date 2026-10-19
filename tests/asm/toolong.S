# Output cap control (Controls/Extractor.lean): HALT with 2^24 + 1 output words (a0 = 0), one
# more than the contract's `outCap`.
  lui  a1, 0x1000      # a1 = 2^24
  addi a1, a1, 1       # a1 = 2^24 + 1
  ecall                # t0 = 0: HALT

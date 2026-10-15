# The baseline's extractor image (RecursionFast/Library/Extractor.lean, `firstMsgImg`): output the
# first transcript round in place. The contract's input tape (Contract/Extractor.lean, `frame`) is
# a directory, then the sections [j], L, x, round 0, ...; section 3 (round 0) starts at the word
# stored in tape word 7 and has the length stored in tape word 8. HALT (ECALL with t0 = 0) returns
# the a1 doublewords from address a0. Eight instructions, eight steps; no data words.
    .text
    .globl _start
_start:
    addi  t1, zero, 1        # t1 = 1
    slli  t1, t1, 63         # t1 = 2^63 = TAPE_BASE
    ld    a0, 56(t1)         # a0 = tape[7]: first word of round 0
    ld    a1, 64(t1)         # a1 = tape[8]: its length in words
    slli  a0, a0, 3          # a0 = 8 * start
    add   a0, a0, t1         # a0 = TAPE_BASE + 8 * start
    addi  t0, zero, 0        # t0 = 0: HALT
    ecall

.section .init
.global main

/* set stack pointer */
lui sp, %hi(512)
addi sp, sp, %lo(512)

/* call main */
jal ra, main

/* break */
ebreak

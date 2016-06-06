.section .init
.global main

/* set stack pointer */
lui sp, %hi(16*1024)
addi sp, sp, %lo(16*1024)

/* call main */
jal ra, main

/* break */
ebreak

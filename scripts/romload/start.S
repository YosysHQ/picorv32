.section .text
.global _start
.global _pvstart
.global _data
.global _data_lma

_pvstart:
/* zero-initialize all registers */
addi x1, zero, 0
addi x2, zero, 0
addi x3, zero, 0
addi x4, zero, 0
addi x5, zero, 0
addi x6, zero, 0
addi x7, zero, 0
addi x8, zero, 0
addi x9, zero, 0
addi x10, zero, 0
addi x11, zero, 0
addi x12, zero, 0
addi x13, zero, 0
addi x14, zero, 0
addi x15, zero, 0
addi x16, zero, 0
addi x17, zero, 0
addi x18, zero, 0
addi x19, zero, 0
addi x20, zero, 0
addi x21, zero, 0
addi x22, zero, 0
addi x23, zero, 0
addi x24, zero, 0
addi x25, zero, 0
addi x26, zero, 0
addi x27, zero, 0
addi x28, zero, 0
addi x29, zero, 0
addi x30, zero, 0
addi x31, zero, 0

/* set stack pointer */

lui sp, %hi(4*1024*1024)
addi sp, sp, %lo(4*1024*1024)
/*
lui sp, %hi(0x100000)
addi sp, sp, %lo(0x100000)
*/
/* push zeros on the stack for argc and argv */
/* (stack is aligned to 16 bytes in riscv calling convention) */
addi sp,sp,-16
sw zero,0(sp)
sw zero,4(sp)
sw zero,8(sp)
sw zero,12(sp)

/*
	// Load data section 
	la a0, _data_lma
	la a1, _data
	la a2, _edata
	bgeu a1, a2, 2f
1:
	lw t0, (a0)
	sw t0, (a1)
	addi a0, a0, 4
	addi a1, a1, 4
	bltu a1, a2, 1b
2:

	// Clear bss section
	la a0, _bss_start
	la a1, _bss_end
	bgeu a0, a1, 2f
1:
	sw zero, (a0)
	addi a0, a0, 4
	bltu a0, a1, 1b
2:
*/


/* jump to libc init */
/*j _ftext
 */
j _start

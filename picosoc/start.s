.section .text

start:
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

li sp, 4*256
call main
j start

.global cmd_read_spi_flash_id_worker_begin
.global cmd_read_spi_flash_id_worker_end

cmd_read_spi_flash_id_worker_begin:
li t0,0x02000008
li t1,'F'
sw t1,0(t0)
li t1,'I'
sw t1,0(t0)
li t1,'X'
sw t1,0(t0)
li t1,'M'
sw t1,0(t0)
li t1,'E'
sw t1,0(t0)
li t1,'\r'
sw t1,0(t0)
li t1,'\n'
sw t1,0(t0)
ret
cmd_read_spi_flash_id_worker_end:


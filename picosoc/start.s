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

loop:
j loop

.global cmd_read_spi_flash_id_worker_begin
.global cmd_read_spi_flash_id_worker_end

cmd_read_spi_flash_id_worker_begin:

# address of SPI ctrl reg
li t0, 0x02000000

# Manual Ctrl
li t1, 0x00
sb t1, 3(t0)

# CS high, IO0 is output
li t1, 0x120
sh t1, 0(t0)

# CS low
sb zero, 0(t0)

# Send 0x9F (EDEC-ID Read)
li t2, 0x9F
li t3, 8
cmd_read_spi_flash_id_worker_L1:
srli t4, t2, 7
andi t4, t4, 0x01
sb   t4, 0(t0)
ori  t4, t4, 0x10
slli t2, t2, 1
addi t3, t3, -1
sb   t4, 0(t0)
bnez t3, cmd_read_spi_flash_id_worker_L1

# Read 16 bytes and store in zero page
li   t3, 0
li   a2, 16
cmd_read_spi_flash_id_worker_L2:
li   a0, 8
li   a1, 0
cmd_read_spi_flash_id_worker_L3:
sb   zero, 0(t0)
li   t4, 0x10
sb   t4, 0(t0)
lb   t4, 0(t0)
andi t4, t4, 2
srli t4, t4, 1
slli a1, a1, 1
or   a1, a1, t4
addi a0, a0, -1
bnez a0, cmd_read_spi_flash_id_worker_L3
sb   a1, 0(t3)
addi t3, t3, 1
bne  t3, a2, cmd_read_spi_flash_id_worker_L2

# back to MEMIO mode
li t1, 0x80
sb t1, 3(t0)

ret
cmd_read_spi_flash_id_worker_end:


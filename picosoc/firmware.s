# write RAM code (a sequence of nops followed by ret)
li      x5,0x00000013   # nop
sw      x5,4(x0)
sw      x5,8(x0)
sw      x5,12(x0)
sw      x5,16(x0)
sw      x5,20(x0)
sw      x5,24(x0)
sw      x5,28(x0)
sw      x5,32(x0)
sw      x5,36(x0)
sw      x5,40(x0)
sw      x5,44(x0)
sw      x5,48(x0)
sw      x5,52(x0)
sw      x5,56(x0)
sw      x5,60(x0)
sw      x5,64(x0)
sw      x5,68(x0)
sw      x5,72(x0)
sw      x5,76(x0)
sw      x5,80(x0)
sw      x5,84(x0)
sw      x5,88(x0)
sw      x5,92(x0)
sw      x5,96(x0)
sw      x5,100(x0)
sw      x5,104(x0)
sw      x5,108(x0)
sw      x5,112(x0)
sw      x5,116(x0)
sw      x5,120(x0)
sw      x5,124(x0)
sw      x5,128(x0)
sw      x5,132(x0)
sw      x5,136(x0)
sw      x5,140(x0)
sw      x5,144(x0)
sw      x5,148(x0)
sw      x5,152(x0)
sw      x5,156(x0)
sw      x5,160(x0)
sw      x5,164(x0)
sw      x5,168(x0)
sw      x5,172(x0)
sw      x5,176(x0)
sw      x5,180(x0)
sw      x5,184(x0)
sw      x5,188(x0)
sw      x5,192(x0)
li      x5,0x00008067   # ret
sw      x5,196(x0)

# setup gpio address in x5
li      x5,0x03000000
sw      x0,0(x5)

# initial entry point into RAM code
li      x3,4

# initialize RAM counter
sw      x0,0(x0)

# start of loop. remember this address
auipc   x4,0

# execute RAM code, come back here
jalr    x3

# load counter and increment
lw      x6,0(x0)
addi    x6,x6,1

# store counter and update gpios
sw      x6,0(x5)
sw      x6,0(x0)

# calculate new entry point into RAM code
slli    x3,x6,2
andi    x3,x3,127
addi    x3,x3,32

# execute RAM code, come back to start of loop
mv      x1,x4
jr      x3

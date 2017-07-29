start:
      li      x1,0xc0000000
      sw      x0,0(x0)
loop: lw      x2,0(x0)
      addi    x2,x2,1
      sw      x2,0(x1)
      sw      x2,0(x0)
      j       loop

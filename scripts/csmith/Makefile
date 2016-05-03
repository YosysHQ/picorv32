RISCV_TOOLS_PREFIX = /opt/riscv32imc/bin/riscv32-unknown-elf-
CSMITH_INCDIR = $(shell ls -d /usr/local/include/csmith-* | head -n1)
CC = $(RISCV_TOOLS_PREFIX)gcc

run: test.exe test.hex testbench.exe
	./test.exe | tee output_ref.txt
	vvp -N testbench.exe | tee output_sim.txt
	diff -u output_ref.txt output_sim.txt

testbench.exe: testbench.v ../../picorv32.v
	iverilog -o testbench.exe testbench.v ../../picorv32.v
	chmod -x testbench.exe

test.hex: start.elf test.elf
	$(RISCV_TOOLS_PREFIX)objcopy -O verilog start.elf start.tmp
	$(RISCV_TOOLS_PREFIX)objcopy -O verilog test.elf test.tmp
	cat start.tmp test.tmp > test.hex
	rm -f start.tmp test.tmp

start.elf: start.S start.ld
	$(CC) -nostdlib -o start.elf start.S -T start.ld
	chmod -x start.elf

test.exe: test.c
	gcc -m32 -o test.exe -w -Os -I $(CSMITH_INCDIR) test.c

test.elf: test.c
	$(CC) -o test.elf -w -Os -I $(CSMITH_INCDIR) test.c syscalls.c
	chmod -x test.elf

test.c:
	echo "integer size = 4" > platform.info
	echo "pointer size = 4" >> platform.info
	csmith -o test.c

clean:
	rm -f platform.info test.c test.elf start.elf test.hex test.exe
	rm -f testbench.exe testbench.vcd output_ref.txt output_sim.txt


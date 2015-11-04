CXX = riscv32-unknown-elf-g++
CC = riscv32-unknown-elf-gcc
AS = riscv32-unknown-elf-gcc
CXXFLAGS = -MD -Os -Wall -std=c++11
CCFLAGS = -MD -Os -Wall -std=c++11
LDFLAGS = -Wl,--gc-sections
LDLIBS = -lstdc++

test: testbench.exe firmware.hex
	vvp -N testbench.exe

testbench.exe: testbench.v ../../picorv32.v
	iverilog -o testbench.exe testbench.v ../../picorv32.v
	chmod -x testbench.exe

firmware.hex: firmware.elf start.elf
	riscv32-unknown-elf-objcopy -O verilog start.elf start.tmp
	riscv32-unknown-elf-objcopy -O verilog firmware.elf firmware.tmp
	cat start.tmp firmware.tmp > firmware.hex
	rm -f start.tmp firmware.tmp

firmware.elf: firmware.o syscalls.o
	$(CC) $(LDFLAGS) -o $@ $^ $(LDLIBS)
	chmod -x firmware.elf

start.elf: start.S start.ld
	$(CC) -nostdlib -o start.elf start.S -T start.ld $(LDLIBS)
	chmod -x start.elf

clean:
	rm -f *.o *.d *.tmp start.elf
	rm -f firmware.elf firmware.hex
	rm -f testbench.exe testbench.vcd

-include *.d
.PHONY: test clean

ifndef RISCV_TOOLS_PREFIX
RISCV_TOOLS_PREFIX = /opt/riscv32ic/bin/riscv32-unknown-elf-
endif
CXX = $(RISCV_TOOLS_PREFIX)g++ -march=rv32i
CC = $(RISCV_TOOLS_PREFIX)gcc -march=rv32i
AS = $(RISCV_TOOLS_PREFIX)gcc -march=rv32i
CXXFLAGS = -MD -Os -Wall -std=c++11
CCFLAGS = -MD -Os -Wall
#LDFLAGS = -Wl,--gc-sections,--no-relax
LDFLAGS = -Wl,--gc-sections
LDLIBS =

test: testbench.vvp firmware32.hex
	vvp -l testbench.log -N testbench.vvp

testbench.vvp: testbench.v ../../picorv32.v firmware_dbg.v
	iverilog -D WRITE_VCD=1 -o testbench.vvp testbench.v ../../picorv32.v
	chmod -x testbench.vvp

firmware32.hex: firmware.elf hex8tohex32.py
	$(RISCV_TOOLS_PREFIX)objcopy -O verilog firmware.elf firmware.tmp
	python3 hex8tohex32.py firmware.tmp > firmware32.hex

#firmware32.hex: firmware.elf start.elf hex8tohex32.py
#	$(RISCV_TOOLS_PREFIX)objcopy -O verilog start.elf start.tmp
#	$(RISCV_TOOLS_PREFIX)objcopy -O verilog firmware.elf firmware.tmp
#	cat start.tmp firmware.tmp > firmware.hex
#	python3 hex8tohex32.py firmware.hex > firmware32.hex
#	rm -f start.tmp firmware.tmp

firmware_dbg.v: firmware.map
	python3 map2debug.py
#firmware.o: firmware.c
#	$(CC) -c $^

start.o: start.S
	$(CC) -c -nostdlib start.S $(LDLIBS)

firmware.elf: firmware.o syscalls.o start.o
	$(CC) $(LDFLAGS),-Map=firmware.map -o $@ $^ -T sections.lds $(LDLIBS)
	chmod -x firmware.elf

start.elf: start.S start.ld
	$(CC) -nostdlib -o start.elf start.S -T start.ld $(LDLIBS)
	chmod -x start.elf

clean:
	rm -f *.o *.d *.tmp start.elf
	rm -f firmware.elf firmware.hex firmware32.hex
	rm -f testbench.vvp testbench.vcd

-include *.d
.PHONY: test clean


TOOLCHAIN_PREFIX = /opt/riscv32ic/bin/riscv32-unknown-elf-

run: testbench.vvp firmware.hex
	vvp -N testbench.vvp

firmware.hex: firmware.S firmware.c firmware.lds
	$(TOOLCHAIN_PREFIX)gcc -Os -ffreestanding -nostdlib -o firmware.elf firmware.S firmware.c \
		 --std=gnu99 -Wl,-Bstatic,-T,firmware.lds,-Map,firmware.map,--strip-debug -lgcc
	$(TOOLCHAIN_PREFIX)objcopy -O binary firmware.elf firmware.bin
	python3 ../../firmware/makehex.py firmware.bin 4096 > firmware.hex

picorv32_presyn.v: picorv32_presyn.ys picorv32_regs.txt ../../picorv32.v
	yosys -v0 picorv32_presyn.ys

testbench.vvp: testbench.v picorv32_presyn.v
	iverilog -o testbench.vvp testbench.v picorv32_presyn.v

clean:
	rm -f firmware.bin firmware.elf firmware.hex firmware.map
	rm -f picorv32_presyn.v testbench.vvp testbench.vcd


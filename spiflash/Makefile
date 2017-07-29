
test: testbench.vvp firmware.hex
	vvp -N $<

prog: design.bin firmware.bin
	iceprog design.bin
	iceprog -o 1M firmware.bin

testbench.vvp: spiflash.v spimemio.v testbench.v top.v ../picorv32.v
	iverilog -s testbench -o $@ $^

firmware.elf: firmware.s
	riscv32-unknown-elf-gcc -c -o firmware.elf firmware.s

firmware_vma.elf: firmware.elf
	riscv32-unknown-elf-objcopy --change-section-vma .text=0x00100000 firmware.elf firmware_vma.elf

firmware.hex: firmware_vma.elf
	riscv32-unknown-elf-objcopy -O verilog firmware_vma.elf firmware.hex

firmware.bin: firmware.elf
	riscv32-unknown-elf-objcopy -O binary firmware.elf firmware.bin

design.blif: spimemio.v top.v ../picorv32.v
	yosys -ql design.log -p 'synth_ice40 -top top -blif design.blif' $^

design.asc: pinout.pcf design.blif
	arachne-pnr -d 8k -o design.asc -p pinout.pcf design.blif

design.bin: design.asc
	icetime -d hx8k -c 12 -mtr design.rpt design.asc
	icepack design.asc design.bin

clean:
	rm -f testbench.vvp testbench.vcd
	rm -f firmware.elf firmware_vma.elf firmware.hex firmware.bin
	rm -f design.blif design.log design.asc design.rpt design.bin

.PHONY: test prog clean


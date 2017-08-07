
# ---- Generic Testbenches ----

testbench: testbench.vvp firmware.hex
	vvp -N $<

testbench.vvp: spiflash.v spimemio.v testbench.v picosoc.v ../picorv32.v
	iverilog -s testbench -o $@ $^

spiflash_tb: spiflash_tb.vvp firmware.hex
	vvp -N $<

spiflash_tb.vvp: spiflash.v spiflash_tb.v
	iverilog -s testbench -o $@ $^

# ---- iCE40 HX8K Breakout Board ----

hx8kprog: hx8kdemo.bin firmware.bin
	iceprog hx8kdemo.bin
	iceprog -o 1M firmware.bin

hx8kdemo.blif: hx8kdemo.v spimemio.v picosoc.v ../picorv32.v
	yosys -ql hx8kdemo.log -p 'synth_ice40 -top hx8kdemo -blif hx8kdemo.blif' $^

hx8kdemo.asc: hx8kdemo.pcf hx8kdemo.blif
	arachne-pnr -d 8k -o hx8kdemo.asc -p hx8kdemo.pcf hx8kdemo.blif

hx8kdemo.bin: hx8kdemo.asc
	icetime -d hx8k -c 12 -mtr hx8kdemo.rpt hx8kdemo.asc
	icepack hx8kdemo.asc hx8kdemo.bin

# ---- Example Firmware ----

firmware.elf: firmware.s
	riscv32-unknown-elf-gcc -c -o firmware.elf firmware.s

firmware_vma.elf: firmware.elf
	riscv32-unknown-elf-objcopy --change-section-vma .text=0x00100000 firmware.elf firmware_vma.elf

firmware.hex: firmware_vma.elf
	riscv32-unknown-elf-objcopy -O verilog firmware_vma.elf firmware.hex

firmware.bin: firmware.elf
	riscv32-unknown-elf-objcopy -O binary firmware.elf firmware.bin

# ---- Clean ----

clean:
	rm -f testbench.vvp testbench.vcd spiflash_tb.vvp spiflash_tb.vcd
	rm -f firmware.elf firmware_vma.elf firmware.hex firmware.bin
	rm -f hx8kdemo.blif hx8kdemo.log hx8kdemo.asc hx8kdemo.rpt hx8kdemo.bin

.PHONY: testbench spiflash_tb hx8kprog clean


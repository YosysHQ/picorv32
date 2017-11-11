
# ---- iCE40 HX8K Breakout Board ----

hx8ksim: hx8kdemo_tb.vvp firmware.hex
	vvp -N $<

hx8ksynsim: hx8kdemo_syn_tb.vvp firmware.hex
	vvp -N $<

hx8kdemo.blif: hx8kdemo.v spimemio.v simpleuart.v picosoc.v ../picorv32.v
	yosys -ql hx8kdemo.log -p 'synth_ice40 -top hx8kdemo -blif hx8kdemo.blif' $^

hx8kdemo_tb.vvp: hx8kdemo_tb.v hx8kdemo.v spimemio.v simpleuart.v picosoc.v ../picorv32.v spiflash.v
	iverilog -s testbench -o $@ $^ `yosys-config --datdir/ice40/cells_sim.v`

hx8kdemo_syn_tb.vvp: hx8kdemo_tb.v hx8kdemo_syn.v spiflash.v
	iverilog -s testbench -o $@ $^ `yosys-config --datdir/ice40/cells_sim.v`

hx8kdemo_syn.v: hx8kdemo.blif
	yosys -p 'read_blif -wideports hx8kdemo.blif; write_verilog hx8kdemo_syn.v'

hx8kdemo.asc: hx8kdemo.pcf hx8kdemo.blif
	arachne-pnr -d 8k -o hx8kdemo.asc -p hx8kdemo.pcf hx8kdemo.blif

hx8kdemo.bin: hx8kdemo.asc
	icetime -d hx8k -c 12 -mtr hx8kdemo.rpt hx8kdemo.asc
	icepack hx8kdemo.asc hx8kdemo.bin

hx8kprog: hx8kdemo.bin firmware.bin
	iceprog hx8kdemo.bin
	iceprog -o 1M firmware.bin

hx8kprog_fw: firmware.bin
	iceprog -o 1M firmware.bin

# ---- Example Firmware ----

firmware.elf: sections.lds start.s firmware.c
	riscv32-unknown-elf-gcc -march=rv32imc -Wl,-Bstatic,-T,sections.lds,--strip-debug -ffreestanding -nostdlib -o firmware.elf start.s firmware.c

firmware.hex: firmware.elf
	riscv32-unknown-elf-objcopy -O verilog firmware.elf /dev/stdout | sed -e '1 s/@00000000/@00100000/; 2,65537 d;' > firmware.hex

firmware.bin: firmware.elf
	riscv32-unknown-elf-objcopy -O binary firmware.elf /dev/stdout | tail -c +1048577 > firmware.bin

# ---- Testbench for SPI Flash Model ----

spiflash_tb: spiflash_tb.vvp firmware.hex
	vvp -N $<

spiflash_tb.vvp: spiflash.v spiflash_tb.v
	iverilog -s testbench -o $@ $^

# ---- ASIC Synthesis Tests ----

cmos.log: spimemio.v simpleuart.v picosoc.v ../picorv32.v
	yosys -l cmos.log -p 'synth -top picosoc; abc -g cmos2; opt -fast; stat' $^

# ---- Clean ----

clean:
	rm -f testbench.vvp testbench.vcd spiflash_tb.vvp spiflash_tb.vcd
	rm -f firmware.elf firmware.hex firmware.bin cmos.log
	rm -f hx8kdemo.blif hx8kdemo.log hx8kdemo.asc hx8kdemo.rpt hx8kdemo.bin
	rm -f hx8kdemo_syn.v hx8kdemo_syn_tb.vvp hx8kdemo_tb.vvp

.PHONY: spiflash_tb hx8kprog hx8kprog_fw hx8ksim hx8ksynsim clean


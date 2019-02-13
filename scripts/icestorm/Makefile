TOOLCHAIN_PREFIX = riscv32-unknown-elf-

ICE40_SIM_CELLS=$(shell yosys-config --datdir/ice40/cells_sim.v)

# set to 4 for simulation
FIRMWARE_COUNTER_BITS=18

all: example.bin

## -------------------
## firmware generation

firmware.elf: firmware.S firmware.c firmware.lds
	$(TOOLCHAIN_PREFIX)gcc \
		-DSHIFT_COUNTER_BITS=$(FIRMWARE_COUNTER_BITS) \
		-march=rv32i -Os -ffreestanding -nostdlib \
		-o $@ firmware.S firmware.c \
		--std=gnu99 -Wl,-Bstatic,-T,firmware.lds,-Map,firmware.map,--strip-debug
	chmod -x $@

firmware.bin: firmware.elf
	$(TOOLCHAIN_PREFIX)objcopy -O binary $< $@
	chmod -x $@

firmware.hex: firmware.bin
	python3 ../../firmware/makehex.py $< 128 > $@

## ------------------------------
## main flow: synth/p&r/bitstream

synth.json: example.v ../../picorv32.v firmware.hex
	yosys -v3 -l synth.log -p 'synth_ice40 -top top -json $@; write_verilog -attr2comment synth.v' $(filter %.v, $^)

example.asc: synth.json example.pcf
	nextpnr-ice40 --hx8k --package ct256 --json $< --pcf example.pcf --asc $@

example.bin: example.asc
	icepack $< $@

## -----------------
## icarus simulation

example_tb.vvp: example.v example_tb.v ../../picorv32.v firmware.hex
	iverilog -o $@ -s testbench $(filter %.v, $^)
	chmod -x $@

example_sim: example_tb.vvp
	vvp -N $<

example_sim_vcd: example_tb.vvp
	vvp -N $< +vcd

## ---------------------
## post-synth simulation

synth_tb.vvp: example_tb.v synth.json
	iverilog -o $@ -s testbench synth.v example_tb.v $(ICE40_SIM_CELLS)
	chmod -x $@

synth_sim: synth_tb.vvp
	vvp -N $<

synth_sim_vcd: synth_tb.vvp
	vvp -N $< +vcd

## ---------------------
## post-route simulation

route.v: example.asc example.pcf
	icebox_vlog -L -n top -sp example.pcf $< > $@

route_tb.vvp: route.v example_tb.v
	iverilog -o $@ -s testbench $^ $(ICE40_SIM_CELLS)
	chmod -x $@

route_sim: route_tb.vvp
	vvp -N $<

route_sim_vcd: route_tb.vvp
	vvp -N $< +vcd

## ---------------------
## miscellaneous targets

prog_sram: example.bin
	iceprog -S $<

timing: example.asc example.pcf
	icetime -c 62 -tmd hx8k -P ct256 -p example.pcf -t $<

view: example.vcd
	gtkwave $< example.gtkw

## ------
## el fin

clean:
	rm -f firmware.elf firmware.map firmware.bin firmware.hex
	rm -f synth.log synth.v synth.json route.v example.asc example.bin
	rm -f example_tb.vvp synth_tb.vvp route_tb.vvp example.vcd

.PHONY: all prog_sram view clean
.PHONY: example_sim synth_sim route_sim timing
.PHONY: example_sim_vcd synth_sim_vcd route_sim_vcd

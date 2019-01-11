
TOOLCHAIN_PREFIX = riscv32-unknown-elf-

all: example.bin

firmware.elf: firmware.S firmware.c firmware.lds
	$(TOOLCHAIN_PREFIX)gcc -Os -ffreestanding -nostdlib -o $@ firmware.S firmware.c \
			--std=gnu99 -Wl,-Bstatic,-T,firmware.lds,-Map,firmware.map,--strip-debug -lgcc
	chmod -x $@

firmware.bin: firmware.elf
	$(TOOLCHAIN_PREFIX)objcopy -O binary $< $@
	chmod -x $@

firmware.hex: firmware.bin
	python3 ../../firmware/makehex.py $< 128 > $@

synth.json: example.v ../../picorv32.v firmware.hex
	yosys -v3 -l synth.log -p 'synth_ice40 -top top -json $@; write_verilog -attr2comment synth.v' $(filter %.v, $^)

example.asc: synth.json example.pcf
	nextpnr-ice40 --hx8k --package ct256 --json $< --pcf example.pcf --asc $@

example.bin: example.asc
	icepack $< $@

example_tb.vvp: example.v example_tb.v ../../picorv32.v firmware.hex
	iverilog -o $@ -s testbench $(filter %.v, $^)
	chmod -x $@

example_sim: example_tb.vvp
	vvp -N $<

example_sim_vcd: example_tb.vvp
	vvp -N $< +vcd

synth_tb.vvp: example_tb.v synth.json
	iverilog -o $@ -s testbench synth.v example_tb.v `yosys-config --datdir/ice40/cells_sim.v`
	chmod -x $@

synth_sim: synth_tb.vvp
	vvp -N $<

synth_sim_vcd: synth_tb.vvp
	vvp -N $< +vcd

route.v: example.asc example.pcf
	icebox_vlog -L -n top -sp example.pcf $< > $@

route_tb.vvp: route.v example_tb.v
	iverilog -o $@ -s testbench $^ `yosys-config --datdir/ice40/cells_sim.v`
	chmod -x $@

route_sim: route_tb.vvp
	vvp -N $<

route_sim_vcd: route_tb.vvp
	vvp -N $< +vcd

prog_sram: example.bin
	iceprog -S $<

view: example.vcd
	gtkwave $< example.gtkw

clean:
	rm -f firmware.elf firmware.map firmware.bin firmware.hex
	rm -f synth.log synth.v synth.json route.v example.asc example.bin
	rm -f example_tb.vvp synth_tb.vvp route_tb.vvp example.vcd

.PHONY: all prog_sram view clean
.PHONY: example_sim synth_sim route_sim
.PHONY: example_sim_vcd synth_sim_vcd route_sim_vcd

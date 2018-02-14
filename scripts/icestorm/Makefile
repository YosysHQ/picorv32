
TOOLCHAIN_PREFIX = riscv32-unknown-elf-

all: example.bin

firmware.elf: firmware.S firmware.c firmware.lds
	$(TOOLCHAIN_PREFIX)gcc -Os -ffreestanding -nostdlib -o firmware.elf firmware.S firmware.c \
			--std=gnu99 -Wl,-Bstatic,-T,firmware.lds,-Map,firmware.map,--strip-debug -lgcc
	chmod -x firmware.elf

firmware.bin: firmware.elf
	$(TOOLCHAIN_PREFIX)objcopy -O binary firmware.elf firmware.bin
	chmod -x firmware.bin

firmware.hex: firmware.bin
	python3 ../../firmware/makehex.py firmware.bin 128 > firmware.hex

synth.blif: example.v ../../picorv32.v firmware.hex
	yosys -v3 -l synth.log -p 'synth_ice40 -top top -blif $@; write_verilog -attr2comment synth.v' $(filter %.v, $^)

example.asc: synth.blif
	arachne-pnr -d 8k -o example.asc -p example.pcf synth.blif

example.bin: example.asc
	icepack example.asc example.bin

example_tb.vvp: example_tb.v example.v firmware.hex
	iverilog -o example_tb.vvp -s testbench example.v example_tb.v ../../picorv32.v
	chmod -x example_tb.vvp

example_sim: example_tb.vvp
	vvp -N example_tb.vvp

example_sim_vcd: example_tb.vvp
	vvp -N example_tb.vvp +vcd

synth_tb.vvp: example_tb.v synth.blif
	iverilog -o synth_tb.vvp -s testbench synth.v example_tb.v `yosys-config --datdir/ice40/cells_sim.v`
	chmod -x synth_tb.vvp

synth_sim: synth_tb.vvp
	vvp -N synth_tb.vvp

synth_sim_vcd: synth_tb.vvp
	vvp -N synth_tb.vvp +vcd

route.v: example.asc
	icebox_vlog -L -n top -sp example.pcf example.asc > route.v

route_tb.vvp: example_tb.v route.v
	iverilog -o route_tb.vvp -s testbench route.v example_tb.v `yosys-config --datdir/ice40/cells_sim.v`
	chmod -x route_tb.vvp

route_sim: route_tb.vvp
	vvp -N route_tb.vvp

route_sim_vcd: route_tb.vvp
	vvp -N route_tb.vvp +vcd

prog_sram:
	iceprog -S example.bin

view:
	gtkwave example.vcd example.gtkw

clean:
	rm -f firmware.elf firmware.map firmware.bin firmware.hex
	rm -f synth.log synth.v synth.blif route.v example.asc example.bin
	rm -f example_tb.vvp synth_tb.vvp route_tb.vvp example.vcd

.PHONY: all prog_sram view clean
.PHONY: example_sim synth_sim route_sim
.PHONY: example_sim_vcd synth_sim_vcd route_sim_vcd


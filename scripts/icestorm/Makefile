
TOOLCHAIN_PREFIX = riscv64-unknown-elf-

all: example.bin

firmware.elf: firmware.S firmware.c firmware.lds
	$(TOOLCHAIN_PREFIX)gcc -Os -m32 -ffreestanding -nostdlib -o firmware.elf firmware.S firmware.c \
			--std=gnu99 -Wl,-Bstatic,-T,firmware.lds,-Map,firmware.map,--strip-debug -lgcc
	chmod -x firmware.elf

firmware.bin: firmware.elf
	$(TOOLCHAIN_PREFIX)objcopy -O binary firmware.elf firmware.bin
	chmod -x firmware.bin

firmware.hex: firmware.bin
	python3 ../../firmware/makehex.py firmware.bin 128 > firmware.hex

synth.blif: example.v firmware.hex
	yosys -v3 -l synth.log -p 'synth_ice40 -top top -blif synth.blif; write_verilog -attr2comment synth.v' ../../picorv32.v example.v

example.txt: synth.blif
	arachne-pnr -d 8k -o example.txt -p example.pcf synth.blif

example.bin: example.txt
	icepack example.txt example.bin

example_tb.exe: example_tb.v example.v firmware.hex
	iverilog -o example_tb.exe -s testbench example.v example_tb.v ../../picorv32.v
	chmod -x example_tb.exe

sim: example_tb.exe
	vvp -N example_tb.exe # +vcd

prog_sram:
	iceprog -S example.bin

clean:
	rm -f firmware.elf firmware.map firmware.bin firmware.hex
	rm -f synth.log synth.v synth.blif example.txt example.bin
	rm -f example_tb.exe example.vcd

.PHONY: all sim prog_sram clean


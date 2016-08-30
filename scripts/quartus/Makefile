
QUARTUS_ROOTDIR = /opt/altera_lite/16.0
QUARTUS_BIN = $(QUARTUS_ROOTDIR)/quartus/bin

VLOG = iverilog
TOOLCHAIN_PREFIX = /opt/riscv32i/bin/riscv32-unknown-elf-

export VIVADO

help:
	@echo ""
	@echo "Simple synthesis tests:"
	@echo "  make synth_area_{small|regular|large}"
	@echo "  make synth_speed"
	@echo ""
	@echo "Example system:"
	@echo "  make synth_system"
	@echo "  make sim_system"
	@echo ""
	@echo "Timing and Utilization Evaluation:"
	@echo "  make table.txt"
	@echo "  make area"
	@echo ""

synth_%:
	rm -f $@.log
	$(VIVADO) -nojournal -log $@.log -mode batch -source $@.tcl
	rm -rf .Xil fsm_encoding.os synth_*.backup.log usage_statistics_webtalk.*
	-grep -B4 -A10 'Slice LUTs' $@.log
	-grep -B1 -A9 ^Slack $@.log && echo

synth_system: firmware.hex

sim_system: firmware.hex system_tb.v system.v ../../picorv32.v
	$(VLOG) -o system_tb system_tb.v system.v ../../picorv32.v
	./system_tb

firmware.hex: firmware.S firmware.c firmware.lds
	$(TOOLCHAIN_PREFIX)gcc -Os -m32 -ffreestanding -nostdlib -o firmware.elf firmware.S firmware.c \
		 --std=gnu99 -Wl,-Bstatic,-T,firmware.lds,-Map,firmware.map,--strip-debug -lgcc
	$(TOOLCHAIN_PREFIX)objcopy -O binary firmware.elf firmware.bin
	python3 ../../firmware/makehex.py firmware.bin 4096 > firmware.hex

tab_%/results.txt:
	bash tabtest.sh $@

area: synth_area_small synth_area_regular synth_area_large
	-grep -B4 -A10 'Slice LUTs' synth_area_small.log synth_area_regular.log synth_area_large.log

table.txt: tab_small_ep4ce_c7/results.txt
table.txt: tab_small_ep4cgx_c7/results.txt
table.txt: tab_small_5cgx_c7/results.txt

table.txt:
	bash table.sh > table.txt

clean:
	rm -rf firmware.bin firmware.elf firmware.hex firmware.map synth_*.log
	rm -rf synth_*.mmi synth_*.bit synth_system.v table.txt tab_*/ webtalk.jou


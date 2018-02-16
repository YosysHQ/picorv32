
export QUARTUS_ROOTDIR = /opt/altera_lite/16.0
export QUARTUS_BIN = $(QUARTUS_ROOTDIR)/quartus/bin

VLOG = iverilog
TOOLCHAIN_PREFIX = /opt/riscv32i/bin/riscv32-unknown-elf-

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
	mkdir -p $@_build
	cp $@.qsf $@_build
	cd $@_build && $(QUARTUS_BIN)/quartus_map $@.qsf
	cd $@_build && $(QUARTUS_BIN)/quartus_fit --read_settings_files=off -write_settings_files=off $@ -c $@
	cd $@_build && $(QUARTUS_BIN)/quartus_sta $@ -c $@
	-cd $@_build && grep -A3 "Total logic elements" output_files/$@.fit.summary
	-cd $@_build && grep -B1 "Slack" output_files/$@.sta.summary

synth_system: firmware.hex

sim_system: firmware.hex system_tb.v system.v ../../picorv32.v
	$(VLOG) -o system_tb system_tb.v system.v ../../picorv32.v
	./system_tb

firmware.hex: firmware.S firmware.c firmware.lds
	$(TOOLCHAIN_PREFIX)gcc -Os -ffreestanding -nostdlib -o firmware.elf firmware.S firmware.c \
		 --std=gnu99 -Wl,-Bstatic,-T,firmware.lds,-Map,firmware.map,--strip-debug -lgcc
	$(TOOLCHAIN_PREFIX)objcopy -O binary firmware.elf firmware.bin
	python3 ../../firmware/makehex.py firmware.bin 4096 > firmware.hex

tab_%/results.txt:
	bash tabtest.sh $@

area: synth_area_small synth_area_regular synth_area_large
	-grep -A3 "Total logic elements" synth_area_*_build/output_files/synth_area_*.fit.summary

table.txt: tab_small_ep4ce_c7/results.txt
table.txt: tab_small_ep4cgx_c7/results.txt
table.txt: tab_small_5cgx_c7/results.txt

table.txt:
	bash table.sh > table.txt

clean:
	rm -rf firmware.bin firmware.elf firmware.hex firmware.map synth_*.log
	rm -rf table.txt tab_*/
	rm -rf synth_*_build


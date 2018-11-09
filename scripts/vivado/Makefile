
VIVADO_BASE = /opt/Xilinx/Vivado/2018.2
VIVADO = $(VIVADO_BASE)/bin/vivado
XVLOG = $(VIVADO_BASE)/bin/xvlog
XELAB = $(VIVADO_BASE)/bin/xelab
GLBL = $(VIVADO_BASE)/data/verilog/src/glbl.v
TOOLCHAIN_PREFIX = riscv32-unknown-elf-

export VIVADO

# work-around for http://svn.clifford.at/handicraft/2016/vivadosig11
export RDI_VERBOSE = False

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

sim_system:
	$(XVLOG) system_tb.v synth_system.v
	$(XVLOG) $(GLBL)
	$(XELAB) -L unifast_ver -L unisims_ver -R system_tb glbl

firmware.hex: firmware.S firmware.c firmware.lds
	$(TOOLCHAIN_PREFIX)gcc -Os -ffreestanding -nostdlib -o firmware.elf firmware.S firmware.c \
		 --std=gnu99 -Wl,-Bstatic,-T,firmware.lds,-Map,firmware.map,--strip-debug -lgcc
	$(TOOLCHAIN_PREFIX)objcopy -O binary firmware.elf firmware.bin
	python3 ../../firmware/makehex.py firmware.bin 4096 > firmware.hex

tab_%/results.txt:
	bash tabtest.sh $@

area: synth_area_small synth_area_regular synth_area_large
	-grep -B4 -A10 'Slice LUTs' synth_area_small.log synth_area_regular.log synth_area_large.log

table.txt: tab_small_xc7k_2/results.txt  tab_small_xc7k_3/results.txt
table.txt: tab_small_xc7v_2/results.txt  tab_small_xc7v_3/results.txt
table.txt: tab_small_xcku_2/results.txt  tab_small_xcku_3/results.txt
table.txt: tab_small_xcvu_2/results.txt  tab_small_xcvu_3/results.txt
table.txt: tab_small_xckup_2/results.txt tab_small_xckup_3/results.txt
table.txt: tab_small_xcvup_2/results.txt tab_small_xcvup_3/results.txt

table.txt:
	bash table.sh > table.txt

clean:
	rm -rf .Xil/ firmware.bin firmware.elf firmware.hex firmware.map synth_*.log
	rm -rf synth_*.mmi synth_*.bit synth_system.v table.txt tab_*/ webtalk.jou
	rm -rf webtalk.log webtalk_*.jou webtalk_*.log xelab.* xsim[._]* xvlog.*



VIVADO = /opt/Xilinx/Vivado/2014.4/bin/vivado

help:
	@echo "Usage: make {synth_speed|synth_area|synth_soc}"

synth_%:
	$(VIVADO) -nojournal -log $@.log -mode batch -source $@.tcl
	rm -rf .Xil fsm_encoding.os synth_*.backup.log


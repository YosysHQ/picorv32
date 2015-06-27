
export VIVADO = /opt/Xilinx/Vivado/2015.1/bin/vivado

help:
	@echo "Usage: make {synth_speed|synth_area|synth_soc}"

synth_%:
	rm -f $@.log
	$(VIVADO) -nojournal -log $@.log -mode batch -source $@.tcl
	rm -rf .Xil fsm_encoding.os synth_*.backup.log usage_statistics_webtalk.*
	-grep -B4 -A10 'Slice LUTs' $@.log
	-grep -B1 -A9 ^Slack $@.log && echo

tab_%/results.txt:
	bash tabtest.sh $@

table.txt: tab_small_xc7a_1/results.txt tab_small_xc7a_2/results.txt tab_small_xc7a_3/results.txt
table.txt: tab_small_xc7k_1/results.txt tab_small_xc7k_2/results.txt tab_small_xc7k_3/results.txt
table.txt: tab_small_xc7v_1/results.txt tab_small_xc7v_2/results.txt tab_small_xc7v_3/results.txt

table.txt:
	bash table.sh > table.txt


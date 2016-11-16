#!/bin/bash

set -ex

yosys -l tracecmp3.yslog \
        -p 'read_verilog ../../picorv32.v' \
        -p 'read_verilog -formal tracecmp3.v' \
	-p 'prep -top testbench -nordff' \
	-p 'write_smt2 -wires tracecmp3.smt2' \
	-p 'miter -assert -flatten testbench miter' \
	-p 'hierarchy -top miter; memory_map; opt -full' \
	-p 'techmap; opt; abc; opt -fast' \
	-p 'write_blif tracecmp3.blif'

yosys-abc -c 'read_blif tracecmp3.blif; undc; strash; zero; sim3 -v; undc -c; write_cex -n tracecmp3.cex'
yosys-smtbmc -s yices --cex tracecmp3.cex --dump-vcd output.vcd --dump-smtc output.smtc tracecmp3.smt2


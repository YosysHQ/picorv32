#!/bin/bash

set -ex

yosys -ql mulcmp.yslog \
        -p 'read_verilog -formal -norestrict -assume-asserts ../../picorv32.v' \
        -p 'read_verilog -formal mulcmp.v' \
	-p 'prep -top testbench -nordff' \
	-p 'write_smt2 -wires mulcmp.smt2'

yosys-smtbmc -s yices -t 100 --dump-vcd output.vcd --dump-smtc output.smtc mulcmp.smt2


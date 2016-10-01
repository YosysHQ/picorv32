#!/bin/bash

set -ex

yosys -ql axicheck.yslog \
	-p 'read_verilog -formal -norestrict -assume-asserts ../../picorv32.v' \
	-p 'read_verilog -formal axicheck.v' \
	-p 'prep -top testbench -nordff' \
	-p 'write_smt2 -wires axicheck.smt2'

yosys-smtbmc -t 50 -s boolector --dump-vcd output.vcd --dump-smtc output.smtc axicheck.smt2
# yosys-smtbmc -t 50 -i -s boolector --dump-vcd output.vcd --dump-smtc output.smtc axicheck.smt2


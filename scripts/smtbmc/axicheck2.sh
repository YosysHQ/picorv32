#!/bin/bash

set -ex

yosys -ql axicheck2.yslog \
	-p 'read_verilog -formal -norestrict -assume-asserts ../../picorv32.v' \
	-p 'read_verilog -formal axicheck2.v' \
	-p 'prep -top testbench -nordff' \
	-p 'write_smt2 -wires axicheck2.smt2'

yosys-smtbmc -t 6 -s yices --dump-vcd output.vcd --dump-smtc output.smtc --smtc axicheck2.smtc axicheck2.smt2


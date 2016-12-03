#!/bin/bash

set -ex

yosys -ql tracecmp2.yslog \
        -p 'read_verilog -formal -norestrict -assume-asserts ../../picorv32.v' \
        -p 'read_verilog -formal tracecmp2.v' \
	-p 'prep -top testbench -nordff' \
	-p 'write_smt2 -wires tracecmp2.smt2'

yosys-smtbmc -s boolector --smtc tracecmp2.smtc --dump-vcd output.vcd --dump-smtc output.smtc tracecmp2.smt2


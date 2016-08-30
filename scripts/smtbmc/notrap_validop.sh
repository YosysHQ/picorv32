#!/bin/bash

set -ex

yosys -ql notrap_validop.yslog \
        -p 'read_verilog -formal -norestrict -assume-asserts ../../picorv32.v' \
        -p 'read_verilog -formal notrap_validop.v' \
	-p 'prep -top testbench -nordff' \
	-p 'write_smt2 -mem -bv -wires notrap_validop.smt2'

#yosys-smtbmc -s yices -t 50 --dump-vcd output.vcd --dump-smtc output.smtc notrap_validop.smt2
yosys-smtbmc -s yices -i -t 27 --dump-vcd output.vcd --dump-smtc output.smtc notrap_validop.smt2


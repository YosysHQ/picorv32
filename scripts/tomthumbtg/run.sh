#!/bin/bash

set -ex

if [ ! -f testgen.tgz ]; then
	rm -f testgen.tgz.part
	wget -O testgen.tgz.part http://maikmerten.de/testgen.tgz
	mv testgen.tgz.part testgen.tgz
fi

rm -rf tests testgen/
tar xvzf testgen.tgz

iverilog -o testbench_a -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=0 -DBARREL_SHIFTER=0 -DTWO_CYCLE_COMPARE=0 -DTWO_CYCLE_ALU=0
iverilog -o testbench_b -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=1 -DBARREL_SHIFTER=0 -DTWO_CYCLE_COMPARE=0 -DTWO_CYCLE_ALU=0
iverilog -o testbench_c -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=0 -DBARREL_SHIFTER=1 -DTWO_CYCLE_COMPARE=0 -DTWO_CYCLE_ALU=0

iverilog -o testbench_d -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=0 -DBARREL_SHIFTER=0 -DTWO_CYCLE_COMPARE=1 -DTWO_CYCLE_ALU=0
iverilog -o testbench_e -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=1 -DBARREL_SHIFTER=0 -DTWO_CYCLE_COMPARE=1 -DTWO_CYCLE_ALU=0
iverilog -o testbench_f -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=0 -DBARREL_SHIFTER=1 -DTWO_CYCLE_COMPARE=1 -DTWO_CYCLE_ALU=0

iverilog -o testbench_g -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=0 -DBARREL_SHIFTER=0 -DTWO_CYCLE_COMPARE=0 -DTWO_CYCLE_ALU=1
iverilog -o testbench_h -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=1 -DBARREL_SHIFTER=0 -DTWO_CYCLE_COMPARE=0 -DTWO_CYCLE_ALU=1
iverilog -o testbench_i -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=0 -DBARREL_SHIFTER=1 -DTWO_CYCLE_COMPARE=0 -DTWO_CYCLE_ALU=1

iverilog -o testbench_j -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=0 -DBARREL_SHIFTER=0 -DTWO_CYCLE_COMPARE=1 -DTWO_CYCLE_ALU=1
iverilog -o testbench_k -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=1 -DBARREL_SHIFTER=0 -DTWO_CYCLE_COMPARE=1 -DTWO_CYCLE_ALU=1
iverilog -o testbench_l -s testbench testbench.v ../../picorv32.v -DTWO_STAGE_SHIFT=0 -DBARREL_SHIFTER=1 -DTWO_CYCLE_COMPARE=1 -DTWO_CYCLE_ALU=1

mkdir -p tests
for i in {0..999}; do
	fn="tests/test_`printf '%03d' $i`"

	{
		cat start.S
		java -jar testgen/tomthumb-testgen-1.0-SNAPSHOT.jar
	} > $fn.s

	riscv32-unknown-elf-gcc -ffreestanding -nostdlib -Wl,-Bstatic,-T,sections.lds -o $fn.elf $fn.s
	riscv32-unknown-elf-objcopy -O binary $fn.elf $fn.bin
	python3 ../../firmware/makehex.py $fn.bin 16384 > $fn.hex
	for tb in testbench_{a,b,c,d,e,f,g,h,i,j,k,l}; do vvp -N $tb +hex=$fn.hex; done
done

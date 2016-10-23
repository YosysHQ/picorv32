#!/bin/bash

set -ex

if [ ! -f testgen.tgz ]; then
	rm -f testgen.tgz.part
	wget -O testgen.tgz.part http://maikmerten.de/testgen.tgz
	mv testgen.tgz.part testgen.tgz
fi

rm -rf tests testgen/
tar xvzf testgen.tgz 

iverilog -o testbench -s testbench testbench.v ../../picorv32.v 

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
	vvp -N ./testbench +hex=tests/test_000.hex
done

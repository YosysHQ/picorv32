#!/bin/bash

set -ex


## Generate test case

cd riscv-torture
./sbt generator/run
cp output/test.S ../test.S
cd ..


## Compile test case and create reference

riscv32-unknown-elf-gcc -m32 -ffreestanding -nostdlib -Wl,-Bstatic,-T,sections.lds -o test.elf test.S
LD_LIBRARY_PATH="./riscv-isa-sim:./riscv-fesvr" ./riscv-isa-sim/spike test.elf > test.ref


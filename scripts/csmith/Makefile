RISCV_TOOLS_DIR = /opt/riscv32imc
RISCV_TOOLS_PREFIX = $(RISCV_TOOLS_DIR)/bin/riscv32-unknown-elf-
CSMITH_INCDIR = $(shell ls -d /usr/local/include/csmith-* | head -n1)
CC = $(RISCV_TOOLS_PREFIX)gcc
SHELL = /bin/bash

help:
	@echo "Usage: make { loop | verilator | iverilog | spike }"

loop: riscv-fesvr/build.ok riscv-isa-sim/build.ok obj_dir/Vtestbench
	+set -e; x() { echo "$$*" >&2; "$$@"; }; i=1; j=1; while true; do echo; echo; \
		echo "---------------- $$((i++)) ($$j) ----------------"; \
		x rm -f test.hex test.elf test.c test_ref test.ld output_ref.txt output_sim.txt; \
		x make spike test.hex || { echo SKIP; continue; }; x rm -f output_sim.txt; \
		x obj_dir/Vtestbench | grep -v '$$finish' > output_sim.txt; \
		x diff -u output_ref.txt output_sim.txt; echo OK; ! ((j++)); \
	done

verilator: test_ref test.hex obj_dir/Vtestbench
	timeout 2 ./test_ref > output_ref.txt && cat output_ref.txt
	obj_dir/Vtestbench | grep -v '$$finish' > output_sim.txt
	diff -u output_ref.txt output_sim.txt

iverilog: test_ref test.hex testbench.vvp
	timeout 2 ./test_ref > output_ref.txt && cat output_ref.txt
	vvp -N testbench.vvp > output_sim.txt
	diff -u output_ref.txt output_sim.txt

spike: riscv-fesvr/build.ok riscv-isa-sim/build.ok test_ref test.elf
	timeout 2 ./test_ref > output_ref.txt && cat output_ref.txt
	LD_LIBRARY_PATH="./riscv-isa-sim:./riscv-fesvr" ./riscv-isa-sim/spike test.elf > output_sim.txt
	diff -u output_ref.txt output_sim.txt

riscv-fesvr/build.ok:
	rm -rf riscv-fesvr
	git clone https://github.com/riscv/riscv-fesvr.git riscv-fesvr
	+cd riscv-fesvr && git checkout 1c02bd6 && ./configure && make && touch build.ok

riscv-isa-sim/build.ok: riscv-fesvr/build.ok
	rm -rf riscv-isa-sim
	git clone https://github.com/riscv/riscv-isa-sim.git riscv-isa-sim
	cd riscv-isa-sim && git checkout 10ae74e
	cd riscv-isa-sim && patch -p1 < ../riscv-isa-sim.diff
	cd riscv-isa-sim && LDFLAGS="-L../riscv-fesvr" ./configure --with-isa=RV32IMC
	+cd riscv-isa-sim && ln -s ../riscv-fesvr/fesvr . && make && touch build.ok

testbench.vvp: testbench.v ../../picorv32.v
	iverilog -o testbench.vvp testbench.v ../../picorv32.v
	chmod -x testbench.vvp

obj_dir/Vtestbench: testbench.v testbench.cc ../../picorv32.v
	verilator --exe -Wno-fatal --cc --top-module testbench testbench.v ../../picorv32.v testbench.cc
	$(MAKE) -C obj_dir -f Vtestbench.mk

test.hex: test.elf
	$(RISCV_TOOLS_PREFIX)objcopy -O verilog test.elf test.hex

start.elf: start.S start.ld
	$(CC) -nostdlib -o start.elf start.S -T start.ld
	chmod -x start.elf

test_ref: test.c
	gcc -m32 -o test_ref -w -Os -I $(CSMITH_INCDIR) test.c

test.elf: test.c syscalls.c start.S
	sed -e '/SECTIONS/,+1 s/{/{ . = 0x00000000; .start : { *(.text.start) } application_entry_point = 0x00010000;/;' \
		$(RISCV_TOOLS_DIR)/riscv32-unknown-elf/lib/riscv.ld > test.ld
	$(CC) -o test.elf -w -Os -I $(CSMITH_INCDIR) -T test.ld test.c syscalls.c start.S
	chmod -x test.elf

test.c:
	echo "integer size = 4" > platform.info
	echo "pointer size = 4" >> platform.info
	csmith --no-packed-struct -o test.c
	gawk '/Seed:/ {print$$2,$$3;}' test.c

clean:
	rm -rf platform.info test.c test.ld test.elf test.hex test_ref obj_dir
	rm -rf testbench.vvp testbench.vcd output_ref.txt output_sim.txt

mrproper: clean
	rm -rf riscv-fesvr riscv-isa-sim

.PHONY: help loop verilator iverilog spike clean mrproper


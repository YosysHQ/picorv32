RISCV_TOOLS_DIR = /opt/riscv32imc
RISCV_TOOLS_PREFIX = $(RISCV_TOOLS_DIR)/bin/riscv32-unknown-elf-
CSMITH_INCDIR = $(shell ls -d /usr/local/include/csmith-* | head -n1)
CC = $(RISCV_TOOLS_PREFIX)gcc

run: test_ref test.hex testbench.vvp
	./test_ref | tee output_ref.txt
	vvp -N testbench.vvp | tee output_sim.txt
	diff -u output_ref.txt output_sim.txt

spike: riscv-fesvr/build.ok riscv-isa-sim/build.ok test_ref test.elf
	./test_ref | tee output_ref.txt
	LD_LIBRARY_PATH="./riscv-isa-sim:./riscv-fesvr" ./riscv-isa-sim/spike test.elf | tee output_spike.txt
	diff -u output_ref.txt output_spike.txt

riscv-fesvr/build.ok:
	rm -rf riscv-fesvr
	git clone https://github.com/riscv/riscv-fesvr.git riscv-fesvr
	+cd riscv-fesvr && git checkout 1c02bd6 && ./configure && make && touch build.ok

riscv-isa-sim/build.ok: riscv-fesvr/build.ok
	rm -rf riscv-isa-sim
	git clone https://github.com/riscv/riscv-isa-sim.git riscv-isa-sim
	cd riscv-isa-sim && git checkout 10ae74e
	cd riscv-isa-sim && patch -p1 < ../riscv-isa-sim-exit.diff
	cd riscv-isa-sim && patch -p1 < ../riscv-isa-sim-console.diff
	cd riscv-isa-sim && LDFLAGS="-L../riscv-fesvr" ./configure --with-isa=RV32IMC
	+cd riscv-isa-sim && ln -s ../riscv-fesvr/fesvr . && make && touch build.ok

testbench.vvp: testbench.v ../../picorv32.v
	iverilog -o testbench.vvp testbench.v ../../picorv32.v
	chmod -x testbench.vvp

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

clean:
	rm -f platform.info test.c test.ld test.elf test.hex test_ref testbench.vvp testbench.vcd
	rm -f output_ref.txt output_sim.txt output_spike.txt

mrproper: clean
	rm -rf riscv-fesvr riscv-isa-sim

.PHONY: run spike clean mrproper


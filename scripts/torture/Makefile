
test: riscv-torture/build.ok riscv-isa-sim/build.ok
	bash test.sh

riscv-torture/build.ok: riscv-torture-rv32.diff
	rm -rf riscv-torture
	git clone https://github.com/ucb-bar/riscv-torture.git riscv-torture
	cd riscv-torture && git checkout 2bc0c42
	cd riscv-torture && patch -p1 < ../riscv-torture-rv32.diff
	cd riscv-torture && patch -p1 < ../riscv-torture-genloop.diff
	cd riscv-torture && ./sbt generator/run && touch build.ok

riscv-fesvr/build.ok:
	rm -rf riscv-fesvr
	git clone https://github.com/riscv/riscv-fesvr.git riscv-fesvr
	+cd riscv-fesvr && git checkout 1c02bd6 && ./configure && make && touch build.ok

riscv-isa-sim/build.ok: riscv-fesvr/build.ok
	rm -rf riscv-isa-sim
	git clone https://github.com/riscv/riscv-isa-sim.git riscv-isa-sim
	cd riscv-isa-sim && git checkout 10ae74e
	cd riscv-isa-sim && patch -p1 < ../riscv-isa-sim-sbreak.diff
	cd riscv-isa-sim && patch -p1 < ../riscv-isa-sim-notrap.diff
	cd riscv-isa-sim && LDFLAGS="-L../riscv-fesvr" ./configure --with-isa=RV32IMC
	+cd riscv-isa-sim && ln -s ../riscv-fesvr/fesvr . && make && touch build.ok

batch_list = $(shell bash -c 'for i in {0..999}; do printf "%03d\n" $$i; done')

batch: $(addprefix tests/test_,$(addsuffix .ok,$(batch_list)))

tests/testbench.vvp: testbench.v ../../picorv32.v
	mkdir -p tests
	iverilog -o tests/testbench.vvp testbench.v ../../picorv32.v

tests/generated.ok: riscv-torture/build.ok
	mkdir -p tests
	rm -f riscv-torture/output/test_*
	cd riscv-torture && ./sbt 'generator/run -n 1000'
	sed -i -e '/addi x2, x2, 0/ s/addi/xori/;' riscv-torture/output/test_*.S
	touch tests/generated.ok

define test_template
tests/test_$(1).S: tests/generated.ok
	mv riscv-torture/output/test_$(1).S tests/
	touch tests/test_$(1).S

tests/test_$(1).elf: tests/test_$(1).S
	riscv32-unknown-elf-gcc -m32 -march=RV32IC -ffreestanding -nostdlib -Wl,-Bstatic,-T,sections.lds -I. -o tests/test_$(1).elf tests/test_$(1).S

tests/test_$(1).bin: tests/test_$(1).elf
	riscv32-unknown-elf-objcopy -O binary tests/test_$(1).elf tests/test_$(1).bin

tests/test_$(1).hex: tests/test_$(1).bin
	python3 ../../firmware/makehex.py tests/test_$(1).bin 4096 > tests/test_$(1).hex

tests/test_$(1).ref: tests/test_$(1).elf riscv-isa-sim/build.ok
	LD_LIBRARY_PATH="./riscv-isa-sim:./riscv-fesvr" ./riscv-isa-sim/spike tests/test_$(1).elf > tests/test_$(1).ref

tests/test_$(1).ok: tests/testbench.vvp tests/test_$(1).hex tests/test_$(1).ref
	vvp tests/testbench.vvp +hex=tests/test_$(1).hex +ref=tests/test_$(1).ref | tee tests/test_$(1).out
	grep -q PASSED tests/test_$(1).out
	mv tests/test_$(1).out tests/test_$(1).ok
endef

$(foreach id,$(batch_list),$(eval $(call test_template,$(id))))

loop:
	date +"%s %Y-%m-%d %H:%M:%S START" >> .looplog
	+set -ex; while true; do \
	  rm -rf tests; $(MAKE) batch; \
	  date +"%s %Y-%m-%d %H:%M:%S NEXT" >> .looplog; \
	done

clean:
	rm -rf riscv-torture riscv-fesvr riscv-isa-sim tests
	rm -f test.S test.elf test.bin test.hex test.ref test.vvp

.PHONY: test batch loop clean


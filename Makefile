
RISCV_GNU_TOOLCHAIN_REV = 888ae43
GCC_URL = http://mirrors.kernel.org/gnu/gcc/gcc-5.3.0/gcc-5.3.0.tar.gz
NEWLIB_URL = ftp://sourceware.org/pub/newlib/newlib-2.2.0.tar.gz
BINUTILS_URL = http://mirrors.kernel.org/gnu/binutils/binutils-2.26.tar.gz

TEST_OBJS = $(addsuffix .o,$(basename $(wildcard tests/*.S)))
FIRMWARE_OBJS = firmware/start.o firmware/irq.o firmware/print.o firmware/sieve.o firmware/multest.o firmware/stats.o
GCC_WARNS  = -Werror -Wall -Wextra -Wshadow -Wundef -Wpointer-arith -Wcast-qual -Wcast-align -Wwrite-strings
GCC_WARNS += -Wredundant-decls -Wstrict-prototypes -Wmissing-prototypes -pedantic # -Wconversion
TOOLCHAIN_PREFIX = /opt/riscv32i/bin/riscv32-unknown-elf-
COMPRESSED_ISA = C

test: testbench.exe firmware/firmware.hex
	vvp -N testbench.exe

testbench.vcd: testbench.exe firmware/firmware.hex
	vvp -N $< +vcd

view: testbench.vcd
	gtkwave $< testbench.gtkw

check: check.smt2
	yosys-smtbmc -t 30 -c check.vcd check.smt2
	yosys-smtbmc -t 30 -c check.vcd -i check.smt2

check.smt2: picorv32.v
	yosys -v2 -p 'read_verilog -formal picorv32.v' \
	          -p 'prep -top picorv32 -nordff' \
		  -p 'write_smt2 -bv -mem -wires check.smt2'

test_sp: testbench_sp.exe firmware/firmware.hex
	vvp -N testbench_sp.exe

test_axi: testbench.exe firmware/firmware.hex
	vvp -N testbench.exe +axi_test

test_synth: testbench_synth.exe firmware/firmware.hex
	vvp -N testbench_synth.exe

testbench.exe: testbench.v picorv32.v
	iverilog -o testbench.exe $(subst C,-DCOMPRESSED_ISA,$(COMPRESSED_ISA)) testbench.v picorv32.v
	chmod -x testbench.exe

testbench_sp.exe: testbench.v picorv32.v
	iverilog -o testbench_sp.exe $(subst C,-DCOMPRESSED_ISA,$(COMPRESSED_ISA)) -DSP_TEST testbench.v picorv32.v
	chmod -x testbench_sp.exe

testbench_synth.exe: testbench.v synth.v
	iverilog -o testbench_synth.exe testbench.v synth.v
	chmod -x testbench_synth.exe

synth.v: picorv32.v scripts/yosys/synth_sim.ys
	yosys -qv3 -l synth.log scripts/yosys/synth_sim.ys

firmware/firmware.hex: firmware/firmware.bin firmware/makehex.py
	python3 firmware/makehex.py $< 16384 > $@

firmware/firmware.bin: firmware/firmware.elf
	$(TOOLCHAIN_PREFIX)objcopy -O binary $< $@
	chmod -x $@

firmware/firmware.elf: $(FIRMWARE_OBJS) $(TEST_OBJS) firmware/sections.lds
	$(TOOLCHAIN_PREFIX)gcc -Os -m32 -ffreestanding -nostdlib -o $@ \
		-Wl,-Bstatic,-T,firmware/sections.lds,-Map,firmware/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(TEST_OBJS) -lgcc
	chmod -x $@

firmware/start.o: firmware/start.S
	$(TOOLCHAIN_PREFIX)gcc -c -m32 -march=RV32IM$(COMPRESSED_ISA)Xcustom -o $@ $<

firmware/%.o: firmware/%.c
	$(TOOLCHAIN_PREFIX)gcc -c -m32 -march=RV32I$(COMPRESSED_ISA) -Os --std=c99 $(GCC_WARNS) -ffreestanding -nostdlib -o $@ $<

tests/%.o: tests/%.S tests/riscv_test.h tests/test_macros.h
	$(TOOLCHAIN_PREFIX)gcc -c -m32 -march=RV32IM -o $@ -DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' -DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

download-tools:
	sudo bash -c 'set -ex; mkdir -p /var/cache/distfiles; $(foreach URL,$(GCC_URL) $(NEWLIB_URL) $(BINUTILS_URL), \
		if ! test -f /var/cache/distfiles/$(notdir $(URL)); then wget -O /var/cache/distfiles/$(notdir $(URL)).part $(URL); \
			mv /var/cache/distfiles/$(notdir $(URL)).part /var/cache/distfiles/$(notdir $(URL)); fi;)'

define build_tools_template
build-$(1)-tools:
	@read -p "This will remove all existing data from /opt/$(1). Type YES to continue: " reply && [[ "$$$$reply" == [Yy][Ee][Ss] || "$$$$reply" == [Yy] ]]
	sudo bash -c "set -ex; rm -rf /opt/$(1); mkdir -p /opt/$(1); chown $$$${USER}. /opt/$(1)"
	$(MAKE) build-$(1)-tools-bh

build-$(1)-tools-bh:
	set -ex; if ! test -d riscv-gnu-toolchain-$(1); then git clone https://github.com/riscv/riscv-gnu-toolchain riscv-gnu-toolchain-$(1); \
		else cd riscv-gnu-toolchain-$(1); git checkout master; git pull; fi
	set -ex; cd riscv-gnu-toolchain-$(1); rm -rf build; git checkout $(RISCV_GNU_TOOLCHAIN_REV); mkdir -p build
	set -ex; cd riscv-gnu-toolchain-$(1)/build; ../configure --with-xlen=32 --with-arch=$(2) --prefix=/opt/$(1) --disable-float --disable-atomic
	+set -ex; cd riscv-gnu-toolchain-$(1)/build; make

.PHONY: build-$(1)-tools
endef

$(eval $(call build_tools_template,riscv32i,I))
$(eval $(call build_tools_template,riscv32ic,IC))
$(eval $(call build_tools_template,riscv32im,IM))
$(eval $(call build_tools_template,riscv32imc,IMC))

build-tools:
	@echo "This will remove all existing data from /opt/riscv32i, /opt/riscv32ic, /opt/riscv32im, and /opt/riscv32imc."
	@read -p "Type YES to continue: " reply && [[ "$$reply" == [Yy][Ee][Ss] || "$$reply" == [Yy] ]]
	sudo bash -c "set -ex; rm -rf /opt/riscv32{i,ic,im,imc}; mkdir -p /opt/riscv32{i,ic,im,imc}; chown $${USER}. /opt/riscv32{i,ic,im,imc}"
	$(MAKE) build-riscv32i-tools-bh build-riscv32ic-tools-bh build-riscv32im-tools-bh build-riscv32imc-tools-bh

toc:
	gawk '/^-+$$/ { y=tolower(x); gsub("[^a-z0-9]+", "-", y); gsub("-$$", "", y); printf("- [%s](#%s)\n", x, y); } { x=$$0; }' README.md

clean:
	rm -rf riscv-gnu-toolchain-riscv32i riscv-gnu-toolchain-riscv32ic \
		riscv-gnu-toolchain-riscv32im riscv-gnu-toolchain-riscv32imc
	rm -vrf $(FIRMWARE_OBJS) $(TEST_OBJS) check.smt2 check.vcd synth.v synth.log \
		firmware/firmware.elf firmware/firmware.bin firmware/firmware.hex firmware/firmware.map \
		testbench.exe testbench_sp.exe testbench_synth.exe testbench.vcd

.PHONY: test view test_sp test_axi test_synth download-tools toc clean


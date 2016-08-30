USE_MYSTDLIB = 0
OBJS = dhry_1.o dhry_2.o stdlib.o
CFLAGS = -MD -O3 -m32 -march=RV32IM -DTIME -DRISCV
TOOLCHAIN_PREFIX = /opt/riscv32im/bin/riscv32-unknown-elf-

ifeq ($(USE_MYSTDLIB),1)
CFLAGS += -DUSE_MYSTDLIB -ffreestanding -nostdlib
OBJS += start.o
else
OBJS += syscalls.o
endif

test: testbench.vvp dhry.hex
	vvp -N testbench.vvp

timing: timing.txt
	grep '^##' timing.txt | gawk 'x != "" {print x,$$3-y;} {x=$$2;y=$$3;}' | sort | uniq -c | \
		gawk '{printf("%03d-%-7s %2d %-8s (%d)\n",$$3,$$2,$$3,$$2,$$1);}' | sort | cut -c13-

timing.txt: timing.vvp dhry.hex
	vvp -N timing.vvp > timing.txt

testbench.vvp: testbench.v ../picorv32.v
	iverilog -o testbench.vvp testbench.v ../picorv32.v
	chmod -x testbench.vvp

timing.vvp: testbench.v ../picorv32.v
	iverilog -o timing.vvp -DTIMING testbench.v ../picorv32.v
	chmod -x timing.vvp

dhry.hex: dhry.elf
	$(TOOLCHAIN_PREFIX)objcopy -O verilog $< $@

ifeq ($(USE_MYSTDLIB),1)
dhry.elf: $(OBJS) sections.lds
	$(TOOLCHAIN_PREFIX)gcc $(CFLAGS) -Wl,-Bstatic,-T,sections.lds,-Map,dhry.map,--strip-debug -o $@ $(OBJS) -lgcc
	chmod -x $@
else
dhry.elf: $(OBJS)
	$(TOOLCHAIN_PREFIX)gcc $(CFLAGS) -Wl,-Bstatic,-Map,dhry.map,--strip-debug -o $@ $(OBJS) -lgcc -lc
	chmod -x $@
endif

%.o: %.c
	$(TOOLCHAIN_PREFIX)gcc -c $(CFLAGS) $<

%.o: %.S
	$(TOOLCHAIN_PREFIX)gcc -c $(CFLAGS) $<

dhry_1.o dhry_2.o: CFLAGS += -Wno-implicit-int -Wno-implicit-function-declaration

clean:
	rm -rf *.o *.d dhry.elf dhry.map dhry.bin dhry.hex testbench.vvp testbench.vcd timing.vvp timing.txt

.PHONY: test clean

-include *.d


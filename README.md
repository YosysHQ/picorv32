
PicoRV32 - A Size-Optimized RISC-V CPU
======================================

PicoRV32 is a CPU core that implements the [RISC-V RV32I Instruction Set](http://riscv.org/).

Tools (gcc, binutils, etc..) can be obtained via the [RISC-V Website](http://riscv.org/download.html#tab_tools).

PicoRV32 is free and open hardware licensed under the [ISC license](http://en.wikipedia.org/wiki/ISC_license)
(a license that is similar in terms to the MIT license or the 2-clause BSD license).


Features and Typical Applications:
----------------------------------

- Small (~1000 LUTs in a 7-Series Xilinx FGPA)
- High fMAX (~250 MHz on 7-Series Xilinx FGPAs)
- Selectable native memory interface or AXI4-Lite master

This CPU is meant to be used as auxiliary processor in FPGA designs and ASICs. Due
to its high fMAX it can be integrated in most existing designs without crossing
clock domains. When operated on a lower frequency, it will have a lot of timing
slack and thus can be added to a design without compromising timing closure.

For even smaller size it is possible disable support for registers `x16`..`x31` as
well as `RDCYCLE[H]`, `RDTIME[H]`, and `RDINSTRET[H]` instructions, turning the
processor into an RV32E core.

Furthermore it is possible to choose between a single-port and a dual-port
register file implementation. The former provides better performance while
the latter results in a smaller core.

*Note: In architectures that implement the register file in dedicated memory
resources, such as many FPGAs, disabling the 16 upper registers and/or
disabling the dual-port register file may not further reduce the core size.*

The core exists in two variations: `picorv32` and `picorv32_axi`. The former
provides a simple native memory interface, that is easy to use in simple
environments, and the latter provides an AXI-4 Lite Master interface that can
easily be integrated with existing systems that are already using the AXI
standard.

A separate core `picorv32_axi_adapter` is provided to bridge between the native
memory interface and AXI4. This core can be used to create custom cores that
include one or more PicoRV32 cores together with local RAM, ROM, and
memory-mapped peripherals, communicating with each other using the native
interface, and communicating with the outside world via AXI4.


Parameters:
-----------

The following Verilog module parameters can be used to configure the PicoRV32
core.

#### ENABLE_COUNTERS (default = 1)

This parameter enables support for the `RDCYCLE[H]`, `RDTIME[H]`, and
`RDINSTRET[H]` instructions. This instructions will cause a hardware
trap (like any other unsupported instruction) if `ENABLE_COUNTERS` is set to zero.

*Note: Strictly speaking the `RDCYCLE[H]`, `RDTIME[H]`, and `RDINSTRET[H]`
instructions are not optional for an RV32I core. But chances are they are not
going to be missed after the application code has been debugged and profiled.
This instructions are optional for an RV32E core.*

#### ENABLE_REGS_16_31 (default = 1)

This parameter enables support for registers the `x16`..`x31`. The RV32E ISA
excludes this registers. However, the RV32E ISA spec requires a hardware trap
for when code tries to access this registers. This is not implemented in PicoRV32.

#### ENABLE_REGS_DUALPORT (default = 1)

The register file can be implemented with two or one read ports. A dual ported
register file improves performance a bit, but can also increase the size of
the core.

#### LATCHED_MEM_RDATA (default = 0)

Set this to 1 if the `mem_rdata` is kept stable by the external circuit after a
transaction. In the default configuration the PicoRV32 core only expects the
`mem_rdata` input to be valid in the cycle with `mem_valid && mem_ready` and
latches the value internally.

#### ENABLE_PCPI (default = 0)

Set this to 1 to enable the Pico Co-Processor Interface (PCPI).

#### ENABLE_IRQ (default = 0)

Set this to 1 to enable IRQs.

#### MASKED_IRQ (default = 32'h 0000_0000)

A 1 bit in this bitmask corresponds to a permanently disabled IRQ.

#### PROGADDR_RESET (default = 32'h 0000_0000)

The start address of the program.

#### PROGADDR_IRQ (default = 32'h 0000_0010)

The start address of the interrupt handler.


Performance:
------------

*A short reminder: This core is optimized for size, not performance.*

Unless stated otherwise, the following numbers apply to a PicoRV32 with
ENABLE_REGS_DUALPORT active and connected to a memory that can accomodate
requests within one clock cycle.

The average Cycles per Instruction (CPI) is 4 to 5, depending on the mix of
instructions in the code. The CPI numbers for the individual instructions
can be found in the table below. The column "CPI (SP)" contains the
CPI numbers for a core built without ENABLE_REGS_DUALPORT.

| Instruction          |  CPI | CPI (SP) |
| ---------------------| ----:| --------:|
| direct jump (jal)    |    3 |        3 |
| ALU reg + immediate  |    3 |        3 |
| ALU reg + reg        |    3 |        4 |
| branch (not taken)   |    3 |        4 |
| memory load          |    5 |        5 |
| memory store         |    5 |        6 |
| branch (taken)       |    5 |        6 |
| indirect jump (jalr) |    6 |        6 |
| shift operations     | 4-14 |     4-15 |

Dhrystone benchmark results: 0.309 DMIPS/MHz (544 Dhrystones/Second/MHz)

For the Dhrystone benchmark the average CPI is 4.167.


PicoRV32 Native Memory Interface
--------------------------------

This section is under construction.


Pico Co-Processor Interface (PCPI)
----------------------------------

This section is under construction.


Custom Instructions for IRQ Handling
------------------------------------

*Note: The IRQ handling features in PicoRV32 do not follow the RISC-V
Privileged ISA specification. Instead a small set of very simple custom
instructions is used to implement IRQ handling with minimal hardware
overhead.*

The following custom instructions are only supported when IRQs are enabled
via the `ENABLE_IRQ` parameter (see above).

The PicoRV32 core has a built-in interrupt controller with 32 interrupts. An
interrupt can be triggered by asserting the corresponding bit in the `irq`
input of the core.

When the interrupt handler is started, the `eoi` End Of Interrupt (EOI) signals
for the handled interrupts go high. The `eoi` signals go low again when the
interrupt handler returns.

The IRQs 0-2 can be triggered internally by the following built-in interrupt sources:

| IRQ | Interrupt Source                   |
| ---:| -----------------------------------|
|   0 | Timer Interrupt                    |
|   1 | SBREAK or Illegal Instruction      |
|   2 | BUS Error (Unalign Memory Access)  |

The core has 4 additional 32-bit registers `q0 .. q3` that are used for IRQ
handling. When an IRQ triggers, the register `q0` contains the return address
and `q1` contains a bitmask of all active IRQs. This means one call to the interrupt
handler might need to service more than one IRQ when more than one bit is set
in `q1`.

Registers `q2` and `q3` are uninitialized and can be used as temporary storage
when saving/restoring register values in the IRQ handler.

#### getq rd, qs

This instruction copies the value from a q-register to a general-purpose
register. This instruction is encoded under the `custom0` opcode:

    0000000 00000 000XX 000 XXXXX 0001011
    f7      rs2   qs    f3  rd    opcode

Example assembler code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| getq x5, q2       | custom0 5, 2, 0, 0  |
| getq x3, q0       | custom0 3, 0, 0, 0  |
| getq x1, q3       | custom0 1, 3, 0, 0  |

#### setq qd, rs

This instruction copies the value from a general-purpose register to a
q-register. This instruction is encoded under the `custom0` opcode:

    0000001 00000 XXXXX 000 000XX 0001011
    f7      rs2   rs    f3  qd    opcode

Example assembler code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| setq q2, x5       | custom0 2, 5, 0, 1  |
| setq q0, x3       | custom0 0, 3, 0, 1  |
| setq q3, x1       | custom0 3, 1, 0, 1  |

#### retirq

Return from interrupt. This instruction copies the value from `q0`
to the program counter and re-enables interrupts. This instruction is
encoded under the `custom0` opcode:

    0000010 00000 00000 000 00000 0001011
    f7      rs2   rs    f3  rd    opcode

Example assembler code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| retirq            | custom0 0, 0, 0, 2  |

#### maskirq

The "IRQ Mask" register contains a bitmask of masked (disabled) interrupts.
This instruction writes a new value to the irq mask register and reads the old
value. This instruction is encoded under the `custom0` opcode:

    0000011 00000 XXXXX 000 XXXXX 0001011
    f7      rs2   rs    f3  rd    opcode

Example assembler code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| maskirq x1, x2    | custom0 1, 2, 0, 3  |

The processor starts with all interrupts disabled.

An illegal instruction or bus error while the illegal instruction or bus error
interrupt is disabled will cause the processor to halt.

#### waitirq

Pause execution until an interrupt triggers. This instruction is encoded under the
`custom0` opcode. The bitmask of pending IRQs is written to `rd`.

    0000100 00000 00000 000 XXXXX 0001011
    f7      rs2   rs    f3  rd    opcode

Example assembler code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| waitirq x1        | custom0 1, 0, 0, 4  |

#### timer

Reset the timer counter to a new value. The counter counts down clock cycles and
triggers the timer interrupt when transitioning from 1 to 0. Setting the
counter to zero disables the timer. The old value of the counter is written to
`rd`.

    0000101 00000 XXXXX 000 XXXXX 0001011
    f7      rs2   rs    f3  rd    opcode

Example assembler code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| timer x1, x2      | custom0 1, 2, 0, 5  |


Building a pure RV32I Toolchain:
--------------------------------

The default settings in the [riscv-tools](https://github.com/riscv/riscv-tools) build
scripts will build a compiler, assembler and linker that can target any RISC-V ISA,
but the libraries are built for RV32G and RV64G targets. Follow the instructions
below to build a complete toolchain (including libraries) that target a pure RV32I
CPU.

The following commands will build the RISC-V gnu toolchain and libraries for a
pure RV32I target, and install it in `/opt/riscv32i`:

    sudo mkdir /opt/riscv32i
    sudo chown $USER /opt/riscv32i

    git clone https://github.com/riscv/riscv-gnu-toolchain riscv-gnu-toolchain-rv32i
    cd riscv-gnu-toolchain-rv32i

    sed -i 's|--enable-languages|--with-arch=RV32I &|' Makefile.in
    sed -i 's|asm volatile|value = 0; // &|' newlib/newlib/libc/machine/riscv/ieeefp.c

    mkdir build; cd build
    ../configure --with-xlen=32 --prefix=/opt/riscv32i
    make -j$(nproc)

The commands will all be named using the prefix `riscv32-unknown-elf-`, which
makes it easy to install them side-by-side with the regular riscv-tools, which
are using the name prefix `riscv64-unknown-elf-` by default.


Todos:
------

- Optional FENCE support
- Optional Co-Processor Interface
- Optional write-through cache
- Optional support for compressed ISA
- Improved documentation and examples
- Code cleanups and refactoring of main FSM


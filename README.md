
PicoRV32 - A Size-Optimized RISC-V CPU
======================================

PicoRV32 is a CPU core that implements the [RISC-V RV32I Instruction Set](http://riscv.org/).

Tools (gcc, binutils, etc..) can be obtained via the [RISC-V Website](http://riscv.org/download.html#tab_tools).

PicoRV32 is free and open hardware licensed under the [ISC license](http://en.wikipedia.org/wiki/ISC_license)
(a license that is similar in terms to the MIT license or the 2-clause BSD license).


Features and Typical Applications:
----------------------------------

- Small (~1000 LUTs in a 7-Series Xilinx FGPA)
- High fMAX (>250 MHz on 7-Series Xilinx FGPAs)
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

### ENABLE_COUNTERS (default = 1)

This parameter enables support for the `RDCYCLE[H]`, `RDTIME[H]`, and
`RDINSTRET[H]` instructions. This instructions will cause a hardware
trap (like any other unsupported instruction) if `ENABLE_COUNTERS` is set to zero.

*Note: Strictly speaking the `RDCYCLE[H]`, `RDTIME[H]`, and `RDINSTRET[H]`
instructions are not optional for an RV32I core. But chances are they are not
going to be missed after the application code has been debugged and profiled.
This instructions are optional for an RV32E core.*

### ENABLE_REGS_16_31 (default = 1)

This parameter enables support for registers the `x16`..`x31`. The RV32E ISA
excludes this registers. However, the RV32E ISA spec requires a hardware trap
for when code tries to access this registers. This is not implemented in PicoRV32.

### ENABLE_REGS_DUALPORT (default = 1)

The register file can be implemented with two or one read ports. A dual ported
register file improves performance a bit, but can also increase the size of
the core.

### LATCHED_MEM_RDATA (default = 0)

Set this to 1 if the `mem_rdata` is kept stable by the external circuit after a
transaction. In the default configuration the PicoRV32 core only expects the
`mem_rdata` input to be valid in the cycle with `mem_valid && mem_ready` and
latches the value internally.

### ENABLE_EXTERNAL_IRQ (default = 0)

Set this to 1 to enable external IRQs.

### ENABLE_ILLINSTR_IRQ (default = 0)

Set this to 1 to enable the illigal instruction IRQ. This can be used for
software implementations of instructions such as `MUL` and `DIV`.

### ENABLE_TIMER_IRQ (default = 0)

Set this to 1 to enable the built-in timer and timer IRQ.

### PROGADDR_RESET (default = 0)

The start address of the program.

### PROGADDR_IRQ (default = 16)

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


Custom Instructions:
--------------------

### IRQ Handling

The following custom instructions are supported when IRQs are enabled.

The core has 4 additional 32-bit general-purpose registers `q0 .. q3`
that are used for IRQ handling. When an IRQ triggers, the register
`q0` contains the return address and `q1` contains the IRQ number.
Registers `q2` and `q3` are uninitialized.

#### getq rd, qs

This instruction copies the value from a q-register to a general-purpose
register. The Instruction is encoded under the `custom0` opcode:

    0000000 00000 000XX 000 XXXXX 0001011
    f7      f5    qs    f3  rd    opcode

Example assember code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| getq x5, q2       | custom0 5, 2, 0, 0  |
| getq x3, q0       | custom0 3, 0, 0, 0  |
| getq x1, q3       | custom0 1, 3, 0, 0  |

#### setq qd, rs

This instruction copies the value from a general-purpose register to a
q-register. The Instruction is encoded under the `custom0` opcode:

    0000001 00000 XXXXX 000 000XX 0001011
    f7      f5    rs    f3  qd    opcode

Example assember code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| setq q2, x5       | custom0 2, 5, 0, 1  |
| setq q0, x3       | custom0 0, 3, 0, 1  |
| setq q3, x1       | custom0 3, 1, 0, 1  |

#### retirq

Return from interrupt. This instruction copies the value from `q0`
to the program counter and enables interrupts. The Instruction is
encoded under the `custom0` opcode:

    0000010 00000 00000 000 00000 0001011
    f7      f5    rs    f3  rd    opcode

Example assember code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| retirq            | custom0 0, 0, 0, 2  |

#### maskirq

Enable/disable interrupt sources. The Instruction is encoded under the
`custom0` opcode:

    0000011 XXXXX 00000 000 00000 0001011
    f7      f5    rs    f3  rd    opcode

The following interrupt sources occupy the following bits
in the `f5` field:

| Bit   | Interrupt Source     |
| ------| ---------------------|
| f5[0] | External IRQ         |
| f5[1] | Timer Interrupt      |
| f5[2] | Illegal Instruction  |
| f5[3] | Reserved             |
| f5[4] | Reserved             |

Set bits in the IRQ mask correspond to enabled interrupt sources.

Example assember code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| maskirq 0         | custom0 0, 0, 0, 3  |
| maskirq 1         | custom0 0, 0, 1, 3  |

The processor starts with all interrupts disabled.

An illegal instruction while the illegal instruction interrupt is disabled will
cause the processor to halt.

#### waitirq (unimplemented)

Pause execution until an interrupt triggers. The Instruction is encoded under the
`custom0` opcode:

    0000100 00000 00000 000 00000 0001011
    f7      f5    rs    f3  rd    opcode

Example assember code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| waitirq           | custom0 0, 0, 0, 4  |

#### timer

Reset the timer counter to a new value. The counter counts down cycles and
triggers the timer interrupt when transitioning from 1 to 0. Setting the
counter to zero disables the timer.

    0000101 00000 XXXXX 000 00000 0001011
    f7      f5    rs    f3  rd    opcode

Example assember code using the `custom0` mnemonic:

| Instruction       | Assember Code       |
| ------------------| --------------------|
| timer x2          | custom0 0, 2, 0, 5  |


Todos:
------

- Optional FENCE support
- Optional write-through cache
- Optional support for compressed ISA
- Improved documentation and examples
- Code cleanups and refactoring of main FSM



PicoRV32 - A Size-Optimized RISC-V CPU
======================================

PicoRV32 is a CPU core that implements the [RISC-V RV32I Instruction Set](http://riscv.org/).

Tools (gcc, binutils, etc..) can be obtained via the [RISC-V Website](http://riscv.org/download.html#tab_tools).

PicoRV32 is free and open hardware licensed under the [ISC license](http://en.wikipedia.org/wiki/ISC_license)
(a license that is similar in terms to the MIT license or the 2-clause BSD license).


Features and Typical Applications:
----------------------------------

- Small (about 1000 LUTs in a 7-Series Xilinx FGPA)
- High fMAX (>250 MHz on 7-Series Xilinx FGPAs)
- Selectable native memory interface or AXI4-Lite master

This CPU is meant to be used as auxiliary processor in FPGA designs and ASICs. Due
to its high fMAX it can be integrated in most existing designs without crossing
clock domains. When operated on a lower frequency, it will have a lot of timing
slack and thus can be added to a design without compromising timing closure.

For even smaller size it is possible disable support for registers `x16`..`x31` as
well as `RDCYCLE[H]`, `RDTIME[H]`, and `RDINSTRET[H]` instructions, turning the
processor into an RV32E core.

*Note: In architectures that implement the register file in dedicated memory
resources, such as many FPGAs, disabling the 16 upper registers may not further
reduce the core size.*

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


Performance:
------------

The average Cycles per Instruction (CPI) is 6 to 8, depending on the
application code. (Most instructions, including unconditional branches and
not-taken conditional branches execute in 5 cycles. Memory load/store, taken
conditional branches, JALR, and shift operations may take more than 5 cycles.)

Dhrystone benchmark results: 0.124 DMIPS/MHz (219 Dhrystones/Second/MHz)

*This numbers apply for setups with memory that can accomodate requests within
one clock cycle. Slower memory will degrade the performance of the processor.*


Todos:
------

- Optional IRQ support
- Optional write-through cache
- Optional support for compressed ISA


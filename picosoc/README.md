
PicoSoC - A simple example SoC using PicoRV32
=============================================

This is a simple PicoRV32 example design that can run code directly from an SPI
flash chip. This example design uses the Lattice iCE40-HX8K Breakout Board.

The flash is mapped to the memory region starting at 0x01000000. The reset
vector is set to 0x01100000, i.e. at the 1MB offset inside the flash memory.

A small scratchpad memory (default 256 words, i.e. 1 kB) is mapped to address
0x00000000.

Run `make test` to run the test bench (and create `testbench.vcd`).

Run `make prog` to build the configuration bit-stream and firmware images
and upload them to a connected iCE40-HX8K Breakout Board.

| File                          | Description                                                     |
| ----------------------------- | --------------------------------------------------------------- |
| [picosoc.v](picosoc.v)        | Top-level PicoSoC Verilog module                                |
| [picosoc.v](picosoc.v)        | Top-level PicoSoC Verilog module                                |
| [spimemio.v](spimemio.v)      | Memory controller that interfaces to external SPI flash         |
| [spiflash.v](spiflash.v)      | Simulation model of an SPI flash (used by testbench.v)          |
| [testbench.v](testbench.v)    | Simple test bench for the design (requires firmware.hex).       |
| [firmware.s](firmware.s)      | Assembler source for firmware.hex/firmware.bin.                 |
| [hx8kdemo.v](hx8kdemo.v)      | FPGA-based example implementation on iCE40-HX8K Breakout Board  |
| [hx8kdemo.pcf](hx8kdemo.pcf)  | Pin constraints for implementation on iCE40-HX8K Breakout Board |


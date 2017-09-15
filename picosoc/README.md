
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

### Memory map:

| Address Range            | Description                             |
| ------------------------ | --------------------------------------- |
| 0x00000000 .. 0x00FFFFFF | Internal SRAM                           |
| 0x01000000 .. 0x01FFFFFF | External Serial Flash                   |
| 0x02000000 .. 0x02000003 | SPI Flash Controller Config Register    |
| 0x02000004 .. 0x02000007 | UART Clock Divider Register             |
| 0x02000008 .. 0x0200000B | UART Send/Recv Data Register            |
| 0x03000000 .. 0xFFFFFFFF | Memory mapped user peripherals          |

The addresses in the internal SRAM region beyond the end of the physical
SRAM map to the corresponding addresses in serial flash.

Reading from the UART Send/Recv Data Register will return the last received
byte, or -1 (all 32 bits set) when the receive buffer is empty.

The example design (hx8kdemo.v) and generic test bench (testbench.v) have 32
GPIO pins mapped to the 32 bit word at address 0x03000000.

### SPI Flash Controller Config Register:

| Bit(s) | Description                                               |
| -----: | --------------------------------------------------------- |
|     31 | MEMIO Enable (reset=1, set to 0 to bit bang SPI commands) |
|  30:20 | Reserved (read 0)                                         |
|  19:16 | IO Output enable bits in bit bang mode                    |
|  15:14 | Reserved (read 0)                                         |
|     13 | Chip select (CS) line in bit bang mode                    |
|     12 | Serial clock line in bit bang mode                        |
|   11:8 | IO data bits in bit bang mode                             |
|      7 | Reserved (read 0)                                         |
|      6 | DDR Enable bit (reset=0)                                  |
|      5 | QSPI Enable bit (reset=0)                                 |
|      4 | Continous Read Enable bit (reset=0)                       |
|    3:0 | Number of QSPI dummy cycles (reset=0)                     |


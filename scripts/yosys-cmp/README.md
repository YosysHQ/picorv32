
Synthesis results for the PicoRV32 core (in its default configuration) with Yosys 0.5+383 (git sha1 8648089), Synplify Pro and Lattice LSE from iCEcube2.2014.08, and Xilinx Vivado 2015.3.

No timing constraints were used for synthesis; only resource utilisation is compared.

Last updated: 2015-10-30


Results for iCE40 Synthesis
---------------------------

| Cell          | Yosys | Synplify Pro | Lattice LSE |
|:--------------|------:|-------------:|------------:|
| `SB_CARRY`    |   405 |          349 |         309 |
| `SB_DFF`      |   125 |          256 |         114 |
| `SB_DFFE`     |   251 |          268 |          76 |
| `SB_DFFESR`   |   172 |           39 |         147 |
| `SB_DFFESS`   |     1 |            0 |          69 |
| `SB_DFFSR`    |    69 |          137 |         134 |
| `SB_DFFSS`    |     0 |            0 |          36 |
| `SB_LUT4`     |  1795 |         1657 |        1621 |
| `SB_RAM40_4K` |     4 |            4 |           4 |

Summary:

| Cell          | Yosys | Synplify Pro | Lattice LSE |
|:--------------|------:|-------------:|------------:|
| `SB_CARRY`    |   405 |          349 |         309 |
| `SB_DFF*`     |   618 |          700 |         576 |
| `SB_LUT4`     |  1795 |         1657 |        1621 |
| `SB_RAM40_4K` |     4 |            4 |           4 |


Results for Xilinx 7-Series Synthesis
-------------------------------------

| Cell        | Yosys | Vivado |
|:------------|------:|-------:|
| `FDRE`      |   671 |    553 |
| `FDSE`      |     0 |     21 |
| `LUT1`      |    41 |    160 |
| `LUT2`      |   517 |    122 |
| `LUT3`      |    77 |    120 |
| `LUT4`      |   136 |    204 |
| `LUT5`      |   142 |    135 |
| `LUT6`      |   490 |    405 |
| `MUXF7`     |    54 |      0 |
| `MUXF8`     |    15 |      0 |
| `MUXCY`     |   420 |      0 |
| `XORCY`     |   359 |      0 |
| `CARRY4`    |     0 |     83 |
| `RAMD32`    |     0 |     72 |
| `RAMS32`    |     0 |     24 |
| `RAM64X1D`  |    64 |      0 |

Summary:

| Cell        | Yosys | Vivado |
|:------------|------:|-------:|
| `FD*`       |   671 |    574 |
| `LUT*`      |  1403 |   1146 |


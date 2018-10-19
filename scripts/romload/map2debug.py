#!/usr/bin/env python3

import re

symbol = re.compile("\s*0x([0-9a-f]+)\s+([\w_]+)")
symbol_map = {}
with open("firmware.map", "r") as fh:
    for fd in fh:
        sym = symbol.match(fd)
        if (sym):
            addr = int(sym.group(1), 16)
            symbol_map[addr] = sym.group(2)

with open("firmware_dbg.v", "w") as fh:
    for k, v in symbol_map.items():
        fh.write("`define C_SYM_{1:s} 32'h{0:08x}\n".format(k, v.upper()))
    fh.write("  task firmware_dbg;\n")
    fh.write("  input [31:0] addr;\n");
    fh.write("  begin\n");
    fh.write("    case (addr)\n");
    for k, v in symbol_map.items():
        fh.write("      32'h{0:08x} : $display(\"%t: FCALL: {1:s}\", $time);\n".format(k, v))
    fh.write("    endcase\n");
    fh.write("  end\n");
    fh.write("  endtask\n");

with open("firmware_addr.txt", "w") as fh:
    for k, v in symbol_map.items():
        fh.write("{0:08x} {1:s}\n".format(k,v))


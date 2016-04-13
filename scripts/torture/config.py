#!/usr/bin/env python3

import numpy as np

compressed_isa = np.random.randint(2)
enable_mul = np.random.randint(2)
enable_div = np.random.randint(2)

with open("config.vh", "w") as f:
    print("// march=RV32I%s%s" % (
            "M" if enable_mul or enable_div else "",
            "C" if compressed_isa else ""), file=f)
    print(".ENABLE_COUNTERS(%d)," % np.random.randint(2), file=f)
    print(".ENABLE_COUNTERS64(%d)," % np.random.randint(2), file=f)
    print(".ENABLE_REGS_DUALPORT(%d)," % np.random.randint(2), file=f)
    print(".TWO_STAGE_SHIFT(%d)," % np.random.randint(2), file=f)
    print(".BARREL_SHIFTER(%d)," % np.random.randint(2), file=f)
    print(".TWO_CYCLE_COMPARE(%d)," % np.random.randint(2), file=f)
    print(".TWO_CYCLE_ALU(%d)," % np.random.randint(2), file=f)
    print(".CATCH_MISALIGN(%d)," % np.random.randint(2), file=f)
    print(".CATCH_ILLINSN(%d)," % np.random.randint(2), file=f)
    print(".COMPRESSED_ISA(%d)," % compressed_isa, file=f)
    print(".ENABLE_MUL(%d)," % enable_mul, file=f)
    print(".ENABLE_DIV(%d)" % enable_div, file=f)

with open("riscv-torture/config/default.config", "r") as fi:
    with open("riscv-torture/config/test.config", "w") as fo:
        for line in fi:
            line = line.strip()
            if line.startswith("torture.generator.mul "):
                line = "torture.generator.mul       %s" % ("true" if enable_mul else "false")
            if line.startswith("torture.generator.divider "):
                line = "torture.generator.divider   %s" % ("true" if enable_div else "false")
            print(line, file=fo)


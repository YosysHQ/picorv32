#!/usr/bin/env python3

import sys, re, subprocess

trace_filename = sys.argv[1]
elf_filename = sys.argv[2]

insns = dict()

with subprocess.Popen(["riscv32-unknown-elf-objdump", "-d", elf_filename], stdout=subprocess.PIPE) as proc:
    while True:
        line = proc.stdout.readline().decode("ascii")
        if line == '': break
        match = re.match(r'^\s*([0-9a-f]+):\s+(\S+)\s*(.*)', line)
        if match: insns[int(match.group(1), 16)] = (int(match.group(2), 16), match.group(3).replace("\t", " "))

with open(trace_filename, "r") as f:
    pc = -1
    last_irq = False
    for line in f:
        raw_data = int(line.replace("x", "0"), 16)
        payload = raw_data & 0xffffffff
        irq_active = (raw_data & 0x800000000) != 0
        is_addr = (raw_data & 0x200000000) != 0
        is_branch = (raw_data & 0x100000000) != 0

        if irq_active and not last_irq:
            pc = 0x10

        if pc >= 0:
            if pc in insns:
                insn_opcode, insn_desc = insns[pc]
                opcode_fmt = "%08x" if (insn_opcode & 3) == 3 else "    %04x"
                print(("%s %s%08x | %08x | " + opcode_fmt + " | %s") % ("IRQ" if irq_active else "   ",
                        ">" if is_branch else "@" if is_addr else "=", payload, pc, insn_opcode, insn_desc))
                if not is_addr:
                    pc += 4 if (insn_opcode & 3) == 3 else 2
            else:
                print("%s %s%08x ** NO INFORMATION ON INSN AT %08x! **" % ("IRQ" if irq_active else "   ",
                        ">" if is_branch else "@" if is_addr else "=", payload, pc))
                pc = -1
        else:
            print("%s %s%08x ** SKIPPING DATA UNTIL NEXT BRANCH **" % ("IRQ" if irq_active else "   ",
                    ">" if is_branch else "@" if is_addr else "=", payload))

        if is_branch:
            pc = payload

        last_irq = irq_active


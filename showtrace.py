#!/usr/bin/env python3

import sys, re, subprocess

trace_filename = sys.argv[1]
elf_filename = sys.argv[2]

insns = dict()

with subprocess.Popen(["riscv32-unknown-elf-objdump", "-d", elf_filename], stdout=subprocess.PIPE) as proc:
    while True:
        line = proc.stdout.readline().decode("ascii")
        if line == '': break
        match = re.match(r'^\s*([0-9a-f]+):\s+([0-9a-f]+)\s*(.*)', line)
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
        info = "%s %s%08x" % ("IRQ" if irq_active or last_irq else "   ",
                ">" if is_branch else "@" if is_addr else "=", payload)

        if irq_active and not last_irq:
            pc = 0x10

        if pc >= 0:
            if pc in insns:
                insn_opcode, insn_desc = insns[pc]
                opname = insn_desc.split()[0]

                if insn_opcode == 0x0400000b:
                    insn_desc = "retirq"
                    opname = "retirq"

                if is_branch and opname not in ["j", "jal", "jr", "jalr", "ret", "retirq",
                        "beq", "bne", "blt", "ble", "bge", "bgt", "bltu", "bleu", "bgeu", "bgtu",
                        "beqz", "bnez", "blez", "bgez", "bltz", "bgtz"]:
                    print("%s ** UNEXPECTED BRANCH DATA FOR INSN AT %08x! **" % (info, pc))

                if is_addr and opname not in ["lb", "lh", "lw", "lbu", "lhu", "sb", "sh", "sw"]:
                    print("%s ** UNEXPECTED ADDR DATA FOR INSN AT %08x! **" % (info, pc))

                opcode_fmt = "%08x" if (insn_opcode & 3) == 3 else "    %04x"
                print(("%s | %08x | " + opcode_fmt + " | %s") % (info, pc, insn_opcode, insn_desc))
                if not is_addr:
                    pc += 4 if (insn_opcode & 3) == 3 else 2
            else:
                print("%s ** NO INFORMATION ON INSN AT %08x! **" % (info, pc))
                pc = -1
        else:
            if is_branch:
                print("%s ** FOUND BRANCH AND STARTING DECODING **" % info)
            else:
                print("%s ** SKIPPING DATA UNTIL NEXT BRANCH **" % info)

        if is_branch:
            pc = payload

        last_irq = irq_active


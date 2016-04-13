#!/usr/bin/env python3

import sys, re

dmp_pattern = re.compile('^\s+([0-9a-f]+):\s+([0-9a-f]+)\s+(\S+)')
disassembled_elf = dict()

def match_insns(s1, s2):
    if s1 == "*" or s1 == s2: return True
    if s1 == "jal" and s2.startswith("j"): return True
    if s1 == "addi" and s2 in ["li", "mv"]: return True
    if s1 == "xori" and s2 == "not": return True
    if s1 == "sub" and s2 == "neg": return True
    if s1.startswith("b") and s2.startswith("b"): return True
    if s1.startswith("s") and s2.startswith("s"): return True
    print(s1, s2)
    return False

with open(sys.argv[2], "r") as f:
    for line in f:
        match = dmp_pattern.match(line)
        if match:
            addr = match.group(1).rjust(8, '0')
            opcode = match.group(2).rjust(8, '0')
            insn = match.group(3)
            disassembled_elf[addr] = (opcode, insn)

with open(sys.argv[1], "r") as f:
    for line in f:
        line = line.split()
        if len(line) < 1 or line[0] != "debugasm":
            continue
        assert(line[1] in disassembled_elf)
        assert(line[2] == disassembled_elf[line[1]][0])
        assert(match_insns(line[3], disassembled_elf[line[1]][1]))


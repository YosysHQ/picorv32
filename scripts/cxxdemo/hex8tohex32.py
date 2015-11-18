#!/usr/bin/env python3

import fileinput
import itertools

ptr = 0
data = []

def write_data():
    if len(data) != 0:
        print("@%08x" % (ptr >> 2))
        while len(data) % 4 != 0:
            data.append(0)
        for word_bytes in zip(*([iter(data)]*4)):
            print("".join(["%02x" % b for b in reversed(word_bytes)]))

for line in fileinput.input():
    if line.startswith("@"):
        addr = int(line[1:], 16)
        if addr > ptr+4:
            write_data()
            ptr = addr
            data = []
            while ptr % 4 != 0:
                data.append(0)
                ptr -= 1
        else:
            while ptr + len(data) < addr:
                data.append(0)
    else:
        data += [int(tok, 16) for tok in line.split()]

write_data()


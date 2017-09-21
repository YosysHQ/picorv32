#!/usr/bin/env python3

import matplotlib.pyplot as plt
import numpy as np

text = """
default        : 010f52ef
dspi-8         : 008dc82f
dspi-7         : 008d6d63
dspi-6         : 008d1297
dspi-5         : 008cb7cb
dspi-4         : 008c5cff
dspi-3         : 008c0233
dspi-2         : 008ba767
dspi-1         : 008b4c9b
dspi-crm-8     : 008af1cf
dspi-crm-7     : 008a9703
dspi-crm-6     : 008a3c37
dspi-crm-5     : 0089e16b
dspi-crm-4     : 0089869f
dspi-crm-3     : 00892bd3
dspi-crm-2     : 0088d107
dspi-crm-1     : 0088763b
qspi-8         : 004a2c6f
qspi-7         : 0049d1a3
qspi-6         : 004976d7
qspi-5         : 00491c0b
qspi-4         : 0048c13f
qspi-3         : 00486673
qspi-2         : 00480ba7
qspi-1         : 0047b0db
qspi-crm-8     : 0047560f
qspi-crm-7     : 0046fb43
qspi-crm-6     : 0046a077
qspi-crm-5     : 004645ab
qspi-crm-4     : 0045eadf
qspi-crm-3     : 00459013
qspi-crm-2     : 00453547
qspi-crm-1     : 0044da7b
qspi-ddr-8     : 00288bf5
qspi-ddr-7     : 00283129
qspi-ddr-6     : 0027d65d
qspi-ddr-5     : 00277b91
qspi-ddr-4     : 002720c5
qspi-ddr-3     : 0026c5f9
qspi-ddr-2     : 00266b2d
qspi-ddr-1     : 00261061
qspi-ddr-crm-8 : 0025b595
qspi-ddr-crm-7 : 00255ac9
qspi-ddr-crm-6 : 0024fffd
qspi-ddr-crm-5 : 0024a531
qspi-ddr-crm-4 : 00244a65
qspi-ddr-crm-3 : 0023ef99
qspi-ddr-crm-2 : 002394cd
qspi-ddr-crm-1 : 00233a01
"""

labels = list()
values = list()

for line in text.split("\n"):
    if line != "":
        line = line.split()
        labels.append(line[0])
        values.append(int(line[2], 16))

plt.figure(figsize=(10, 3))
plt.title("Performance comparison for different PicoSoC SPI flash configurations")
plt.plot(range(len(labels)), values[0] / np.array(values))
plt.xticks(range(len(labels)), labels, rotation=90)

for color, x1, x2 in [["black", 0, 0], ["red", 1, 8], ["green", 9, 16],
        ["red", 17, 24], ["green", 25, 32], ["red", 33, 40], ["green", 41, 48]]:
    for t in plt.axes().xaxis.get_ticklabels()[x1:x2+1]:
        t.set_color(color)
    plt.plot([x1, x1], [0, values[0] / values[x1] - 0.2], color=color)
    plt.plot([x2, x2], [0, values[0] / values[x2] - 0.2], color=color)  
    plt.plot([x1], [values[0] / values[x1]], "k.")
    plt.plot([x2], [values[0] / values[x2]], "k.")

plt.xlim(-1, len(values))
plt.ylim(0, 9)
plt.grid()

plt.savefig("performance.png")
# plt.show()

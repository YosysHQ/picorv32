#!/usr/bin/env python3

import matplotlib.pyplot as plt
import numpy as np

uncompr_text = """
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
instns         : 0003df2d
"""

compr_text = """
default        : 00f3d36d
dspi-8         : 008008ad
dspi-7         : 007fade1
dspi-6         : 007f5315
dspi-5         : 007ef849
dspi-4         : 007e9d7d
dspi-3         : 007e42b1
dspi-2         : 007de7e5
dspi-1         : 007d8d19
dspi-crm-8     : 007d324d
dspi-crm-7     : 007cd781
dspi-crm-6     : 007c7cb5
dspi-crm-5     : 007c21e9
dspi-crm-4     : 007bc71d
dspi-crm-3     : 007b6c51
dspi-crm-2     : 007b1185
dspi-crm-1     : 007ab6b9
qspi-8         : 00434ced
qspi-7         : 0042f221
qspi-6         : 00429755
qspi-5         : 00423c89
qspi-4         : 0041e1bd
qspi-3         : 004186f1
qspi-2         : 00412c25
qspi-1         : 0040d159
qspi-crm-8     : 0040768d
qspi-crm-7     : 00401bc1
qspi-crm-6     : 003fc0f5
qspi-crm-5     : 003f6629
qspi-crm-4     : 003f0b5d
qspi-crm-3     : 003eb091
qspi-crm-2     : 003e55c5
qspi-crm-1     : 003dfaf9
qspi-ddr-8     : 00255d87
qspi-ddr-7     : 002502bb
qspi-ddr-6     : 0024a7ef
qspi-ddr-5     : 00244d23
qspi-ddr-4     : 0023f257
qspi-ddr-3     : 0023978b
qspi-ddr-2     : 00233cbf
qspi-ddr-1     : 0022e1f3
qspi-ddr-crm-8 : 00228727
qspi-ddr-crm-7 : 00222c5b
qspi-ddr-crm-6 : 0021d18f
qspi-ddr-crm-5 : 002176c3
qspi-ddr-crm-4 : 00211bf7
qspi-ddr-crm-3 : 0020c12b
qspi-ddr-crm-2 : 0020665f
qspi-ddr-crm-1 : 00200b93
instns         : 0003df2d
"""

labels = list()
uncompr_values = list()
compr_values = list()

for line in uncompr_text.split("\n"):
    if line != "":
        line = line.split()
        if line[0] == "instns":
            for i in range(len(uncompr_values)):
                uncompr_values[i] = int(line[2], 16) / uncompr_values[i]
        else:
            labels.append(line[0])
            uncompr_values.append(int(line[2], 16))

for line in compr_text.split("\n"):
    if line != "":
        line = line.split()
        if line[0] == "instns":
            for i in range(len(compr_values)):
                compr_values[i] = int(line[2], 16) / compr_values[i]
        else:
            compr_values.append(int(line[2], 16))

print(np.array(compr_values) / np.array(uncompr_values))

values = list()
for i in range(len(compr_values)):
    values.append(uncompr_values[i] / uncompr_values[0])
    # values.append(compr_values[i] / compr_values[0])

values = np.array(values)
print(values)

plt.figure(figsize=(10, 5))
plt.title("Performance comparison for different PicoSoC SPI flash configurations")
plt.plot(range(len(labels)), values)
plt.xticks(range(len(labels)), labels, rotation=80)

for color, x1, x2 in [["black", 0, 0], ["red", 1, 8], ["green", 9, 16],
        ["red", 17, 24], ["green", 25, 32], ["red", 33, 40], ["green", 41, 48]]:
    for t in plt.axes().xaxis.get_ticklabels()[x1:x2+1]:
        t.set_color(color)
    plt.plot([x1, x1], [0, values[x1] - 0.2], color=color)
    plt.plot([x2, x2], [0, values[x2] - 0.2], color=color)
    plt.plot([x1], [values[x1]], "k.")
    plt.plot([x2], [values[x2]], "k.")

plt.xlim(-1, len(labels))
plt.ylim(0, 9)
plt.grid()

plt.gcf().subplots_adjust(bottom=0.3)
plt.savefig("performance.png")
# plt.show()

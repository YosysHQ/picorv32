#!/bin/bash
set -ex
echo -n > firmware.hex
yosys -l synth.log -p 'synth_ice40 -top top -blif synth.blif' ../../picorv32.v top.v
arachne-pnr -d 8k -o synth.txt synth.blif
icepack synth.txt synth.bin

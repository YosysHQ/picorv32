#!/bin/bash
set -ex
yosys -ql synth.log -p 'synth_ice40 -blif synth.blif' ../../picorv32.v
arachne-pnr -d 8k -o synth.txt synth.blif
icepack synth.txt synth.bin

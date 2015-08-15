#!/bin/bash
set -ex
yosys -qv1 sync.ys
time python3 sync.py 

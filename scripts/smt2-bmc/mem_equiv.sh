#!/bin/bash
set -ex
yosys -qv1 mem_equiv.ys
time python3 mem_equiv.py 

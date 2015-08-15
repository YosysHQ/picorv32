#!/bin/bash
set -ex
yosys -qv1 async.ys
time python3 async.py 

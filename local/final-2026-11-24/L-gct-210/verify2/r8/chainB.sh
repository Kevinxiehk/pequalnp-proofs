#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verify2/r8
timeout 1700 python3 -I f4b_repro.py exact C1G FULL 0 1 60
echo CHAIN_B_DONE

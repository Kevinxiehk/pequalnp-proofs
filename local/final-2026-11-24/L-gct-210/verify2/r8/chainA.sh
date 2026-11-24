#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verify2/r8
for a in "C3b LEVEL 1 0" "C12ab LEVEL 1 0" "C3c FULL 1 1" "C12ac FULL 1 1"; do timeout 1500 python3 -I f4b_repro.py exact $a 120; done
echo CHAIN_A_DONE

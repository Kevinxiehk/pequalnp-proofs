#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r7/s5; ulimit -v 2500000
for CH in "$@"; do timeout 600 Singular -q A_$CH.sing > A_$CH.out 2>&1; done

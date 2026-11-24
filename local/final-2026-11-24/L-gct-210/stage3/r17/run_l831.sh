#!/bin/sh
cd /home/kevxhk/work/L-gct-210/stage3/r17
ulimit -v 500000
for J in 0 1 2 3 4; do for XC in v0 v1 v2 v3 v4 a1 a2 a3 a4 b1 b2 b3 b4; do
  f=$(python3 -I leaf8_31x.py $J $XC 0); timeout 120 Singular -q $f 2>&1 | grep LEAF8
done; done

#!/bin/sh
# special locus h_0 = e_0 of stratum (II): all 10 x*-charts, over Q (slimgb), with the components printed when non-unit (mod 32003 decomposition separately)
cd /home/kevxhk/work/L-gct-210/stage3/r17
ulimit -v 700000
for I in 0 1; do for J in 0 1 2 3 4; do
  f=$(python3 -I spec_exact.py $I $J 0)
  timeout 300 Singular -q $f 2>&1 | grep -v redefin | grep SPEC
done; done

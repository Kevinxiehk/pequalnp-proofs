#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r9
for INF in x 1 12 123 0 01 012 0123; do
  r=$(timeout 1500 python3 -I ../r8/t31e_stages.py M0K:$INF 2147483629 p5b 0 m0/alphaK_$INF "Z1;Z2;Z12" 1200 2>&1 | grep -E "stage|VERDICT" | tr '\n' ' ')
  echo "alpha INF={$INF}: $r"
done
echo ALPHA_DONE

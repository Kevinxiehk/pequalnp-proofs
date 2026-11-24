#!/bin/bash
# [DC3] structured, m = (1,1,-2,0,0) and (1,w,w^2,0,0) at p = 2147483629 (single thread, timeout 90 s)
ulimit -v 2500000
G=/home/kevxhk/work/L-gct-210/verifyfl/exact/gen_n1s.py
for M in m11m2 iso; do
  python3 -I $G 2147483629 $M 3 /home/kevxhk/work/L-gct-210/verifyfl/r7/dc3 run timeout=90
done
echo CHAIN_B_DONE

#!/bin/bash
# [DC3] structured, m = (1,2,-3,0,0), two more primes (single thread each case, timeout 90 s)
ulimit -v 2500000
G=/home/kevxhk/work/L-gct-210/verifyfl/exact/gen_n1s.py
for P in 2147483497 2147483077; do
  python3 -I $G $P m12m3 3 /home/kevxhk/work/L-gct-210/verifyfl/r7/dc3 run timeout=90
done
echo CHAIN_A_DONE

#!/bin/bash
cd /home/kevxhk/work/L-gct-210/rows/r7/x5
ulimit -v 2500000
for P in 2147483629 2147483497 2147483077; do for ch in 11 10 01 00; do
  python3 -I x5gen.py $P $ch x5_${ch}_$P.sing > /dev/null; timeout 600 Singular -q x5_${ch}_$P.sing > x5_${ch}_$P.out 2>&1
  python3 -I x5gen.py $P $ch x5c_${ch}_$P.sing cal > /dev/null; timeout 600 Singular -q x5c_${ch}_$P.sing > x5c_${ch}_$P.out 2>&1
done; done
echo ALLDONE

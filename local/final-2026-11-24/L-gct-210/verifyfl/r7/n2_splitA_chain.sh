#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r7
M=${1:-m12m3}
for vt in ab z1 z2; do for lc in 0 1; do
  timeout 1500 python3 -I n2_split.py 2147483629 $M R1:$vt:$lc a n2/R1_${M}_${vt}_$lc 1200 2>&1 | grep -E "VERDICT|stage 1" || echo "VERDICT n2 R1:$vt:$lc $M: TIMEOUT/FAIL"
done; done
echo N2A_DONE

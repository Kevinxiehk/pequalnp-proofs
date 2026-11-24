#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r11; mkdir -p t31A
for C in A B; do for Z in chi1 R2:01:ab R2:01:z1 R2:01:z2 R2:02:ab R2:02:z1 R2:02:z2 R2:12:ab R2:12:z1 R2:12:z2; do
  timeout 1800 python3 -I t31A_sym.py 2147483629 $C $Z t31A/${C}_$(echo $Z | tr ':' '_') 2>&1 | grep VERDICT || echo "VERDICT t31A-sym chart $C $Z: TIMEOUT/FAIL"
done; done
echo T31A_DONE

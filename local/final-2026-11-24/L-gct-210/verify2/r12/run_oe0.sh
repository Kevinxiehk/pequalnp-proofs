#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r12
ulimit -v 2500000
for args in "2121V0 col,4,3 3 col,3" "11121A1 col,4,3 3 col,3" "213def none 4 col,4" "22_2 row,0,1 0 row,1"; do
  set -- $args
  timeout 1500 python3 -I rr_omega_e0.py $1 $2 $3 $4 > oe0_$1.log 2>&1
done
echo done > oe0_done.flag

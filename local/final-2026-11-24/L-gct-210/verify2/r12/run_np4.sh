#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verify2/r12
ulimit -v 2500000
for args in "211iii row,0,2 0 row,1" "11121A1 col,4,3 3 col,3" "213def none 4 col,4"; do
  set -- $args
  timeout 1500 python3 -I rr_omega_e0.py $1 $2 $3 $4 4 > oe0np4_$1.log 2>&1
  echo "$1 npiv4: $(grep -m1 'pivot sets cover' oe0np4_$1.log | sed 's/.*COVSIZE//') | $(grep -c 'NON-unit in \[\]' oe0np4_$1.log) all-unit sets | $(grep VERDICT oe0np4_$1.log | cut -c1-80)"
done
echo done

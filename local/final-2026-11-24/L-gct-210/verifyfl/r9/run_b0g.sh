#!/bin/bash
ulimit -v 2500000
cd /home/kevxhk/work/L-gct-210/verifyfl/r9
for M in $@; do n=$(grep -c "" factors_$M.txt); for i in $(seq 0 $((n-1))); do
  r=$(timeout 900 python3 -I ../r8/t31e_stages.py B0G 2147483629 $M 0 b0g/${M}_g$i "Z;Z1;Z2;Z12" 600 gfac=factors_$M.txt:$i:lin_$M.txt 2>&1 | tail -1)
  echo "$M g$i: $r"
done; done
echo B0G_DONE

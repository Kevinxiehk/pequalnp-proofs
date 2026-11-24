#!/bin/bash
# verifyfl VF-M0-ALPHA-UPDATE: last three (alpha) charts of [T31] split A for m0 = (1,1,1,1,-4), big slot, one at a time
R9=/home/kevxhk/work/L-gct-210/verifyfl/r9
for INF in 0 1 x; do
  echo "$(date -u +%T) M0 alpha chart $INF start"
  ( cd $R9 && /home/kevxhk/work/tools/bigslot.sh sh -c "ulimit -v 10000000; MSOLVE_THREADS=1 timeout 11000 python3 -I ../r8/t31e_stages.py M0K:$INF 2147483629 p5b 0 m0/Q_alphaK_$INF 'Z1;Z2;Z12' 10800" ) > /home/kevxhk/work/runs/m0alpha_$INF.log 2>&1
  echo "$(date -u +%T) M0 alpha chart $INF end: $(grep -h VERDICT /home/kevxhk/work/runs/m0alpha_$INF.log | tail -1)"
done
echo "$(date -u +%T) ALLDONE"

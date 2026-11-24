#!/bin/bash
# verifyfl VF-P5B-T22-BIG: the remaining [T22] cells for m0 = (1,1,1,1,-4), big slot, one at a time, N-GB first
R9=/home/kevxhk/work/L-gct-210/verifyfl/r9
for C in 12 11 2 1 0; do
  echo "$(date -u +%T) p5b T22 cell $C start"
  ( cd $R9 && /home/kevxhk/work/tools/bigslot.sh sh -c "ulimit -v 10000000; MSOLVE_THREADS=1 timeout 11000 python3 -I n3g_case.py 2147483629 p5b $C n3g 10800 7200" ) > /home/kevxhk/work/runs/p5bt22_c$C.log 2>&1
  echo "$(date -u +%T) p5b T22 cell $C end: $(grep -h VERDICT /home/kevxhk/work/runs/p5bt22_c$C.log | tail -1)"
done
echo "$(date -u +%T) ALLDONE"

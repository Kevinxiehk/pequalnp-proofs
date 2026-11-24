#!/bin/bash
# VF-T22H driver: hard [T22] cases, one case at a time in the big-memory slot (8 GB cap, 4 msolve threads), skipping decided cases
cd /home/kevxhk/work/L-gct-210/verifyfl/r7
for M in m12m3 m11m2 iso; do
  for C in 11 10 9 8 7 6 5 4 3 2 1 0; do
    if grep -qE "case $C .*VERDICT|VERDICT.* case $C( |$)|^VERDICT $M $C " n3_chain_$M.log n3q/*_${M}_*c${C}*.log 2>/dev/null; then echo "skip $M $C (decided)"; continue; fi
    echo "== $M case $C start $(date -u +%T)"
    /home/kevxhk/work/tools/bigslot.sh sh -c "ulimit -v 8000000; MSOLVE_THREADS=4 timeout 11000 python3 -I n3_case.py 2147483629 $M $C n3q 10800" > /home/kevxhk/work/runs/t22h_${M}_c$C.log 2>&1
    echo "== $M case $C end $(date -u +%T): $(grep -h VERDICT /home/kevxhk/work/runs/t22h_${M}_c$C.log | tail -1)"
  done
done
echo ALLDONE

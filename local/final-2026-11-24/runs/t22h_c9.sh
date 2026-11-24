#!/bin/bash
# retry of VF-T22H m12m3 case 9 (first attempt died: bigslot.sh was rewritten in place while running)
cd /home/kevxhk/work/L-gct-210/verifyfl/r7
echo "== m12m3 case 9 retry start $(date -u +%T)"
/home/kevxhk/work/tools/bigslot.sh sh -c "ulimit -v 8000000; MSOLVE_THREADS=4 timeout 11000 python3 -I n3_case.py 2147483629 m12m3 9 n3q 10800" > /home/kevxhk/work/runs/t22h_m12m3_c9.log 2>&1
echo "== m12m3 case 9 retry end $(date -u +%T): $(grep -h VERDICT /home/kevxhk/work/runs/t22h_m12m3_c9.log | tail -1)"

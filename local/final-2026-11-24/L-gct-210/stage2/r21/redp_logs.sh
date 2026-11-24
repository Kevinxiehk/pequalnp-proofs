#!/bin/bash
# re-runs (with logs) of the RED-p members and Kt3 lines cited in the F2COL-TABLE whose output had only been printed to the terminal.
cd /home/kevxhk/work/L-gct-210/stage2
P=2147483629
echo "== R2 nu=0, a=(0,0,1): setup + kernel test + full charts $(date -u +%H:%M:%S)"
C=$(timeout 600 python3 -I r16_F2col_setup.py R2 $P "nu=0,a1=0,a2=0,a3=1" 2>&1 | grep -oE "/home[^ ]*cache_[0-9a-f]+\.pkl" | head -1); echo "cache $C"
timeout 600 python3 -I r16_Kauto.py $C 2>&1 | grep -E "FIXED MEMBER|NOT the standard"
MSV=2000000 timeout 900 python3 -I r17_charts.py $C $P 2>&1 | grep -E "NONUNIT|FAILED|rational|RESULT"
echo "== R1 cross-type lam=0, a=(0,0,1): setup + kernel test + full charts $(date -u +%H:%M:%S)"
C=$(timeout 600 python3 -I r16_F2col_setup.py R1 $P "lam=0,a1=0,a2=0,a3=1" 2>&1 | grep -oE "/home[^ ]*cache_[0-9a-f]+\.pkl" | head -1); echo "cache $C"
timeout 600 python3 -I r16_Kauto.py $C 2>&1 | grep -E "FIXED MEMBER|NOT the standard"
MSV=2000000 timeout 900 python3 -I r17_charts.py $C $P 2>&1 | grep -E "NONUNIT|FAILED|rational|RESULT"
echo "== R1 jump point lam=0, a=(0,-8,7): reduced charts Gr(3,8) (k in L'') $(date -u +%H:%M:%S)"
SAT=0 MSV=2000000 timeout 900 python3 -I r16_F2col_K2.py r16/cache_8967677ebd48.pkl $P "a2=-8" 2>&1 | grep -E "subfamily|kernel vector|q0|eliminating|NONUNIT|FAILED|rational|RESULT"
for C in f9b8fe0eac09 9a05094bcabd 698f1aa37be6 f309f7a3a7bc; do echo "== Kt3 R2 line cache_$C $(date -u +%H:%M:%S)"; STO=300 MSV=1500000 timeout 1500 python3 -I r18_Kt3.py r16/cache_$C.pkl 2>&1 | grep -E "fix|k =|chart|RESULT"; done
echo "ALL DONE $(date -u +%H:%M:%S)"

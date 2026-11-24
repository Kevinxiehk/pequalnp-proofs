#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2
until grep -q "ALL DONE" r18/ktlines_B.log; do sleep 20; done
echo "== fixed member nu=-1/2, a=(2,1,1) $(date -u +%H:%M:%S)"
C=$(timeout 600 python3 -I r16_F2col_setup.py R2 2147483629 "nu=-1/2,a1=2,a2=1,a3=1" 2>&1 | grep -oE "/home[^ ]*cache_[0-9a-f]+\.pkl" | head -1)
timeout 600 python3 -I r16_Kauto.py $C 2>&1 | grep -E "FIXED MEMBER|NOT the standard"
MSV=2000000 timeout 900 python3 -I r17_charts.py $C 2147483629 2>&1 | grep -E "NONUNIT|FAILED|RESULT"
echo "ALL DONE $(date -u +%H:%M:%S)"

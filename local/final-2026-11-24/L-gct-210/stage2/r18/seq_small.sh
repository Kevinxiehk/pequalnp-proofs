#!/bin/bash
# one job at a time, small memory (big slot busy): (0,0,1) char-0 timeout systems, D3A degeneracy, D3A T1cert (Singular), KU (0,0,0) Singular.
cd /home/kevxhk/work/L-gct-210/stage2
echo "== f309f7a3a7bc msolve char 0 $(date -u +%H:%M:%S)"
SYSLIST="0:1:0-1-3;0:1:0-1-5;0:1:0-1-6;0:1:0-3-5;0:1:0-3-6;0:1:0-4-6;0:1:0-5-6;0:1:1-4-6;0:1:1-5-6;1:1:0-1-3;1:1:0-1-5;1:1:0-1-6;1:1:0-3-5;1:1:0-3-6;1:1:0-4-6;1:1:0-5-6;1:1:1-5-6" MSV=2000000 timeout 1800 python3 -I r18_Kt2.py r16/cache_f309f7a3a7bc.pkl 0 2>&1 | grep -E "NONUNIT|FAILED|RESULT"
echo "== D3A big-kernel degeneracy $(date -u +%H:%M:%S)"; timeout 2400 python3 -I r18_D3A_deg.py 2>&1 | cut -c1-400
echo "== D3A T1cert Singular $(date -u +%H:%M:%S)"; ENGINE=sing EXC="(a2-1)*(a2+a3+1)" MSV=1000000 timeout 1500 python3 -I r18_T1cert_D3A.py 0 2>&1 | grep -E "lcm|excluded|NONUNIT|FAILED|RESULT"
echo "== KU (0,0,0) Singular $(date -u +%H:%M:%S)"; ENGINE=sing STO=120 MSV=1000000 timeout 5400 python3 -I r18_KU.py r16/cache_0d3623f0f596.pkl 0 2 2>&1 | grep -E "U-chart|RESULT"
echo "ALL DONE $(date -u +%H:%M:%S)"

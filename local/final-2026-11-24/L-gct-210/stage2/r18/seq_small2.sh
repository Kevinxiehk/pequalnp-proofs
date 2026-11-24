#!/bin/bash
# one small job at a time (big slot busy): D3A degeneracy (fast version), D3A T1cert (Singular), KU (0,0,0) Singular.
cd /home/kevxhk/work/L-gct-210/stage2
echo "== D3A big-kernel degeneracy (fast) $(date -u +%H:%M:%S)"; timeout 2400 python3 -I r18_D3A_deg2.py 2>&1 | cut -c1-600
echo "== D3A T1cert Singular $(date -u +%H:%M:%S)"; ENGINE=sing EXC="(a2-1)*(a2+a3+1)" MSV=1000000 timeout 1500 python3 -I r18_T1cert_D3A.py 0 2>&1 | grep -E "lcm|excluded|NONUNIT|FAILED|RESULT"
echo "== KU (0,0,0) Singular $(date -u +%H:%M:%S)"; ENGINE=sing STO=120 MSV=1000000 timeout 5400 python3 -I r18_KU.py r16/cache_0d3623f0f596.pkl 0 2 2>&1 | grep -E "U-chart|RESULT"
echo "ALL DONE $(date -u +%H:%M:%S)"

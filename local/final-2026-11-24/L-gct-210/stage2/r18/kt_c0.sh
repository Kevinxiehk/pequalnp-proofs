#!/bin/bash
# Singular-timeout systems of the Kt line runs: msolve char 0 now [M0]; Singular with 6 GB / 1 h goes to the big slot (QUEUE ST2-KTBIG).
cd /home/kevxhk/work/L-gct-210/stage2
until grep -q "ALL DONE" r18/ktlines_B.log; do sleep 30; done
run(){ echo "== $1 msolve char 0 $(date -u +%H:%M:%S)"; SYSLIST="$2" MSV=2000000 timeout 1800 python3 -I r18_Kt2.py r16/cache_$1.pkl 0 2>&1 | grep -E "NONUNIT|FAILED|RESULT" ; }
run f9b8fe0eac09 "0:1:0-1-5;0:1:0-1-6;1:1:0-1-5;1:1:0-1-6"
run 9a05094bcabd "0:1:0-1-5;0:1:0-1-6;0:1:0-3-5;0:1:0-3-6;1:1:0-1-5;1:1:0-1-6;1:1:0-3-5;1:1:0-3-6"
run 698f1aa37be6 "0:1:0-2-5;0:1:0-2-6;0:1:0-3-5;0:1:0-3-6;0:1:0-4-5;0:1:0-4-6;1:1:0-2-5;1:1:0-2-6;1:1:0-3-5;1:1:0-3-6;1:1:0-4-5;1:1:0-4-6;1:6:0-1-3;1:6:0-1-4"
echo "== D3A big-kernel degeneracy $(date -u +%H:%M:%S)"; timeout 1500 python3 -I r18_D3A_deg.py 2>&1 | cut -c1-400
echo "== D3A T1cert Singular $(date -u +%H:%M:%S)"; ENGINE=sing EXC="(a2-1)*(a2+a3+1)" timeout 1500 python3 -I r18_T1cert_D3A.py 0 2>&1 | grep -E "lcm|excluded|NONUNIT|FAILED|RESULT"
echo "ALL DONE $(date -u +%H:%M:%S)"

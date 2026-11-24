#!/bin/bash
# re-run the Singular timeouts of the Kt line runs with STO=600 (proof grade if [1]); remaining timeouts -> msolve char 0 [M0].
cd /home/kevxhk/work/L-gct-210/stage2
until grep -q "ALL DONE" r18/ktlines_B.log; do sleep 30; done
run(){ echo "== $1 Singular STO=600 $(date -u +%H:%M:%S)"; SYSLIST="$2" ENGINE=sing STO=600 MSV=2000000 timeout 7000 python3 -I r18_Kt2.py r16/cache_$1.pkl 0 2>&1 | grep -E "TIMEOUT|NONUNIT|FAILED|RESULT" ; }
run f9b8fe0eac09 "0:1:0-1-5;0:1:0-1-6;1:1:0-1-5;1:1:0-1-6"
run 9a05094bcabd "0:1:0-1-5;0:1:0-1-6;0:1:0-3-5;0:1:0-3-6;1:1:0-1-5;1:1:0-1-6;1:1:0-3-5;1:1:0-3-6"
run 698f1aa37be6 "0:1:0-2-5;0:1:0-2-6;0:1:0-3-5;0:1:0-3-6;0:1:0-4-5;0:1:0-4-6;1:1:0-2-5;1:1:0-2-6;1:1:0-3-5;1:1:0-3-6;1:1:0-4-5;1:1:0-4-6;1:6:0-1-3;1:6:0-1-4"
echo "ALL DONE $(date -u +%H:%M:%S)"

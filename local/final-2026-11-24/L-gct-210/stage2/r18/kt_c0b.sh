#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2
until grep -q "ALL DONE" r18/kt_c0.log; do sleep 30; done
echo "== f309f7a3a7bc msolve char 0 $(date -u +%H:%M:%S)"
SYSLIST="0:1:0-1-3;0:1:0-1-5;0:1:0-1-6;0:1:0-3-5;0:1:0-3-6;0:1:0-4-6;0:1:0-5-6;0:1:1-4-6;0:1:1-5-6;1:1:0-1-3;1:1:0-1-5;1:1:0-1-6;1:1:0-3-5;1:1:0-3-6;1:1:0-4-6;1:1:0-5-6;1:1:1-5-6" MSV=2000000 timeout 1800 python3 -I r18_Kt2.py r16/cache_f309f7a3a7bc.pkl 0 2>&1 | grep -E "NONUNIT|FAILED|RESULT"
echo "ALL DONE $(date -u +%H:%M:%S)"

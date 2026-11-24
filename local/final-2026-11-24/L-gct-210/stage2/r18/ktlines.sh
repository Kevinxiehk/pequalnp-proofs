#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2
for C in "$@"; do echo "== $C $(date -u +%H:%M:%S)"; ENGINE=sing STO=120 MSV=2000000 timeout 3000 python3 -I r18_Kt.py r16/cache_$C.pkl 0 2>&1 | grep -E "dim K|Rabin|chart j0|NONUNIT|FAILED|TIMEOUT|RESULT" | cut -c1-200; done
echo "ALL DONE $(date -u +%H:%M:%S)"

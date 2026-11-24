#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2
until grep -q "ALL DONE" r18/ktlines_A.log; do sleep 20; done
echo "== KU (0,0,0) m=2 Singular $(date -u +%H:%M:%S)"
ENGINE=sing STO=120 MSV=2000000 timeout 3000 python3 -I r18_KU.py r16/cache_0d3623f0f596.pkl 0 2 2>&1 | grep -E "dim K|Rabin|U-chart|RESULT" | cut -c1-200
echo "ALL DONE $(date -u +%H:%M:%S)"

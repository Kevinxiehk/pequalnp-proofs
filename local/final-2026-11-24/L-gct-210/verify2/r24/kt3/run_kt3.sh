#!/bin/bash
# verify2 r24: re-run stage2's Kt3 (R19-1) on the four kap = 2 R2 lines (no saved logs found); temp files in /tmp/st2_Kt3_<pid>.
# Waits for my rank-2 Q(i) job (run34.sh, PID given as $1) to finish first (one job > 0.5 GB at a time).
while kill -0 "$1" 2>/dev/null; do sleep 20; done
cd /home/kevxhk/work/L-gct-210/stage2
for C in f9b8fe0eac09 9a05094bcabd 698f1aa37be6 f309f7a3a7bc; do
  echo "== Kt3 $C $(date -u +%H:%M:%S)"
  STO=600 MSV=2000000 timeout 1800 python3 -I r18_Kt3.py r16/cache_$C.pkl 2>&1 | grep -E "fix|discriminant|NONUNIT|timeout|RESULT|Error|assert" | cut -c1-220
done
echo "ALL DONE $(date -u +%H:%M:%S)"

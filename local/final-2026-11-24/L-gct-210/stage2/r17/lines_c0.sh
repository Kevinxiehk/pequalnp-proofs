#!/bin/bash
# R2 nu-lines (cut survivors), char-0 msolve (multimodular, evidence) on all 70 charts; exact T_1 on the line.
cd /home/kevxhk/work/L-gct-210/stage2
for A in "$@"; do
  echo "== R2 $A $(date -u +%H:%M:%S)"
  O=$(timeout 600 python3 -I r16_F2col_setup.py R2 2147483629 "$A" 2>&1); echo "$O" | grep -E "rank-jump|dim T_1" | sed 's/^/   /'
  C=$(echo "$O" | grep -oE "/home[^ ]*cache_[0-9a-f]+\.pkl" | head -1)
  [ -z "$C" ] && { echo "SETUP FAILED"; continue; }
  MSV=2000000 timeout 1500 python3 -I r17_charts.py $C 0 2>&1 | grep -E "Rabinowitsch|NONUNIT|FAILED|RESULT|timed out" | sed 's/^/   /'
done
echo "ALL DONE $(date -u +%H:%M:%S)"

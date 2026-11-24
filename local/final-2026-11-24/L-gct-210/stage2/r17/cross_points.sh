#!/bin/bash
# cross-type (lam = 0) pieces left by the S_4 cut: fixed members (1,1,1), (0,1,1), (0,0,0) [a4 = 1], and the 1-parameter family a1 = a2 = 0.
cd /home/kevxhk/work/L-gct-210/stage2
for A in "a1=1,a2=1,a3=1" "a1=0,a2=1,a3=1" "a1=0,a2=0,a3=0"; do
  echo "== R1 lam=0,$A $(date -u +%H:%M:%S)"
  C=$(timeout 600 python3 -I r16_F2col_setup.py R1 2147483629 "lam=0,$A" 2>&1 | grep -oE "/home[^ ]*cache_[0-9a-f]+\.pkl" | head -1)
  [ -z "$C" ] && { echo "SETUP FAILED"; continue; }
  K=$(timeout 600 python3 -I r16_Kauto.py $C 2>&1 | grep -E "FIXED MEMBER|NOT the standard")
  echo "   kernel test: $K"
  case "$K" in *KILLED*) continue;; esac
  MSV=2000000 timeout 900 python3 -I r17_charts.py $C 2147483629 2>&1 | grep -E "NONUNIT|FAILED|RESULT" | sed 's/^/   /'
done
RUL=R1 timeout 1200 r16/fam_batch.sh "lam=0,a1=0,a2=0" | grep -v "^c=\|cof =\|non-exceptional factors:"
echo "ALL DONE $(date -u +%H:%M:%S)"

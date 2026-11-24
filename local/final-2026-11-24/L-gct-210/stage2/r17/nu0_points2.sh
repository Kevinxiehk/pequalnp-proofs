#!/bin/bash
# Fixed members of the nu = 0 slice left by the symmetry cut (same point list as the generic-nu lines, R16-5): kernel test first, then full charts.
cd /home/kevxhk/work/L-gct-210/stage2
for A in "a1=0,a2=0,a3=1" "a1=0,a2=0,a3=0" "a1=0,a2=0,a3=-1"; do
  echo "== R2 nu=0,$A $(date -u +%H:%M:%S)"
  C=$(timeout 600 python3 -I r16_F2col_setup.py R2 2147483629 "nu=0,$A" 2>&1 | grep -oE "/home[^ ]*cache_[0-9a-f]+\.pkl" | head -1)
  [ -z "$C" ] && { echo "SETUP FAILED"; continue; }
  K=$(timeout 600 python3 -I r16_Kauto.py $C 2>&1 | grep -E "FIXED MEMBER|NOT the standard")
  echo "   kernel test: $K"
  case "$K" in *KILLED*) continue;; esac
  MSV=2000000 timeout 900 python3 -I r17_charts.py $C 2147483629 2>&1 | grep -E "NONUNIT|FAILED|RESULT" | sed 's/^/   /'
done
echo "ALL DONE $(date -u +%H:%M:%S)"

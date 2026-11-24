#!/bin/bash
# R1 lines left by the S_3 cut (RD = {(1,1,1)} in char p, exact confirmation pending): setup on the line (lam free) + general kernel bound + exceptional lam.
cd /home/kevxhk/work/L-gct-210/stage2
for A in "a1=1,a2=1,a3=1" "a1=2,a2=1,a3=1" "a1=3,a2=0,a3=1" "a1=4,a2=0,a3=1" "a1=22/7,a2=0,a3=6/7" "a1=11/3,a2=0,a3=7/6" "a1=4,a2=0,a3=0" "a1=6,a2=0,a3=0" "a1=0,a2=1,a3=1" "a1=0,a2=1/7,a3=-8/7"; do
  echo "== R1 $A $(date -u +%H:%M:%S)"
  C=$(timeout 900 python3 -I r16_F2col_setup.py R1 2147483629 "$A" 2>&1 | grep -oE "/home[^ ]*cache_[0-9a-f]+\.pkl" | head -1)
  [ -z "$C" ] && { echo "SETUP FAILED"; continue; }
  echo "   cache $C"
  timeout 600 python3 -I r18_linerank.py $C 2>&1 | grep -E "fix|=>" | cut -c1-330
  timeout 600 python3 -I r18_lineexc.py $C 2>&1 | grep "exceptional" | cut -c1-200
done
echo "ALL DONE $(date -u +%H:%M:%S)"

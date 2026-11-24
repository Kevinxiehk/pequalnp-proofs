#!/bin/bash
# R2 nu-lines left by the S_3 symmetry cut (NOTES-stage2 R16-5), not already in ST2-R2LINES: full Gr(4,8) FO2-joint, 1 parameter nu, hardened driver.
cd /home/kevxhk/work/L-gct-210/stage2
for A in "a1=2,a2=1,a3=1" "a1=3,a2=0,a3=1" "a1=4,a2=0,a3=1" "a1=22/7,a2=0,a3=6/7" "a1=11/3,a2=0,a3=7/6" "a1=4,a2=0,a3=0" "a1=6,a2=0,a3=0" "a1=0,a2=1,a3=1" "a1=0,a2=1/7,a3=-8/7" "a1=0,a2=0,a3=1" "a1=0,a2=0,a3=0" "a1=0,a2=0,a3=-1"; do
  echo "== R2 $A $(date -u +%H:%M:%S)"
  MSV=2000000 timeout 3600 python3 -I r13_F2col_v4_fx.py R2 2147483629 "$A" 2>&1 | grep -E "rank-jump|dim T_1|complement valid|denominators|Rabinowitsch|NONUNIT|parameter ideal|FAILED|RESULT"
done
echo "ALL DONE $(date -u +%H:%M:%S)"

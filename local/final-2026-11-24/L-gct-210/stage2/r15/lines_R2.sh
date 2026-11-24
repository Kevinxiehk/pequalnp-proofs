#!/bin/bash
# R2 survivor lines a in {(1,0,0),(1,0,1),(1,1,0),(1,1,1)}, nu free: full Gr(4,8) FO2-joint, 1 parameter, hardened driver (NOTES-stage2 R15-5).
cd /home/kevxhk/work/L-gct-210/stage2
for A in "a1=1,a2=0,a3=0" "a1=1,a2=0,a3=1" "a1=1,a2=1,a3=0" "a1=1,a2=1,a3=1"; do
  echo "== R2 $A $(date -u +%H:%M:%S)"
  MSV=2000000 timeout 3600 python3 -I r13_F2col_v4_fx.py R2 2147483629 "$A" 2>&1 | grep -E "rank-jump|dim T_1|complement valid|denominators|Rabinowitsch|NONUNIT|parameter ideal|FAILED|RESULT"
done
echo "ALL DONE $(date -u +%H:%M:%S)"

#!/bin/bash
cd /home/kevxhk/work/L-gct-210/stage2
echo "== T1cert cross-type (Singular QQ) $(date -u +%H:%M:%S)"
ENGINE=sing EXC="a1*(a1+a2+a3-4)*(a1+a2+a3+1)" timeout 1500 python3 -I r16_T1cert.py R1 0 "lam=0" 2>&1 | grep -E "lcm|excluded|NONUNIT|FAILED|RESULT"
RUL=R1 timeout 2400 r16/fam_batch.sh "lam=0,a1=0" "lam=0,a1=4-a2-a3"
echo "== T1cert cross a1=0 (Singular) $(date -u +%H:%M:%S)"
ENGINE=sing EXC="a2*(a2+a3-4)*(a2+a3+1)" timeout 1500 python3 -I r16_T1cert.py R1 0 "lam=0,a1=0" 2>&1 | grep -E "lcm|excluded|NONUNIT|FAILED|RESULT"
echo "CROSS BATCH DONE $(date -u +%H:%M:%S)"

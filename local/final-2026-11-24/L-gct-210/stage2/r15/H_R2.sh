#!/bin/bash
# R2 survivor hyperplane H = {a1+2a2+2a3 = 6}: kernel-reduced FO2-joint charts Gr(3,7) (35), 3 parameters (NOTES-stage2 R15-4/5).
cd /home/kevxhk/work/L-gct-210/stage2
S="a1=6-2*a2-2*a3"; C=r14/cache_F2col_4ac3c2e05b6d.pkl
echo "== modp $(date -u +%H:%M:%S)"; MSV=${MSV:-2000000} timeout 5400 python3 -I r16_F2col_K.py $C 2147483629 "$S" 2>&1 | grep -E "Rabinowitsch|NONUNIT|FAILED|rational|RESULT"
echo "== char0 msolve $(date -u +%H:%M:%S)"; MSV=${MSV:-2000000} timeout 7200 python3 -I r16_F2col_K.py $C 0 "$S" 2>&1 | grep -E "NONUNIT|FAILED|RESULT"
echo "== char0 Singular std over QQ $(date -u +%H:%M:%S)"; ENGINE=sing MSV=${MSV:-2000000} timeout 7200 python3 -I r16_F2col_K.py $C 0 "$S" 2>&1 | grep -E "NONUNIT|FAILED|RESULT"
echo "ALL DONE $(date -u +%H:%M:%S)"

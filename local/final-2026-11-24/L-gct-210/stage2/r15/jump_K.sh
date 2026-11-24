#!/bin/bash
# R1 jump locus (lam=0, a3=-1-a1-a2), kernel lemma of NOTES-stage2 R15-6: survivors on a1 = -8; reduced charts Gr(3,9) (84), 1 parameter a2.
cd /home/kevxhk/work/L-gct-210/stage2
C=r14/cache_F2col_abe61e9e5caa.pkl
echo "== Deg (exact degeneracy locus) $(date -u +%H:%M:%S)"; timeout 3600 python3 -I r16_Kjump_deg.py $C 2>&1 | tail -30
echo "== modp a1=-8 $(date -u +%H:%M:%S)"; MSV=${MSV:-2000000} timeout 7200 python3 -I r16_F2col_K2.py $C 2147483629 "a1=-8" 2>&1 | grep -E "NONUNIT|FAILED|rational|RESULT"
echo "== char0 Singular std over QQ a1=-8 $(date -u +%H:%M:%S)"; ENGINE=sing MSV=${MSV:-2000000} timeout 7200 python3 -I r16_F2col_K2.py $C 0 "a1=-8" 2>&1 | grep -E "NONUNIT|FAILED|RESULT"
echo "ALL DONE $(date -u +%H:%M:%S)"

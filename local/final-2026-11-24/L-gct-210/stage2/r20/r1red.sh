#!/bin/bash
# R1 lines: K2 (K = Ck, q0(k,k) = 0) and Kt3 (dim K = 2) reductions in Singular; then the exact R1 RD certificate (char 0).
cd /home/kevxhk/work/L-gct-210/stage2
for C in 17dc07201935 9881b981b0a9 05809a23902d ad0a91b6ba10; do echo "== K2 $C $(date -u +%H:%M:%S)"; ENGINE=sing STO=120 MSV=1000000 timeout 3000 python3 -I r20_F2col_K2b.py r16/cache_$C.pkl 0 "" 2>&1 | grep -E "subfamily|q0\(k,k\)|eliminating|Rabinowitsch|NONUNIT|FAILED|RESULT|Error|assert|timed out" | cut -c1-200; done
for C in 97f34f926218 29c73249bd89; do echo "== Kt3 $C $(date -u +%H:%M:%S)"; STO=300 MSV=1000000 timeout 2400 python3 -I r18_Kt3.py r16/cache_$C.pkl 2>&1 | grep -E "discriminant|chart|RESULT|Error|assert" | cut -c1-200; done
echo "== R1 RD certificate char 0 $(date -u +%H:%M:%S)"; SING_ULIM=1500000 SING_TMO=2400 timeout 2600 python3 -I r20_RDcert.py r14/cache_F2col_05c7df28474c.pkl "lam*a1*(a1+a2+a3-4)" "a1-1;a2-1;a3-1" 0 2>&1 | cut -c1-300
echo "ALL DONE $(date -u +%H:%M:%S)"

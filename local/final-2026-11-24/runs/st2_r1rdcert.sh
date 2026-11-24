#!/bin/bash
# ST2-R1RDCERT (stage2 07:35): exact char-0 certificate that the R1 common rank-drop locus is {a=(1,1,1)} (generic R1 + a1=0 family)
cd /home/kevxhk/work/L-gct-210/stage2 || exit 1
SING_ULIM=6000000 SING_TMO=7200 python3 -I r20_RDcert.py r14/cache_F2col_05c7df28474c.pkl "lam*a1*(a1+a2+a3-4)" "a1-1;a2-1;a3-1" 0 > r21/R1RDcert_big.log 2>&1 && \
SING_ULIM=6000000 SING_TMO=7200 python3 -I r20_RDcert.py r16/cache_f454e873c453.pkl "lam*a2*(a2+a3-4)*(a2+a3+1)" "a2-1;a3-1" 0 >> r21/R1RDcert_big.log 2>&1
echo "ST2-R1RDCERT exit $? $(date -u +%T)"; tail -4 r21/R1RDcert_big.log

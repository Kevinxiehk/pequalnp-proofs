#!/bin/bash
# R1 remaining certificates: RD (char 0) for generic R1 and the a1 = 0 family; T1cert for a1 = 0; the a1 = a2 = 0 family.
cd /home/kevxhk/work/L-gct-210/stage2
echo "== RD cert generic R1 char 0 $(date -u +%H:%M:%S)"; SING_ULIM=1500000 SING_TMO=2400 timeout 2600 python3 -I r20_RDcert.py r14/cache_F2col_05c7df28474c.pkl "lam*a1*(a1+a2+a3-4)" "a1-1;a2-1;a3-1" 0 2>&1 | cut -c1-200
echo "== RD cert R1 a1=0 char 0 $(date -u +%H:%M:%S)"; SING_ULIM=1500000 SING_TMO=2400 timeout 2600 python3 -I r20_RDcert.py r16/cache_f454e873c453.pkl "lam*a2*(a2+a3-4)*(a2+a3+1)" "a2-1;a3-1" 0 2>&1 | cut -c1-200
echo "== T1cert R1 a1=0 Singular $(date -u +%H:%M:%S)"; ENGINE=sing EXC="lam*a2*(a2+a3-4)*(a2+a3+1)" timeout 1500 python3 -I r16_T1cert.py R1 0 "a1=0" 2>&1 | grep -E "lcm|excluded|NONUNIT|FAILED|RESULT"
echo "== R1 a1=a2=0 family $(date -u +%H:%M:%S)"
O=$(timeout 1500 python3 -I r16_F2col_setup.py R1 2147483629 "a1=0,a2=0" 2>&1); echo "$O" | grep -E "rank-jump|dim T_1|complement valid|denominators"
C=$(echo "$O" | grep -oE "/home[^ ]*cache_[0-9a-f]+\.pkl" | head -1); echo "cache $C"
timeout 900 python3 -I r18_linerank.py $C 2>&1 | grep -E "fix|=>"
timeout 900 python3 -I r20_kbound_rec.py $C 4 5 2>&1 | grep -E "CONTRADICTION|RESULT"
echo "ALL DONE $(date -u +%H:%M:%S)"

#!/bin/bash
# round-15 pool chain c: pieces P2/P1 (gen_t22pc) through the open-chart radical cover (rc0..rc3 + gam0, rc5; rc4 not here).  Waits for chain15b.
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p rad
while kill -0 538606 2>/dev/null; do sleep 5; done
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
for it in P2/z1:z1:z1/- P2/ab:z1:0/- P1a/z1:z1:z1/- P1b/z1:z1:z1/-; do
  tag=$(echo $it | tr '/:' '__')
  run 1500 env RCS=0,1,2,3 GAM0=1 python3 -I radcell3g.py 2147483629 A 0 pc $it rad/gpc_A0_$tag 300
  run 900 env RCS=5 python3 -I radcell3.py 2147483629 A 0 pc $it rad/opc_A0_$tag 300
done
echo "$(date -u +%T) chain15c done" >> chain13.log

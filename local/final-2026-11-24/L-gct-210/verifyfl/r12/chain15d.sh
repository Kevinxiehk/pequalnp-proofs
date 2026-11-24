#!/bin/bash
# round-15 pool chain d: rc4 of the P2/P1 sample items (short stages).  Waits for chain15c.
cd /home/kevxhk/work/L-gct-210/verifyfl/r12
while kill -0 553658 2>/dev/null; do sleep 5; done
run() { cap=$1; shift; echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout $cap "$@") >> chain13.out 2>&1; }
for it in P2/z1:z1:z1/- P2/ab:z1:0/- P1a/z1:z1:z1/- P1b/z1:z1:z1/-; do
  tag=$(echo $it | tr '/:' '__'); run 900 env RCS=4 python3 -I radcell3.py 2147483629 A 0 pc $it rad/o4pc_A0_$tag 300
done
echo "$(date -u +%T) chain15d done" >> chain13.log

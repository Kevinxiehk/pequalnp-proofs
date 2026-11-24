#!/bin/bash
# round-14 pool chain, one job at a time (<= 2.5 GB, single thread)
cd /home/kevxhk/work/L-gct-210/verifyfl/r12; mkdir -p rad
run() { echo "$(date -u +%T) start $*" >> chain13.log; (ulimit -v 2500000; MSOLVE_THREADS=1 timeout 2400 "$@") >> chain13.out 2>&1; }
# (a) the failing radical cells of t0c-01 with fine stages + extra filtering
run env RCS=0,2 python3 -I radcell3.py 2147483629 A 0 t0c 01 rad/f_A0_t0c_01 600 t0/t0c_A_c0_01_None_N.ms.gb
# (b) P2 / P1 pieces through the radical cells: cheap charts first
for it in P2/z1:z1:z1/- P2/ab:z1:0/- P1a/z1:z1:z1/- P1b/z1:z1:z1/- P2/ab:0:0/- P1a/ab:0:0/-; do
  tag=$(echo $it | tr '/:' '__'); run python3 -I radcell3.py 2147483629 A 0 pc $it rad/pc_A0_$tag 600
done
echo "$(date -u +%T) chain14 done" >> chain13.log
